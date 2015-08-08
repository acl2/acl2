(in-package "BAG")

(include-book "basic")
(include-book "ordinals/e0-ordinal" :dir :system)
;eventually, move the any-subbagp meta rule below to a different book?

#|
(defun implies-if (a term)
  (declare (type t a term))
  (if a t term))
|#

;trying disabled...
(defund meta-subbagp (list1 list2)
  (declare (type t list1 list2))
  (subbagp list1 list2))

;trying disabled...
(defund meta-memberp (x list)
  (declare (type t x list))
  (memberp x list))

;;===========================================================================
;; :meta rule to establish membership syntactically When TERM is a nest of
;; conses and appends which contains a cons of X, we can tell just by looking
;; at TERM that X is a memberp of it.
;============================================================================

;How much other behavior should this rule rely on?  Should we rely on the fact
;that nests of appends get basically right associated (that is, that the first
;argument to an append is never another append)?  What about the fact that, in
;a perm context, the conses are brought before the appends.

#|
Without the :meta rule, this fails:
(thm (memberp x (cons y (cons yy (append w (cons x (append ww z))))))
     :hints (("Goal" :in-theory (disable memberp))))
|#

;The evaluator for the :meta rule syntactic-membership-meta-rule.
(defevaluator evaluator-for-memberp-cons-and-append evaluator-for-memberp-cons-and-append-list
  ((memberp x l)
   (binary-append x y)
   (cons x y)
;   (quote x)
   (list-fix x)
   ))

;TERM is a nest of conses and appends
;This function looks through that nest for a cons of X.
;If it finds such a cons, it returns T.  Else, it returns nil.
;It refuses to look inside any function which is not a cons or an append.
;This no longer depends on nests of appends and conses being normalized?
;BOZO don't need to repeat the checking of X on recursive calls when X doesn't change... pass in a flag?

(defignore syntax-memberp a (x term)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp term))))
  (if (consp term)
      (if (equal (car term) 'quote) ;; '(quote arg1)    ;could make this case more efficient??
          (if (and (consp x)
                   (equal (car x) 'quote)
                   (null (cddr x))
                   (null (cddr term))
                   )
              (memberp (cadr x) (cadr term)) ;if x and term are quoted constants, just run memberp on the constants!
            nil ;if TERM is a quoted constant but X isn't, we don't really know anything about membership
            )
        (if (and (equal (car term) 'cons) ;; '(cons arg1 arg2)
                 (null (cdddr term)) ;consider inlining this?
                 )
            (if (equal (cadr term) x)
                t ;If the thing consed on is x, we're done.
              (syntax-memberp x (caddr term))) ;Else, skip the cons.
          (if (and (equal (car term) 'binary-append)   ;; '(binary-append arg1 arg2)
                   (null (cdddr term)) ;consider inlining this?
                   )
              (or (syntax-memberp x (cadr term))
                  (syntax-memberp x (caddr term)))
;            (if (and (equal (car term) 'list-fix)   ;; '(list-fix arg1)
  ;                   (null (cddr term)) ;consider inlining this?
   ;                  )
;                (syntax-memberp x (cadr term))
              nil ;We've found something that is neither a cons nor an append nor a quote.
    ;          )
            )))
    nil))

(defirrelevant syntax-memberp 1 a (x term)
  )

;We expect TERM to be of the form (memberp x y).  If not, we do nothing.
;If so, we call syntax-memberp.  If that function returns t, that means we can show
;syntactically that X is a memberp of Y.  If that function returns nil, we don't know whether
;X is a memberp of Y; in this case, we must return something equivalent to TERM,
;so we return TERM itself !
(defun syntax-memberp-wrapper (term)
  (declare (type t term)
           (xargs :guard (pseudo-termp term)))
  (if (not (and (equal 3 (len term))
                (equal (car term) 'memberp)))
      term
    (if (syntax-memberp-fn nil (cadr term) (caddr term))
        ''t
      term
      )))

(defthm syntax-memberp-implies-memberp
  (implies (syntax-memberp x y)
	   (memberp (evaluator-for-memberp-cons-and-append x a)
		    (evaluator-for-memberp-cons-and-append y a)))
  :hints (("Goal" :in-theory (enable memberp)))
  :rule-classes (:rewrite :forward-chaining))


(defthm syntactic-membership-meta-rule
  (equal (evaluator-for-memberp-cons-and-append term a)
	 (evaluator-for-memberp-cons-and-append (syntax-memberp-wrapper term) a))
  :hints (("Goal" :in-theory (enable  syntax-memberp-irrelevant)
	   :do-not '(generalize eliminate-destructors)))
  :rule-classes ((:meta :trigger-fns (memberp))))

(encapsulate
 ()

;bozo how does the t-p rule get used if we disable it??
 (local (defthm memberp-meta-rule-test
          (memberp x (cons y (cons yy (append w (cons x (append ww z))))))
          :hints (("Goal" :in-theory (union-theories '(syntactic-membership-meta-rule)
                                                     (theory 'minimal-theory))))))

 (local (defthm memberp-meta-rule-test-2
          (memberp '3 (append x '(1 2 3)))
          :hints (("Goal" :in-theory (union-theories '(syntactic-membership-meta-rule)
                                                     (theory 'minimal-theory))))))

 (local (defthm memberp-meta-rule-test-3
          (memberp x (append (append y (cons x w)) z))
          :hints (("Goal" :in-theory (union-theories '(syntactic-membership-meta-rule)
                                                     (theory 'minimal-theory)))))))






(defund subbagp-pair (x1 x2 list1 list2)
  (declare (type t x1 x2 list1 list2))
  (or (and (subbagp x1 list1)
	   (subbagp x2 list2))
      (and (subbagp x1 list2)
	   (subbagp x2 list1))))



;like remove-1, but this returns (mv hit result), where hit indicates whether anything was actually removed.
(defun run-remove-1 (a x)
  (declare (type t a x))
  (if (consp x)
      (if (equal a (car x))
          (mv t (cdr x)) ;we removed (car x)
          (met ((hit result) (run-remove-1 a (cdr x)))
               (mv hit (cons (car x) result))))
      (mv nil x)))

(defthm v1-run-remove-1
  (equal (val 1 (run-remove-1 a x))
         (remove-1 a x)))

(defthm v0-run-remove-1
  (equal (val 0 (run-remove-1 a x))
         (memberp a x)))

;TERM is a term built from conses and appends (we refuse to look
;inside anything other than a cons or append).  Given an element,
;ELEM, and a term, TERM, syntactically remove one copy of ELEM from
;TERM, if possible.  Returns (mv hit new-term).  If we found an
;occurrence of ELEM to remove, hit is t and new-list is a new TERM
;whose contents are a permutation of the contents of the removal of
;one copy of ELEM from the contents of TERM.  The only way to remove
;ELEM from TERM is to find ELEM consed on somewhere in TERM.  if hit
;is nil, do we ever use the return value?


(defignored syntax-remove-1 a (elem term)
  (declare (type t elem term)
           (xargs :guard (and (pseudo-termp elem)
                              (pseudo-termp term))))
  (if (consp term)
      (if (and (equal (car term) 'binary-append) ;; '(binary-append arg1 arg2)
               (null (cdddr term))
               )
          (let ((arg1 (cadr term))
                (arg2 (caddr term)))
            (met ((hit newarg1) (syntax-remove-1 elem arg1))
                 (if hit (mv t `(binary-append ,newarg1 ,arg2))
                   (met ((hit newarg2) (syntax-remove-1 elem arg2))
                        (if hit (mv t `(binary-append ,arg1 ,newarg2))
                          (mv nil term))))))
        (if (and (equal (car term) 'cons) ;; '(cons arg1 arg2)
                 (null  (cdddr term)))
            (let ((arg1 (cadr term))
                  (arg2 (caddr term)))
              (if (equal elem arg1) ;if arg1 is equal to elem
                  (mv t arg2)       ;then just return arg2 (we just drop arg1, since it matches elem)
                (met ((hit newarg2) (syntax-remove-1 elem arg2)) ;otherwise, try to remove elem from arg2
                     (if hit ;if we succeeded in removing it
                         (mv t `(cons ,arg1 ,newarg2))  ;the return the result of removing it, with arg1 tacked onto the front
                       (mv nil term) ;otherwise, we failed to remove elem from term
                       ))))
          (if (and (equal (car term) 'quote) ;; '(quote arg1)
                   (consp elem)
                   (equal (car elem) 'quote)
                   (null (cddr elem))
                   (null (cddr term))
                   )
              (met ((hit result) (run-remove-1 (cadr elem) (cadr term)))
                   (if hit
                       (mv t `(quote ,result))
                     (mv nil term)))
;;             (if (and (equal (car term) 'list-fix) ;; '(list-fix arg1)
;;                      (consp (cdr term))
;;                      (null  (cddr term)))
;;                 (let ((arg1 (cadr term)))
;;                   (met ((hit newarg1) (syntax-remove-1 elem arg1))
;;                        (if hit ;if we succeeded in removing it
;;                            (mv t `(list-fix ,newarg1))  ;should we not re-add the list-fix call around the result?
;;                          (mv nil term) ;otherwise, we failed to remove elem from term
;;                          )))
              (mv nil term)
              ;)
              )))
    (mv nil term)))

(defthm not-v0-no-change-syntax-remove-1
  (implies (not (v0 (syntax-remove-1 elem term)))
	   (equal (v1 (syntax-remove-1 elem term))
		      term))
  :hints (("Goal" :in-theory (enable syntax-remove-1-fn))))

(defirrelevant syntax-remove-1 2 a (elem term)
  :hints (("goal" :in-theory (enable syntax-remove-1-fn))))

;looks for X being appended onto something in TERM, and if it finds
;such an occurrence, removes it.  does not look inside of X, so X
;shouldn't be a cons or append, for example.  can X be a quoted
;constant bag?  what about nil?  only removes one copy of X.  bozo
;handle quoted stuff? or not?  can x ever be a quoted thing?  bozo
;handle list-fix?

(defignore syntax-remove-bag-1 a (x term)
  (declare (type t x term)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp term))))
  (if (and (consp term)
	   (equal (car term) 'binary-append) ;; '(binary-append arg1 arg2)
	   (null  (cdddr term)))
      (let ((arg1 (cadr term))
	    (arg2 (caddr term)))
        (met ((hit newarg1) (syntax-remove-bag-1 x arg1))
             (if hit
                 (mv t `(binary-append ,newarg1 ,arg2))
               (met ((hit2 newarg2) (syntax-remove-bag-1 x arg2))
                    (if hit2
                        (mv t `(binary-append ,arg1 ,newarg2))
                      (mv nil term))))))
    (if (and (consp term)
             (equal (car term) 'cons) ;; '(cons arg1 arg2)
             (null  (cdddr term)))
        (let ((arg1 (cadr term))
              (arg2 (caddr term)))
          (met ((hit newarg2) (syntax-remove-bag-1 x arg2))
               (if hit
                   (mv t `(cons ,arg1 ,newarg2))
                 (mv nil term))))
;;       (if  (and (equal (car term) 'quote) ;; '(quote arg1)  bozo think about this
;;                 (consp x)
;;                 (equal (car x) 'quote)
;;                 (consp (cdr x))
;;                 (null (cddr x))
;;                 (consp (cdr term))
;;                 (null (cddr term))
;;                 )
;      (remove-bag (cadr x) (cadr term))
      (if (equal x term)
          (mv t `(final-cdr ,x))        ;  (mv t `(quote nil))
        (mv nil term)))))

(defthm booleanp-of-mv-nth-0-of-syntax-remove-bag-1
  (booleanp (val 0 (syntax-remove-bag-1 term1 term2)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable syntax-remove-bag-1-fn))))

(defthm not-v0-no-change-syntax-remove-bag-1
  (implies (not (v0 (syntax-remove-bag-1 x y)))
	   (equal (v1 (syntax-remove-bag-1 x y))
		      y))
  :hints (("goal" :in-theory (enable syntax-remove-bag-1-fn))))

(defirrelevant syntax-remove-bag-1 2 a (x term)
  :hints (("goal" :in-theory (enable syntax-remove-bag-1-fn))))

(defthm pseudo-termp-of-v1-of-syntax-remove-bag-1
  (implies (and (pseudo-termp term1)
                (pseudo-termp term2))
           (pseudo-termp (val 1 (syntax-remove-bag-1 term1 term2)))))

(defthm pseudo-termp-of-v1-of-syntax-remove-1
  (implies (and (pseudo-termp term1)
                (pseudo-termp term2))
           (pseudo-termp (val 1 (syntax-remove-1 term1 term2))))
  :hints (("Goal" :in-theory (enable syntax-remove-1-fn))))


;takes two terms and syntactically cancels common stuff from them.
;return value is of the form: (mv hit newterm1 newterm2), where hit
;indicates whether anything changed, and term1 and term2 are the new
;versions (with common stuff cancelled) of term1 and term2,
;respectively.  does hit indicate that *anything* changed?  what if
;the only thing changes is that something gets list fixed?  what
;should (syntax-remove-bag ''3 '(cons a b)) return?  (mv t ''nil
;'(cons a b))?

(defignored syntax-remove-bag a (term1 term2)
  (declare (type t term1 term2)
           (xargs :verify-guards nil
		  :guard (and (pseudo-termp term1)
                              (pseudo-termp term2))))
  (if (consp term1)
      (if (and (equal (car term1) 'binary-append) ;; '(binary-append arg1 arg2)
               (null (cdddr term1))
               )
          (let ((arg1 (cadr term1))
                (arg2 (caddr term1)))
            (met ((hit newarg1 newterm2) (syntax-remove-bag arg1 term2))
                 (met ((hit2 newarg2 newerterm2) (syntax-remove-bag arg2 newterm2))
                      (if (or hit hit2)
                          (if (and (equal newarg2 ''nil)
					;don't bother making an append term of two nils
					;(BOZO eventually, avoid making the append term if either arg is nil)
                                   (equal newarg1 ''nil))
                              (mv t ''nil newerterm2)
                            ;(mv t `(binary-append ,newarg1 ,newarg2) newerterm2)
                            (mv t `(binary-append ,newarg1 ,newarg2) newerterm2))
                        (mv nil term1 term2) ;nothing changed!
                        ))))
        (if (and (equal (car term1) 'cons) ;; '(cons arg1 arg2)
                 (null (cdddr term1))
                 )
            (let ((arg1 (cadr term1))
                  (arg2 (caddr term1)))
              (met ((hit newterm2) (syntax-remove-1 arg1 term2))
                   (met ((hit2 newarg2 newerterm2) (syntax-remove-bag arg2 newterm2))
                        (if hit ;arg1 was removed from term2 (and perhaps stuff from arg2 was also removed from term2)
                            (mv t newarg2 newerterm2)
                          (if hit2 ;arg1 wasn't removed from term2, but stuff from arg2 was.
                              (mv t `(cons ,arg1 ,newarg2) newerterm2)
                            (mv nil term1 term2) ;nothing changed!
                            )))))
          (if (and (equal (car term1) 'quote) ;; '(quote arg1)
                   (null (cddr term1))
                   )
              (let ((arg1 (cadr term1)))
                (if (consp arg1)
                    (let ((arg1car `(quote ,(car arg1)))
                          (arg1cdr `(quote ,(cdr arg1))))
                      (met ((hit newterm2) (syntax-remove-1 arg1car term2))
                           (met ((hit2 newarg1cdr newerterm2) (syntax-remove-bag arg1cdr newterm2))
                                (if hit ;arg1car was removed from term2 (and perhaps stuff from arg1cdr was also removed from term2)
                                    (mv t newarg1cdr newerterm2)
                                  (if hit2 ;arg1car wasn't removed from term2, but stuff from arg1cdr was.
                                      (mv t `(cons ,arg1car ,newarg1cdr) newerterm2)
                                    (mv nil term1 term2) ;nothing changed!
                                    )))))

                  ;term1 is a quoted constant which is not a consp..  thus, it reprsents the empty bag
                  (if (equal arg1 'nil)
                      (mv nil term1 term2)
                    (mv t ''nil term2))
                  ))

;;           (if (and (equal (car term1) 'list-fix) ;; '(list-fix arg1)
;;                    (null (cddr term1))
;;                    )
;;               (let ((arg1 (cadr term1)))
;;                 (met ((hit newarg1 newterm2) (syntax-remove-bag arg1 term2)) ;we drop the list-fix; is that the right thing to do?
;;                      (declare (ignore hit))
;;                      (mv t newarg1 newterm2)))


;term1 isn't a call to binary-append or cons:
            (met ((hit newterm2) (syntax-remove-bag-1 term1 term2))
                 (if hit
                     (mv t '(quote nil) newterm2)
                   (mv nil term1 term2))))
;    )
          ))

;term1 is a non-consp:
    (met ((hit newterm2) (syntax-remove-bag-1 term1 term2))
         (if hit
             (mv t '(quote nil) newterm2)
           (mv nil term1 term2))))
  )


(defirrelevant syntax-remove-bag 3 a (term1 term2)
  :hints (("goal" :in-theory (enable SYNTAX-REMOVE-1-FN
				     syntax-remove-bag-fn
				     syntax-remove-1-irrelevant
				     syntax-remove-bag-1-irrelevant))))

(defthm unchanged-syntax-remove-bag
  (implies
   (not (v0 (syntax-remove-bag term1 term2)))
   (and
    (equal (v1 (syntax-remove-bag term1 term2))
	   term1)
    (equal (v2 (syntax-remove-bag term1 term2))
	   term2)))
  :hints (("goal" :in-theory (enable syntax-remove-bag-fn))))

;(syntax-remove-bag '(cons 2 '(3 4)) '(cons 2 (cons 3 (cons 4 c))))
;(syntax-subbagp '(cons 2 '(3 4)) '(cons 2 (cons 3 (cons 4 c))))

;I think both parts of this had to be proved together
(defthm pseudo-termp-of-syntax-remove-bag
  (implies (and (pseudo-termp term1)
                (pseudo-termp term2))
           (and (pseudo-termp (val 1 (syntax-remove-bag term1 term2)))
                (pseudo-termp (val 2 (syntax-remove-bag term1 term2)))))
  :hints (("Goal" :induct t
           :in-theory (enable syntax-remove-bag-fn))))

(verify-guards
 syntax-remove-bag-fn
 )

#|
old version:
;Returns non-nil iff we can tell just by looking at list1 and list2 that list1 is a subbagp of list2.
;perhaps make this a separate :meta rule? <-- huh?
;We syntactically try to remove everything in list2 from list1.  If doing so removes everything from list1, then
;list1 must have been a subbagp of list2.
;This seems inefficient, since it can't fail before syntax-remove-bag has completely finished.

(defun syntax-subbagp (list1 list2)
  (declare (type t list1 list2))
  (met ((hit newlist2 newlist1) (syntax-remove-bag list2 list1))
       (declare (ignore newlist2))
       (and hit ;syntax-remove-bag did something
	    (equal newlist1 '(quote nil)) ;syntax-remove-bag removed everything from newlist1
            )))
|#

;tests whether term1 is a syntactic subbag of term2 returns (mv flg
;leftover) where flg indicates whether term1 is a sytactic subbag of
;term2 and leftover represents the remainder of term2 after
;syntactically removing term1.  leftover is only meaningful when flg
;is t.  handle quoted constants?

(defignored syntax-subbagp-helper a (term1 term2)
  (declare (type t term1 term2)
           (xargs :verify-guards nil
		  :guard (and (pseudo-termp term1)
                              (pseudo-termp term2))))
  (if (consp term1)
      (if (and (equal (car term1) 'binary-append) ;; '(binary-append arg1 arg2)
               (null (cdddr term1))
               )
          (let ((arg1 (cadr term1))
                (arg2 (caddr term1)))
            (met ((flg newterm2) (syntax-subbagp-helper arg1 term2))
                 (if flg
                     (syntax-subbagp-helper arg2 newterm2)
                   (mv nil term2))))
        (if (and (equal (car term1) 'cons) ;; '(cons arg1 arg2)
                 (null (cdddr term1))
                 )
            (let ((arg1 (cadr term1))
                  (arg2 (caddr term1)))
              (met ((hit newterm2) (syntax-remove-1 arg1 term2))
                   (if hit
                       (syntax-subbagp-helper arg2 newterm2)
                     (mv nil term2))))
;term1 isn't a call to binary-append or cons:
;check whether it is a quoted constant which isn't a cons, like nil or 3 (either of which is a subbag of anything)
          (if (and (equal (car term1) 'quote) ;; '(quote arg1)
                   (null (cddr term1))
;                   (not (consp (cadr term1)))
                   )

;BOZO test (here and elsewhere) whether quoted constants are bagps?
              (let ((arg1 (cadr term1)))
                (if (consp arg1)
                    (let ((arg1car `(quote ,(car arg1)))
                          (arg1cdr `(quote ,(cdr arg1))))
                      (met ((hit newterm2) (syntax-remove-1 arg1car term2))
                           (if hit
                               (syntax-subbagp-helper arg1cdr newterm2)
                             (mv nil term2) ;since the second value returned here is irrelevant, consider just returning nil?
                             )))
;term1 is a quoted constant which is not a consp..  thus, it reprsents the empty bag, which is a subbagp of anything
                  (mv t term2) ;is this right? ;should we normalize the quoted constant?
                  ))
            (syntax-remove-bag-1 term1 term2))
          ))
    (syntax-remove-bag-1 term1 term2)))

(defthm pseudo-termp-syntax-subbagp-helper
  (implies
   (and
    (pseudo-termp term1)
    (pseudo-termp term2))
   (pseudo-termp (v1 (syntax-subbagp-helper term1 term2))))
  :hints (("goal" :in-theory (enable syntax-subbagp-helper-fn))))

(verify-guards
 syntax-subbagp-helper-fn
 )

(defirrelevant syntax-subbagp-helper 2 a (term1 term2)
  :hints (("goal" :in-theory (enable syntax-subbagp-helper-fn
				     syntax-remove-bag-1-irrelevant
				     syntax-remove-1-irrelevant))))

(defthm booleanp-of-mv-nth-0-of-syntax-subbagp-helper
  (booleanp (val 0 (syntax-subbagp-helper x2 y2)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable syntax-subbagp-helper-fn))))

(defignored syntax-subbagp a (x y)
  (declare (type t x y)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y))))
  (met ((hit result) (syntax-subbagp-helper x y))
       (declare (ignore result))
       hit))

(defirrelevant syntax-subbagp 1 a (x y)
  :hints (("goal" :in-theory (enable syntax-subbagp-fn
				     syntax-subbagp-helper-irrelevant))))

(defthm booleanp-of-syntax-subbagp
  (booleanp (syntax-subbagp x2 y2))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable syntax-subbagp-fn))))


;Checks whether we know syntactically that either x1 is a subbag of y1
;and x2 is a subbag of y2 or x1 is a subbag of y2 and x2 is a subbag
;of y1 We we call this fucntion, we know that y1 and y2 are disjoint,
;so if (subbagp x1 y1) is true, we don't bother to check whether
;(subbagp x1 y2), because we know it's false.

(defignored syntax-subbagp-pair a (x1 x2 y1 y2)
  (declare (type t x1 x2 y1 y2)
           (xargs :guard (and (pseudo-termp x1)
                              (pseudo-termp y1)
                              (pseudo-termp x2)
                              (pseudo-termp y2))))
  (if (syntax-subbagp x1 y1)
      (syntax-subbagp x2 y2)
    (if (syntax-subbagp x2 y1)
        (syntax-subbagp x1 y2)
      nil)))

(defirrelevant syntax-subbagp-pair 1 a (x1 x2 y1 y2)
  :hints (("goal" :in-theory (enable syntax-subbagp-pair-fn
				     syntax-subbagp-irrelevant))))

;try to determine syntactically whether list contains enough to
;contain both y and x (that is, we can take x out of list and list
;still contains y).  might it be cheaper to create an append x and y
;and then call syntax-remove-bag once on the append?  that avoids
;rebuilding two new version of list...



(defignored syntax-unique-subbagps a (x y list)
  (declare (type t x y list)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y)
                              (pseudo-termp list))))
  (met ((hitx list1 leftover) (syntax-remove-bag x list))
       (if (and hitx (equal list1 '(quote nil))) ;x is a subbagp
	   (met ((hity list1 list2) (syntax-remove-bag y leftover))
		(declare (ignore list2))
		(if (and hity (equal list1 '(quote nil)))
		    t ; '(quote t) ;why quote t?
		  nil))
	 nil)))

(defirrelevant syntax-unique-subbagps 1 a (x y list)
  :hints (("goal" :in-theory (enable syntax-unique-subbagps-fn
				     syntax-remove-bag-irrelevant
				     ))))


;add guard?
(defund meta-remove-bag (x y)
  (remove-bag x y))

#|
;drop?
(defund meta-remove-1 (x list)
  (remove-1 x list))
|#

;remove this?
;add guard?
(defun any-subbagp (term list)
  (declare (type t term list))
  (if (consp list)
      (or (subbagp term (car list))
	  (any-subbagp term (cdr list)))
    nil))





;add guard?
(defund hide-disjoint (x y)
  (disjoint x y))

(defthm hide-disjoint-forward
  (implies (disjoint x y)
	   (hide-disjoint x y))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable hide-disjoint))))


;add guard?
(defund hide-unique (list)
  (unique list))

(defthm hide-unique-forward
  (implies (unique x)
	   (hide-unique x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable hide-unique))))


;add guard?
(defund hide-subbagp (x y)
  (subbagp x y))

(defthm hide-subbagp-forward
  (implies (subbagp x y)
	   (hide-subbagp x y))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable hide-subbagp))))

(defthm hide-subbagp-z-z
  (hide-subbagp z z)
  :hints (("Goal" :in-theory (enable hide-subbagp))))

;add guard?
(defund hide-memberp (x y)
  (memberp x y))

(defthm hide-memberp-forward
  (implies (memberp x y)
	   (hide-memberp x y))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable hide-memberp))))




(defevaluator syntax-ev syntax-ev-list
  (
   (hide x)
   (hide-unique list)
   (hide-subbagp x y) ;added by eric
   (hide-disjoint x y) ;added by eric
   (hide-memberp a x) ;added by eric
   (perm x y)
   (unique list)
;   (implies-if a term)
   (if a b c)
   (consp x)
   (true-listp x)
   (binary-append x y)
   (cons a b)
   (meta-subbagp list1 list2)
   (remove-bag x list)
   (meta-remove-bag x list)
   (remove-1 x list)
;   (meta-remove-1 x list)
   (unique-subbagps x y list)
   (subbagp-pair x1 x2 list1 list2)
   (meta-memberp x list)
   (any-subbagp x list) ;remove this?
   (final-cdr x)
   (list-fix x)
   (subbagp x y) ;added by eric
   (memberp a x) ;added by eric
   (disjoint x y) ;added by eric
;   (synp vars form term) ;added by eric
   (equal x y)
))

;-- proof that the simplification is valid --;

;If syntax-remove-1 signals a hit, ELEM must have been found (and removed) in TERM.
(defthm syntax-remove-1-implements-memberp
  (implies (v0 (syntax-remove-1 elem term))
	   (memberp (syntax-ev elem a) (syntax-ev term a)))
  :hints (("Goal" :in-theory (enable syntax-remove-1-fn)))
  :rule-classes (:rewrite :forward-chaining))

(defthm syntax-remove-bag-1-implements-subbagp
  (implies (and (v0 (syntax-remove-bag-1 list1 list2))
		(equal (v1 (syntax-remove-bag-1 list1 list2))
		       '(quote nil)))
	   (subbagp (syntax-ev list2 a) (syntax-ev list1 a)))
  :rule-classes (:rewrite :forward-chaining))

;the new TERM returned by syntax-remove-1 represents a term which is a subbag of the original TERM.
(defthm v1-syntax-remove-1-subbagp
  (subbagp (syntax-ev (v1 (syntax-remove-1 x list1)) a)
           (syntax-ev list1 a))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-1-fn))))

(defthm v1-syntax-remove-bag-1-subbagp
  (subbagp (syntax-ev (v1 (syntax-remove-bag-1 x list1)) a)
           (syntax-ev list1 a)))

#|
(defthm syntax-remove-bag-1-not
  (implies (and (v0 (syntax-remove-bag-1 list1 list2))
		(not (syntax-ev (v1 (syntax-remove-bag-1 list1 list2)) alist)))
	   (subbagp (syntax-ev list2 alist)
                    (syntax-ev list1 alist)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))
|#

(set-well-founded-relation e0-ord-<)

(defthm v0-remove-1-subbagp
  (implies
   (v0 (syntax-remove-bag-1 list1 list2))
   (subbagp (syntax-ev list1 a) (syntax-ev list2 a)))
  :rule-classes (:rewrite :forward-chaining))

;think more about the proof of this?? how should we handle remove-1 and
;append?  If syntax-remove-1 signals a hit, then the new term it returns
;represents a bag which is a permutation of the bag resulting from the removal
;of ELEM from the bag represented by TERM.

(defthm v1-syntax-remove-1-perm-remove-1
  (implies (v0 (syntax-remove-1 elem term))
	   (perm (syntax-ev (v1 (syntax-remove-1 elem term)) a)
		 (remove-1 (syntax-ev elem a) (syntax-ev term a))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (;remove-1
                            syntax-remove-1-fn
                            REMOVE-1-APPEND
                            ;APPEND-OF-REMOVE-1-TWO
                            PERM-CONS-REDUCTION
                            ;APPEND-OF-REMOVE-1-TWO
                            )
                           (APPEND-REMOVE-1-REDUCTION
                            PERM-OF-REMOVE-1-ONE
                            ;PERM-CONSP-REMOVE-1 ;bozo looped! when mv-nth was enabled.
                            ;PERM-OF-REMOVE-1-ONE
                            ;PERM-OF-CONS
                            ;PERM-OF-CONS-MEMBERP-CASE
                            ;PERM-COMMUTATIVE
                            )))))


(defthm v1-syntax-remove-bag-1-perm-remove-bag
  (implies (v0 (syntax-remove-bag-1 list1 list2))
	   (perm (syntax-ev (v1 (syntax-remove-bag-1 list1 list2)) a)
		 (remove-bag (syntax-ev list1 a) (syntax-ev list2 a))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

;theorem we are interested in
(defthm syntax-remove-bag-1-subbagp-append
  (implies (and (v0 (syntax-remove-bag-1 x list2))
                (subbagp (syntax-ev (v1 (syntax-remove-bag-1 x list2)) a)
                         (syntax-ev y a)))
           (subbagp (syntax-ev list2 a)
                    (append (syntax-ev x a)
                            (syntax-ev y a)))))


;make local?
(defthmd not-v1-syntax-remove-1
  (implies (and (v0 (syntax-remove-1 x list2))
                (not (syntax-ev (v1 (syntax-remove-1 x list2)) a)))
           (not (consp (remove-1 (syntax-ev x a) (syntax-ev list2 a)))))
  :hints (("Goal" :in-theory (enable syntax-remove-1-fn)))
  :rule-classes (:rewrite :forward-chaining))


(defthm syntax-remove-bag-adds-no-elements
  (implies (memberp elem (syntax-ev (val 2 (syntax-remove-bag term1 term2)) a))
           (memberp elem (syntax-ev term2 a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag-fn))))





;we don't really use this?  maybe someday...
(defund syntax-count (elem term)
  (declare (type t elem term)
           (xargs :guard (pseudo-termp term))
           )
  (if (consp term)
      (if (and (equal (car term) 'binary-append) ;; '(binary-append arg1 arg2)
;               (consp (cdr term))
 ;              (consp (cddr term))
               (null  (cdddr term)))
          (+ (syntax-count elem (cadr term))
             (syntax-count elem (caddr term)))
        (if (and (equal (car term) 'cons) ;; '(cons arg1 arg2)
;                 (consp (cdr term))
 ;                (consp (cddr term))
                 (null  (cdddr term)))
            (if (equal (cadr term) elem)
                (+ 1 (syntax-count elem (caddr term)))
              (syntax-count elem (caddr term)))
          0))
    0))

;(include-book "arithmetic/top" :dir :system)


(defthm syntax-count-of-non-consp
  (implies (not (consp term1))
           (equal (syntax-count elem term1) 0))
 :hints (("Goal" :in-theory (enable syntax-count))))


(defthm count-in-SYNTAX-REMOVE-1-linear
  (<= (COUNT ELEM (SYNTAX-EV (VAL 1 (SYNTAX-REMOVE-1 x Y)) a))
      (COUNT ELEM (SYNTAX-EV Y a)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable SYNTAX-REMOVE-1-fn))))

(defthm count-in-SYNTAX-REMOVE-bag-1-linear
  (>= (COUNT ELEM (SYNTAX-EV (VAL 1 (SYNTAX-REMOVE-bag-1 x Y)) a))
      (- (COUNT ELEM (SYNTAX-EV Y a))
         (COUNT ELEM (SYNTAX-EV x a))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable SYNTAX-REMOVE-bag-1-fn))))

(defthm booleanp-of-VAL-of-SYNTAX-REMOVE-1
  (booleanp (VAL 0 (SYNTAX-REMOVE-1 ELEM TERM)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable SYNTAX-REMOVE-1-fn))))

(encapsulate
 ()

 (local (defthm syntax-remove-1-did-something-iff-1
          (implies (val 0 (syntax-remove-1 elem term))
                   (syntax-memberp elem term))
          :hints (("Goal" :in-theory (enable syntax-remove-1-fn)
                   :do-not '(generalize eliminate-destructors)))
          ))


 (local (defthm syntax-remove-1-did-something-iff-2
          (implies (syntax-memberp elem term)
                   (val 0 (syntax-remove-1 elem term)))
          :hints (("Goal" :in-theory (enable syntax-remove-1-fn syntax-memberp-fn)
                   :do-not '(generalize eliminate-destructors)))
          ))

 (defthm syntax-remove-1-did-something-iff
   (equal (val 0 (syntax-remove-1 elem term))
          (syntax-memberp elem term))
   :hints (("Goal" :use (syntax-remove-1-did-something-iff-1
                         syntax-remove-1-did-something-iff-2)
            :in-theory (disable syntax-remove-1-did-something-iff-1
                                syntax-remove-1-did-something-iff-2)))))



(defthm count-of-syntax-remove-1
  (equal (count (syntax-ev x a)
                (syntax-ev (val 1 (syntax-remove-1 x y)) a))
         (if (syntax-memberp x y)
             (+ -1 (count (syntax-ev x a)
                          (syntax-ev y a)))
           (count (syntax-ev x a)
                  (syntax-ev y a))))
  :hints (("Goal" :in-theory (enable syntax-remove-1-fn)
           :do-not '(generalize eliminate-destructors))))

(defthm count-of-syntax-remove-1-better
  (equal (count elem (syntax-ev (val 1 (syntax-remove-1 x y)) a))
         (if (equal elem (syntax-ev x a))
             (if (syntax-memberp x y)
                 (+ -1 (count (syntax-ev x a)
                              (syntax-ev y a)))
               (count (syntax-ev x a)
                      (syntax-ev y a)))
           (count elem (syntax-ev y a))))
  :hints (("Goal" :in-theory (enable syntax-remove-1-fn)
           :do-not '(generalize eliminate-destructors))))

(defthm count-in-syntax-remove-bag-linear
  (>= (count elem (syntax-ev (val 2 (syntax-remove-bag x y)) a))
     (- (count elem (syntax-ev y a))
        (count elem (syntax-ev x a))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag-fn))))


#|kill?
(thm
 (IMPLIES
  (< (+ (COUNT ELEM (SYNTAX-EV x1 alist))
        (COUNT ELEM (SYNTAX-EV x2 alist)))
     (COUNT ELEM (SYNTAX-EV Y alist)))
  (MEMBERP
   ELEM
   (SYNTAX-EV
    (VAL
     2
     (SYNTAX-REMOVE-BAG x2
                        (VAL 2 (SYNTAX-REMOVE-BAG x1 Y)))) alist)))
 )
|#

(defthm memberp-of-syntax-remove-bag-one
  (implies (memberp elem (remove-bag (syntax-ev x a) (syntax-ev y a)))
           (memberp elem (syntax-ev (val 2 (syntax-remove-bag x y)) a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag-fn memberp))))

;do we even need this?
;BOZO handle constants!
(defignored syntax-intersection a (term1 term2)
  (declare (type t term1 term2)
           (xargs :guard (and (pseudo-termp term1)
                              (pseudo-termp term2))))
  (if (consp term1)
      (if (and (equal (car term1) 'binary-append) ;; '(binary-append arg1 arg2)
               (null (cdddr term1))
               )
          (let ((arg1 (cadr term1))
                (arg2 (caddr term1)))
            (met ((hit newarg1 newterm2) (syntax-remove-bag arg1 term2))
                 (if hit
;find out what we removed:
                     (met ((hit2 blah diff) (syntax-remove-bag newarg1 arg1))
                          (declare (ignore hit2 blah))
                          (list 'binary-append diff (syntax-intersection arg2 newterm2)))
                   (syntax-intersection arg2 term2))))
        (if (and (equal (car term1) 'cons) ;; '(cons arg1 arg2)
                 (null (cdddr term1))
                 )
            (let ((arg1 (cadr term1))
                  (arg2 (caddr term1)))
              (met ((hit newterm2) (syntax-remove-1 arg1 term2))
                   (if hit
                       (list 'cons arg1 (syntax-intersection arg2 newterm2))
                     (syntax-intersection arg2 term2))))

;;           (if (and (equal (car term1) 'list-fix) ;; '(list-fix arg1)
;;                    (null (cddr term1))
;;                    )
;;               (syntax-intersection (cadr term1) term2)

          (if (and (equal (car term1) 'quote) ;; '(quote arg1)
                   (null (cddr term1))
                   )
              (let ((arg1 (cadr term1)))
                (if (consp arg1)
                    (let ((arg1car `(quote ,(car arg1)))
                          (arg1cdr `(quote ,(cdr arg1))))
                    (met ((hit newterm2) (syntax-remove-1 arg1car term2))
                         (if hit
                             `(cons ,arg1car ,(syntax-intersection arg1cdr newterm2))
                           (syntax-intersection arg1cdr term2))))
                  ''nil
                  ))

;term1 isn't a call to binary-append or cons or list-fix:
            (met ((hit newterm2) (syntax-remove-bag-1 term1 term2))
                 (declare (ignore newterm2))
                 (if hit
                     term1
                   ''nil)))
            ;)
          ))

;term1 is a non-consp:
    (met ((hit newterm2) (syntax-remove-bag-1 term1 term2))
         (declare (ignore newterm2))
         (if hit
             term1
           ''nil)))
  )

(defirrelevant syntax-intersection 1 a (term1 term2)
  :hints (("goal" :in-theory (enable syntax-intersection-fn
				     syntax-memberp-irrelevant
				     syntax-remove-1-irrelevant
				     syntax-remove-bag-1-irrelevant
				     syntax-remove-bag-irrelevant
				     ))))


(defthm syntax-intersection-is-nil-when-syntax-remove-bag-does-nothing
  (implies (not (val 0 (syntax-remove-bag term1 term2)))
           (equal (syntax-intersection term1 term2)
                  ''nil))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct t
           :expand ((SYNTAX-INTERSECTION TERM1 TERM2))
           :in-theory (enable syntax-remove-bag-fn
                              syntax-remove-bag-1-fn
                              syntax-intersection-fn
                              ))))


(defthm kingoftown
  (implies (not (syntax-memberp elem term))
           (not (syntax-memberp elem (val 1 (syntax-remove-bag-1 other-term term))))))

(defthm kingoftown2
  (IMPLIES
   (NOT (SYNTAX-MEMBERP ELEM TERM))
   (NOT
    (SYNTAX-MEMBERP ELEM
                       (VAL 1
                                  (SYNTAX-REMOVE-1 OTHER-TERM TERM)))))
  :hints (("Goal" :in-theory (enable SYNTAX-REMOVE-1-fn))))

(defthm smith-blah
  (IMPLIES (NOT (SYNTAX-MEMBERP elem term))
           (NOT (SYNTAX-MEMBERP elem (VAL 2 (SYNTAX-REMOVE-BAG other-term term)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable SYNTAX-REMOVE-BAG-fn
                              SYNTAX-MEMBERP-fn))))


#|

;really want the -alt form?
(defthm not-syntax-memberp-means-not-in-syntactic-intersection
  (implies (not (syntax-memberp x y))
           (not (syntax-memberp x (syntax-intersection y other-term))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-intersection syntax-memberp))))
|#


(in-theory (disable SYNTAX-MEMBERP-FN))

(defthm hack-eric
  (implies (and (val 0 (syntax-remove-bag-1 other-term y))
                (not (syntax-memberp x y))
                )
           (not (syntax-memberp x other-term)))
  :hints (("Goal" :in-theory (enable syntax-memberp-fn)
           :do-not '(generalize eliminate-destructors))))


(defthm not-syntax-memberp-means-not-syntax-memberp-of-syntax-remove-1
  (implies (not (syntax-memberp x y))
           (not (syntax-memberp x (val 1 (syntax-remove-1 elem y)))))
  :hints (("Goal" :in-theory (enable syntax-remove-1-fn syntax-memberp-fn))))


#|
;could show that syntactic-intersection is a syntactic subset of each arg?
(defthm not-syntax-memberp-means-not-in-syntactic-intersection-alt
  (implies (not (syntax-memberp x y))
           (not (syntax-memberp x (syntax-intersection other-term y))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (syntax-intersection syntax-memberp
                              )
                           (poopsmith
                            (:induction  syntax-memberp))))))

|#


;BOZO change names!
(defthm syntax-remove-bag-cannot-increase-count-one
  (equal (< (count elem (syntax-ev term1 a))
            (count elem (syntax-ev (val 1 (syntax-remove-bag term1 term2)) a)))
         nil)
 :hints (("Goal" :in-theory (enable syntax-remove-bag-fn))))

(defthm syntax-remove-bag-1-cannot-increase-count
  (equal (< (count elem (syntax-ev term2 a))
            (count elem (syntax-ev (val 1 (syntax-remove-bag-1 term1 term2)) a)))
         nil))

(defthm syntax-remove-bag-cannot-increase-count-two
  (equal (< (count elem (syntax-ev term2 a))
            (count elem (syntax-ev (val 2 (syntax-remove-bag term1 term2)) a)))
         nil)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag-fn))))


(defthm bubs
  (<= (count elem (syntax-ev (val 2 (syntax-remove-bag (val 1 (syntax-remove-bag term1 term2)) term3)) a))
      (count elem (syntax-ev term3 a)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (disable syntax-remove-bag-cannot-increase-count-two)
           :use (:instance syntax-remove-bag-cannot-increase-count-two (term1 (val 1 (syntax-remove-bag term1 term2))) (term2 term3)))))


(defthm checkinemail
  (<= (count (syntax-ev elem a)
             (syntax-ev (syntax-intersection term1 term2) a))
      (count (syntax-ev elem a)
             (syntax-ev term1 a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-intersection-fn)))
  )






;whoa! this proved!
(defthm syntax-remove-bag-does-the-right-thing-helper
  (equal (- (count elem (syntax-ev term1 a))
            (count elem (syntax-ev term2 a)))
         (- (count elem (syntax-ev (v1 (syntax-remove-bag term1 term2)) a))
            (count elem (syntax-ev (v2 (syntax-remove-bag term1 term2)) a))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag-fn; subbagp
                              ))))

(defthm not-syntax-memberp-means-syntax-remove-1-does-nothing
  (implies (not (syntax-memberp elem term))
           (equal (val 1 (syntax-remove-1 elem term))
                  term)))


(in-theory (disable SYNTAX-REMOVE-BAG-1-fn SYNTAX-MEMBERP-fn))

(in-theory (disable SUBBAGP-OF-REMOVE-1-FROM-SUBBAGP)) ;why needed?

#|
(thm
 (implies (not (syntax-memberp elem term))
          (implies (memberp (syntax-ev elem alist)
                            (syntax-ev (val 2 (syntax-remove-bag other-term term)) alist))
                   (memberp (syntax-ev elem alist)
                            (syntax-ev term alist))))
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
          :in-theory (enable syntax-remove-bag))))


;not true?
(thm
 (implies (not (syntax-memberp elem term))
          (implies (memberp (syntax-ev elem alist)
                            (syntax-ev term alist))
                   (memberp (syntax-ev elem alist)
                            (syntax-ev (val 2 (syntax-remove-bag other-term term)) alist))))
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
          :in-theory (enable syntax-remove-bag SYNTAX-REMOVE-BAG-1))))

;bozo make equal
(defthm syntax-remove-bag-does-the-right-thing
  (implies (subbagp (syntax-ev term1 alist) (syntax-ev term2 alist))
           (subbagp (syntax-ev (v1 (syntax-remove-bag term1 term2)) alist)
                    (syntax-ev (v2 (syntax-remove-bag term1 term2)) alist)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag; subbagp
                              ))))



    (implies (and (v0 (syntax-remove-bag list1 list2))
                  (equal (syntax-ev
                          (v2 (syntax-remove-bag list1 list2)) alist)
                         nil)
                  )
             (subbagp (syntax-ev list2 alist) (syntax-ev list1 alist)))
    :hints (("Goal" :do-not '(generalize eliminate-destructors)
;             :induct (SYNTAX-REMOVE-BAG LIST1 LIST2)
 ;            :do-not-induct t
             :in-theory (e/d (SUBBAGP-CONS-TO-SUBBAGP-REMOVE-1
                              syntax-remove-bag
                              not-v1-syntax-remove-1)
                             (
                              (:REWRITE SUBBAGP-OF-CONS)
                              SUBBAGP-OF-REMOVE-1-BOTH
                              )))
            ))

  )


(thm
 (IMPLIES
  (SUBBAGP (SYNTAX-EV (VAL 2 (SYNTAX-REMOVE-BAG x1 Y)) alist)
           (SYNTAX-EV x2 alist))
  (SUBBAGP (SYNTAX-EV Y alist)
           (APPEND (SYNTAX-EV x1 alist)
                   (SYNTAX-EV x2 alist))))
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
          :in-theory (enable SYNTAX-REMOVE-BAG))))


(thm
 (implies (not (syntax-ev (val 2 (syntax-remove-bag x y)) alist))
          (subbagp (syntax-ev y alist) (syntax-ev x alist)))
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
          :in-theory (enable syntax-remove-bag
                             subbagp
                             ))))


(thm
 (IMPLIES
  (NOT
   (SYNTAX-EV
    (VAL 2
               (SYNTAX-REMOVE-BAG x2
                                  (VAL 2
                                             (SYNTAX-REMOVE-BAG x1 y)))) alist))
  (SUBBAGP (SYNTAX-EV y alist)
           (APPEND (SYNTAX-EV x1 alist)
                   (SYNTAX-EV x2 alist))))
 :hints (("Goal" :in-theory (enable SYNTAX-REMOVE-BAG))))

(local
  (defthm syntax-subbagp-implements-subbagp-syntax-ev-nil
    (implies (and (v0 (syntax-remove-bag list1 list2))
                  (equal (syntax-ev (v2 (syntax-remove-bag list1 list2)) alist)
                         nil)
                  )
             (subbagp (syntax-ev list2 alist) (syntax-ev list1 alist)))
    :hints (("Goal" :do-not '(generalize eliminate-destructors)
;             :induct (SYNTAX-REMOVE-BAG LIST1 LIST2)
 ;            :do-not-induct t
             :in-theory (e/d (SUBBAGP-CONS-TO-SUBBAGP-REMOVE-1
                              syntax-remove-bag
                              not-v1-syntax-remove-1)
                             (
                              (:REWRITE SUBBAGP-OF-CONS)
                              SUBBAGP-OF-REMOVE-1-BOTH
                              )))
            ))

  )

|#



(defthm *trigger*-syntax-ev-syntax-subbagp
  (implies (and (unique list2)
                (meta-subbagp list1 list2)
                )
           (unique list1))
  :hints (("Goal" :in-theory (enable meta-subbagp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;--------------------- SUBBAGP-PAIR --------------------------
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;A main lemma...
;To show disjointness of x1 and x2, we can find two other bags, list1 and list2, which we know are disjoint and
;which we can tell (syntactcally) are supersets of x1 and x2 (either x1 is a subset of list1 and x2 is a subset of
;list2, or vice versa).
(defthm *trigger*-subbagp-pair-disjoint
  (implies (and (disjoint list1 list2) ;list1 and list2 are free variables
                (subbagp-pair x1 x2 list1 list2))
           (disjoint x1 x2))
  :hints (("goal" :in-theory (enable subbagp-pair))))


(defthm v1-syntax-remove-bag-1-implication-lemma
  (implies (and (v0 (syntax-remove-bag-1 u y))
                (subbagp (syntax-ev v a)
                         (syntax-ev (v1 (syntax-remove-bag-1 u y)) a))
                (equal (v1 (syntax-remove-bag v (v1 (syntax-remove-bag-1 u y))))
                       ''nil))
           (subbagp (append (syntax-ev u a)
                            (syntax-ev v a))
                    (syntax-ev y a))))


(defthm v2-subbagp-remove-bag
  (implies (and (v0 (syntax-remove-bag x list))
		(equal (v1 (syntax-remove-bag x list))
		       ''nil))
	   (perm (syntax-ev (v2 (syntax-remove-bag x list)) a)
		 (remove-bag (syntax-ev x a) (syntax-ev list a))))
  :hints (("Goal" :in-theory (enable syntax-remove-bag-fn))))

(defthm syntax-memberp-quoted-implies-memberp
  (implies (syntax-memberp (list 'quote elem) term)
           (memberp elem (syntax-ev term a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable SYNTAX-MEMBERP-fn))))

(defthm subbagp-when-cdr-is-non-consp
  (implies (and (not (consp (cdr x)))
                (consp x) ;move to conclusion?
                )
           (equal (subbagp x y)
                  (memberp (car x) y))))

;key lemma for subgoal 2 of syntax-unique-subbagps-implies-unique-subbagps
(defthm v1-syntax-remove-bag-implication
  (implies (and (v0 (syntax-remove-bag x y))
		(equal (v1 (syntax-remove-bag x y))
		       '(quote nil)))
	   (subbagp (syntax-ev x a)
                    (syntax-ev y a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag-fn))))




;disable stuff like this?
(defthm v2-syntax-remove-bag-implication-lemma
  (implies
   (and
    (subbagp (syntax-ev x a) (syntax-ev list a))
    (subbagp (syntax-ev y a) (syntax-ev (v2 (syntax-remove-bag x list)) a))
    (perm (syntax-ev (v2 (syntax-remove-bag x list)) a)
	  (remove-bag (syntax-ev x a) (syntax-ev list a)))
    )
   (subbagp (syntax-ev y a)
            (remove-bag (syntax-ev x a)
                        (syntax-ev list a)))))

(defthm v2-syntax-remove-bag-implication
  (implies
   (and
    (v0 (syntax-remove-bag x list))
    (equal (v1 (syntax-remove-bag x list))
	   ''nil)
    (v0 (syntax-remove-bag y (v2 (syntax-remove-bag x list))))
    (equal (v1 (syntax-remove-bag y (v2 (syntax-remove-bag x list))))
	   ''nil)
    )
   (subbagp (syntax-ev y a)
	   (remove-bag (syntax-ev x a)
			(syntax-ev list a))))
; Matt K. v7-1 mod for avoiding "Goal'", 2/13/2015: "Goal'" changed to "Goal".
  :hints (("Goal" :in-theory (disable v1-syntax-remove-bag-implication
				       v2-subbagp-remove-bag)
	   :use ((:instance v1-syntax-remove-bag-implication (y list))
		 (:instance v1-syntax-remove-bag-implication (x y)
			    (y (v2 (syntax-remove-bag x list))))
		 (:instance v2-subbagp-remove-bag)
		 ))))

;this is the key lemma for the meta rule
(defthm syntax-unique-subbagps-implies-unique-subbagps
  (implies (syntax-unique-subbagps x y list)
           (unique-subbagps (syntax-ev x a)
                            (syntax-ev y a)
                            (syntax-ev list a)))
  :hints (("Goal" :in-theory (enable syntax-unique-subbagps-fn
                                     unique-subbagps))))

(defun syntax-unique-subbagps-wrapper (term)
  (declare (type t term)
           (xargs :guard (pseudo-termp term))
           )
  (if (and (consp term)
	   (equal (car term) 'unique-subbagps) ;; (unique-subbagps x y list)
	   (consp (cdr term))
	   (consp (cddr term))
	   (consp (cdddr term))
	   (null  (cddddr term)))
      (let ((x (cadr term))
	    (y (caddr term))
	    (list (cadddr term)))
	(let ((hit (syntax-unique-subbagps-fn nil x y list)))
	  (if hit
	      `(quote t)
	    term)))
    term))

;is this no longer used?
(defthm *meta*-syntax-ev-syntax-unique-subbagps
  (equal (syntax-ev term a)
         (syntax-ev (syntax-unique-subbagps-wrapper term) a))
  :rule-classes ((:meta :trigger-fns (unique-subbagps)))
  :hints (("goal" :in-theory (enable syntax-unique-subbagps-irrelevant))))

;If list is unique and is big enough to contain both x and y, then x and y must be disjoint.
(defthm *trigger*-unique-subbagps-implies-disjointness
  (implies (and (unique list) ;list is a free variable
                (unique-subbagps x y list))
           (disjoint x y))
  :hints (("goal" :in-theory (enable unique-subbagps remove-bag disjoint)
           :do-not '(generalize eliminate-destructors))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;-------------------------- MEMBERP ------------------------
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
(defthm syntax-memberp-implements-memberp
  (implies (syntax-memberp x list)
           (memberp (syntax-ev x alist) (syntax-ev list alist))))

(defun syntax-memberp-wrapper (term)
  (declare (type t term))
  (if (and (consp term)
	   (equal (car term) 'meta-memberp) ;; (meta-memberp x list)
;	   (consp (cdr term))
	;   (consp (cddr term))
	   (null  (cdddr term)))
      (let ((x (cadr term))
	    (list (caddr term)))
	(let ((hit (syntax-memberp x list)))
	  (if hit
	      '(quote t)
	    term)))
    term))

;replace this with eric's rule?
(defthm *meta*-syntax-ev-syntax-memberp
  (equal (syntax-ev term alist)
         (syntax-ev (syntax-memberp-wrapper term) alist))
  :rule-classes ((:meta :trigger-fns (meta-memberp)))
  :hints (("Goal" :in-theory (enable meta-memberp))))
|#

;yuck?
(defthmd non-memberp-eric
  (implies (and (not (memberp a y)) ;y is a free variable
                (subbagp x y))
           (equal (memberp a x)
                  nil)))

;bozo ti of REMOVE-BAG-OVER-REMOVE-1 and REMOVE-1-OF-REMOVE-BAG
;bozo REMOVE-BAG-REMOVE-1 and REMOVE-BAG-OVER-REMOVE-1 !

#|
(thm
 (implies (and (true-listp x)
               (true-listp y))
          (equal (ACL2-COUNT (BINARY-APPEND Y X))
                 (+ (acl2-count x) (acl2-count y))))
 :hints (("Goal" :in-theory (enable append))))
|#


#|
zz

(thm
 (implies (and (val 0 (syntax-remove-bag-1 x y))
               (unique (syntax-ev y alist))
               )
          (equal (syntax-ev (val 1 (syntax-remove-bag-1 x y)) alist)
                 (remove-bag (syntax-ev x alist)
                             (syntax-ev y alist))))
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
          :in-theory (enable syntax-remove-bag-1
                             ;unique
                             ))))

PUTBACK
(defthm v1-syntax-remove-bag-1-is-remove-bag
   (implies (and (unique (syntax-ev list alist))
                 (true-listp (syntax-ev list alist))
                 (v0 (syntax-remove-bag-1 x list)))
            (equal (syntax-ev (v1 (syntax-remove-bag-1 x list)) alist)
                   (remove-bag (syntax-ev x alist) (syntax-ev list alist))))
   :hints (("goal" :do-not '(generalize eliminate-destructors)
            :in-theory (e/d (remove-bag-append-disjoint
                             syntax-remove-bag-1
;remove-bag
                             )
                            (remove-bag-append)))))
|#

;when do we use these?
(defthm v1-syntax-remove-1-is-remove-1
   (implies (and (unique (syntax-ev term a)) ;why this hyp?
                 (v0 (syntax-remove-1 elem term)))
            (equal (syntax-ev (v1 (syntax-remove-1 elem term)) a)
                   (remove-1 (syntax-ev elem a) (syntax-ev term a))))
   :hints (("Goal" :in-theory (e/d ( ;remove-1
				    syntax-remove-1-fn
				    REMOVE-1-APPEND
				    remove-bag-append-disjoint
				    disjoint-memberp-implies-non-membership
				    SYNTAX-MEMBERP-fn
				    remove-1
				    )
				   (
				    CONS-CAR-ONTO-REMOVE-1-OF-CDR ;BOZO why did i need to disable this?
				    ))
            :do-not '(generalize eliminate-destructors))))

#|
PUTBACK
(defthm v2-syntax-remove-bag-is-remove-bag
   (implies (and (unique (syntax-ev list a))
                 (true-listp (syntax-ev list a))
                 (v0 (syntax-remove-bag x list))
                 (equal (v1 (syntax-remove-bag x list))
                        ''nil))
            (equal (syntax-ev (v2 (syntax-remove-bag x list)) a)
                   (remove-bag (syntax-ev x a) (syntax-ev list a))))
   :hints (("Goal" :in-theory (enable syntax-remove-bag))))
|#

;BOZO it would be nice if this returned a simplified term even if the first arg didn't simplify to nil.
(defun syntax-meta-remove-bag-wrapper (term)
   (declare (type t term)
            (xargs :guard (pseudo-termp term)))
   (if (and (consp term)
            (equal (car term) 'meta-remove-bag)
;            (consp (cdr term))
 ;           (consp (cddr term))
            (null  (cdddr term)))
       (met ((hit v1 v2) (syntax-remove-bag-fn nil (cadr term) (caddr term)))

            (if (and hit

                     (equal v1 '(quote nil))
                     )
                ;bozo consider remove-bag here?
                ;`(meta-remove-bag ,v1 ,v2)
                v2

              term))
     term))

;; (thm
;;  (implies (not (val 0 (syntax-remove-bag term1 term2)))
;;           (equal (syntax-intersection term1 term1)
;;                  ''nil))
;;    :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;             :in-theory (enable syntax-remove-bag syntax-intersection syntax-remove-bag-1))))


#|

(defthm hhelperh
  (implies t;(val 0 (syntax-remove-bag term1 term2))
           (perm (syntax-ev (val 1 (syntax-remove-bag term1 term2)) a)
                 (remove-bag (syntax-ev (syntax-intersection term1 term1) a)
                             (syntax-ev term1 a))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag syntax-intersection))))


   (PERM (REMOVE-BAG (SYNTAX-EV TERM3 a)
                     (SYNTAX-EV TERM5 a))
         (REMOVE-BAG (SYNTAX-EV (VAL 1 (SYNTAX-REMOVE-BAG TERM3 TERM5)) a)
                     (SYNTAX-EV (VAL 2 (SYNTAX-REMOVE-BAG TERM3 TERM5)) a)))

|#

(defthm *meta*-syntax-ev-meta-remove-bag-perm
   (perm (syntax-ev term a)
         (syntax-ev (syntax-meta-remove-bag-wrapper term) a))
   :hints (("goal" :in-theory (enable meta-remove-bag
				      syntax-remove-bag-irrelevant)))
   :rule-classes ((:meta :trigger-fns (meta-remove-bag))))

;trying a change where this handles remove-1 instead of meta-remove-1
(defun syntax-remove-1-wrapper (term)
   (declare (type t term)
            (xargs :guard (pseudo-termp term)))
   (if (and (consp term)
            (equal (car term) 'remove-1) ;(equal (car term) 'meta-remove-1)
;            (consp (cdr term))
 ;           (consp (cddr term))
            (null  (cdddr term)) ;why?
            )
       (met ((hit v1) (syntax-remove-1-fn nil (cadr term) (caddr term)))
            (if hit ;if we succeeded, then
                v1 ;return the resulting term
              term ;else, do nothing
              ))
     term))

#|
(defthm *meta*-syntax-ev-meta-remove-1-perm
  (perm (syntax-ev term a)
        (syntax-ev (syntax-meta-remove-1-wrapper term) a))
  :hints (("goal" :in-theory (enable meta-remove-1)))
  :rule-classes ((:meta :trigger-fns (meta-remove-1))))
 |#

(defthm *meta*-syntax-ev-remove-1-perm
  (perm (syntax-ev term a)
	(syntax-ev (syntax-remove-1-wrapper term) a))
  :hints (("goal" :in-theory (enable remove-1
				     SYNTAX-MEMBERP-irrelevant
				     syntax-remove-1-irrelevant)))
  :rule-classes ((:meta :trigger-fns (remove-1))))




(defun which-subbagp (x list1 list2 key)
  (declare (type t x list1 list2 key)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp list1)
                              (pseudo-termp list2)
                              (pseudo-termp key))))
  (or (and (syntax-subbagp-fn nil x list1)
           `((,key . (quote t))))
      (and (syntax-subbagp-fn nil x list2)
           `((,key . (quote nil))))))

(defmacro replace-perm (hit x y list)
  `(if ,hit (meta-remove-bag ,x (append ,y ,list))
     ,list))

(defthm perm-free-substitution
  (implies (and (perm x y)
                (bind-free (which-subbagp x list1 list2 'in1) (in1))
                (meta-subbagp x (if in1 list1 list2))
                (equal in2 (not in1))
                )
           (equal (perm list1 list2)
                  (perm (replace-perm in1 x y list1)
                        (replace-perm in2 x y list2))))
  :hints (("Goal" :in-theory (enable meta-subbagp meta-remove-bag))))

#|
;BOZO wrong value on (common-elements '(cons b nil) '(cons a (cons b nil)))?
;should we just write a function for the syntactic intersection of two terms, instead of calling syntax-remove-bag?
(defun common-elements (term1 term2)
  (declare (type t term1 term2))
  (met ((hit xterm1 xterm2) (syntax-remove-bag term1 term2))
       (declare (ignore xterm2))
       (if (not hit)
           (mv nil nil)
         (met ((hit xterm1 sub) (syntax-remove-bag xterm1 term1))
              (declare (ignore xterm1))
              (mv
               hit ;should this be t?  what if xterm1 is nil?
               sub)))))

(defun bind-common-elements (term1 term2 key)
  (declare (type t term1 term2 key))
  (met ((hit common) (common-elements term1 term2))
       (if (not hit) nil
         `((,key . ,common)))))


;cancel common stuff from both sides of a perm.
;BOZO consider doing the same for a subbagp and a remove-bag?
(defthm perm-common-elimination
  (implies (and (bind-free (bind-common-elements list1 list2 'x) (x))
                (meta-subbagp x list1)
                (meta-subbagp x list2))
           (equal (perm list1 list2)
                  (perm (meta-remove-bag x list1)
                        (meta-remove-bag x list2))))
  :hints (("Goal" :in-theory (enable meta-subbagp;BOZO why did I have to enable this?
                                     meta-remove-bag))))
|#

;   (in-theory (disable perm-consp-remove-1))

;; I don't know how expensive these rules are in practice.
;; For now, I disable them until needed.

(in-theory
 (disable
  perm-free-substitution
;  perm-common-elimination
  ))

;; Nonetheless, perm-common-elimination should be used in
;; place of such hack rules as these ..

(in-theory
 (disable
  perm-cons-x-y-z
  perm-append-x-y-z
  ;perm-append-y-z-a
  perm-append-x-a-y-append-a-z
  ))

;; This comment is probably not entirely correct:
;; I think I know more about congruence based rewriting now.  I don't
;; think we need the meta rules stated above to do effective perm
;; reasoning.
;;
;; I think proving congruence and associative rules for append/cons/
;; etc should be enough .. we are close even now. I'm not sure how
;; destructors factor in (remove-1, remove-bag, etc), but I bet there
;; is a good strategy somewhere.
;;
;; So, in the future we may want to transition to rules of this form
;; to do perm reasoning:

;;
;; Try to clean up the perm mess a bit ..
;;

(in-theory
 (disable
;  perm-not-consp-nil
 ; perm-remove-bag-x-x
;  perm-append
  perm-cons-append
  perm-append-remove-1
;  perm-remove-1
 ; perm-remove-bag
  subbagp-perm-append-remove-bag
  perm-cons-reduction
  perm-nil-y
;  perm-remove-bag-2
  perm-consp-remove-1
  perm-subbagp-subbagp
  remove-1-cons
  ))


;;
;; Some meta trigger functions we need to keep around
;;

(in-theory
 (disable
;  meta-remove-bag
 ;meta-remove-1
  ))



;;=================================================================================
;; :meta rule to simplify (memberp x lst) when we know that X is not a member of
;; certain things (namely, things syntactically present in LST).
;==================================================================================

;We are rewriting a term of the form (memberp x lst).  First, gather the list L of all the things which we know
;syntactically from the goal do not contain x; that is, L contains all BLAH such that the goal contains (not (memberp x blah)).
;Be careful not to use the literal which we're currently rewriting!  If L is empty, do nothing.  Otherwise,
;process Z as follows:  Z is a nest of conses and appends.  We ignore the conses.  If we find an element of L being
;appended, we drop it.  If we find an element of L at a leaf, we also discard it.
;We refuse to look inside any function which is not a cons or an append.

(defevaluator ev2 ev2-list
  ((memberp x l)
   (binary-append x y)
   (cons x y)
   (not x)
   (if x y z)
   ))

;returns the list of all BLAH such that mfc contains a literal of the form (not (memberp x BLAH)).
;doesn't allow BLAH to be Z, though.
;a hyp of the form (not (memberp x lst)) will appear negated in the clause as (memberp x lst)
;BOZO this should use the type-alist, not the clause
(defun get-irrel-list-from-clause (x z clause)
  (declare (type t x clause)
;           (xargs :guard (pseudo-termp term))
           )
  (if (not (consp clause))
      nil
    (let ((literal (car clause)))
      (if (and (consp literal)
               (equal (car literal) 'memberp)
               (consp (cdr literal))
               (equal x (cadr literal))
               (consp (cddr literal))
               (not (equal z (caddr literal))) ;skip this case...
               )
          (cons (caddr literal) (get-irrel-list-from-clause x z (cdr clause)))
        (get-irrel-list-from-clause x z (cdr clause))))))


;pass in x?  have a case to handle constants like the meta rule above does?
;write this more efficiently?  bozo make this more efficient can we avoid some
;consing by adding a passing a flag which indicates whether the recursive
;calls changed anything?  bozo don't depend on append nest being associated?

(defun simplify-cons-and-append-nest-given-irrelevant-lists (nest irrel-list)
  (declare (type t nest irrel-list))
  (if (not (equal 3 (len nest))) ;calls to cons and binary-append have length 3
      ;we've hit a leaf; check whether it is something in the irrelevant list.
      (if (memberp nest irrel-list)
          ''nil
        nest)
    (if (equal (car nest) 'cons)
        (list 'cons (cadr nest) (simplify-cons-and-append-nest-given-irrelevant-lists (caddr nest) irrel-list))
      (if (equal (car nest) 'binary-append)
       ;We don't have to recur on (cadr nest) because we know it won't be an append or a cons, because of how
       ;nests of those functions get normalized?
          (if (memberp (cadr nest) irrel-list) ;we're appending something irrelevant, so drop it
              (simplify-cons-and-append-nest-given-irrelevant-lists (caddr nest) irrel-list)
            (list 'binary-append (cadr nest)
                  (simplify-cons-and-append-nest-given-irrelevant-lists (caddr nest) irrel-list)))
       ;We've found something that is neither a cons nor an append.
        (if (memberp nest irrel-list)
            ''nil
          nest))
      )
    ))

(set-state-ok t)


(defun simplify-cons-and-append-nest (term mfc state)
  (declare (ignore state) (type t term mfc state))
  (if (not (and (equal 3 (len term))
                (equal (car term) 'memberp)))
      term
    (let ((irrel-list (get-irrel-list-from-clause (cadr term) (caddr term) (mfc-clause mfc))))
      (if (not (consp irrel-list))
          term
        (list 'memberp
              (cadr term)
              (simplify-cons-and-append-nest-given-irrelevant-lists (caddr term) irrel-list))))))

(defun make-not-memberp-claim (x term)
  (declare (type t x term))
  `(not (memberp ,x ,term)))

(defun hyp-fun-simplify-cons-and-append-nest-given-irrelevant-lists (x nest irrel-list)
  (declare (type t x nest irrel-list))
  (if (not (equal 3 (len nest))) ;calls to cons and binary-append have length 3
       ;we've hit a leaf:
      (if (memberp nest irrel-list)
          (make-not-memberp-claim x nest) ;we dropped nest
        ''nil ;no hyps necessary
        )
    (if (equal (car nest) 'cons)
        (hyp-fun-simplify-cons-and-append-nest-given-irrelevant-lists x (caddr nest) irrel-list)
      (if (equal (car nest) 'binary-append)
       ;We don't have to recur on (cadr nest) because we know it won't be an append or a cons, because of how
       ;nests of those functions get normalized?
          (if (memberp (cadr nest) irrel-list) ;we're appending something irrelevant, so drop it
              (list 'if (make-not-memberp-claim x (cadr nest))
                    (hyp-fun-simplify-cons-and-append-nest-given-irrelevant-lists x (caddr nest) irrel-list)
                    ''nil)
            (hyp-fun-simplify-cons-and-append-nest-given-irrelevant-lists x (caddr nest) irrel-list))
       ;We've found something that is neither a cons nor an append.
        (if (memberp nest irrel-list)
            (make-not-memberp-claim x nest) ;we dropped nest
          ''nil ;no hyps necessary
          )
        )
      )))


(defun hyp-fun-simplify-cons-and-append-nest (term mfc state)
  (declare (ignore state)  (type t term mfc state))
  (if (not (and (equal 3 (len term))
                (equal (car term) 'memberp)))
      'nil
    (let ((irrel-list (get-irrel-list-from-clause (cadr term) (caddr term) (mfc-clause mfc))))
      (if (not (consp irrel-list))
          'nil
        (hyp-fun-simplify-cons-and-append-nest-given-irrelevant-lists (cadr term) (caddr term) irrel-list)))))

(encapsulate
 ()
 (local
  (defthm helper-eric
    (implies
     (ev2 (hyp-fun-simplify-cons-and-append-nest-given-irrelevant-lists x nest irrel-list)
          a)
     (equal (memberp (ev2 x a) (ev2 nest a))
            (memberp (ev2 x a) (ev2 (simplify-cons-and-append-nest-given-irrelevant-lists nest irrel-list) a))))
    :hints (("Goal" :do-not '(generalize eliminate-destructors)))))

;bozo bad name; what we're simplifying is actually a call to memberp
 (defthm meta-rule-to-simplify-cons-and-append-nest
   (implies (ev2 (hyp-fun-simplify-cons-and-append-nest term mfc state) a)
            (equal (ev2 term a)
                   (ev2 (simplify-cons-and-append-nest term mfc state) a)))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)))
   :rule-classes ((:meta :trigger-fns (memberp)))))


(encapsulate
 ()
 (local (defthm test
          (implies (not (memberp x foo))
                   (equal (memberp x (append a foo))
                          (memberp x a)))
          :hints (("Goal" :in-theory (disable memberp-of-cons MEMBERP-of-APPEND))))))


(defun syntax-subbagp-wrapper (term)
  (declare (type t term)
           (xargs :guard (pseudo-termp term))
           )
  (if (and (consp term)
	   (equal (car term) 'meta-subbagp) ;; (meta-subbagp list1 list2)
;	   (consp (cdr term))
	;   (consp (cddr term))
	   (null  (cdddr term)))
      (let ((list1 (cadr term))
	    (list2 (caddr term)))
	(let ((hit (syntax-subbagp-fn nil list1 list2)))
	  (if hit
	      '(quote t)
	    term)))
    term))


(defun syntax-subbagp-pair-wrapper (term)
  (declare (type t term)
           (xargs :guard (pseudo-termp term)))
  (if (and (consp term)
	   (equal (car term) 'subbagp-pair) ;; (subbagp-pair x1 x2 list1 list2)
;	   (consp (cdr term))
	;   (consp (cddr term))
	 ;  (consp (cdddr term))
	  ; (consp (cddddr term))
	   (null  (cdddddr term)))
      (let ((x1    (cadr term))
	    (x2    (caddr term))
	    (list1 (cadddr term))
	    (list2 (caddddr term)))
	(let ((hit (syntax-subbagp-pair-fn nil x1 x2 list1 list2)))
	  (if hit
	      `(quote t)
	    term)))
    term))



;(my-syntax-subbagp '(cons a x) '(cons b (cons a x)))
;(my-syntax-subbagp '(cons a x) '(cons a x))

#|

;key lemma for *meta*-syntax-ev-syntax-subbagp
;bozo rename
 (defthm syntax-subbagp-implements-subbagp
   (implies (and (v0 (syntax-remove-bag list1 list2))
                 (equal (v2 (syntax-remove-bag list1 list2))
                        '(quote nil))
                 )
            (subbagp (syntax-ev list2 a) (syntax-ev list1 a)))
   :hints (("Goal" :in-theory (enable meta-subbagp)))))

(thm
 (perm (syntax-ev (val 1 (syntax-remove-bag term1 term2)) a)
       (remove-bag (syntax-ev (syntax-intersection term1 term2) a) (syntax-ev term1 a)))
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
          :in-theory (enable syntax-remove-bag
                             syntax-intersection
                             ))))



|#


(defthm hhelper
  (implies (val 0 (syntax-subbagp-helper term1 term2))
           (perm (syntax-ev (val 1 (syntax-subbagp-helper term1 term2)) a)
                 (remove-bag (syntax-ev term1 a) (syntax-ev term2 a))))
  :hints (("Goal" :in-theory (enable syntax-subbagp-helper-fn))))

(defthm syntax-subbagp-helper-implements-subbagp
  (implies (v0 (syntax-subbagp-helper term1 term2))
           (subbagp (syntax-ev term1 a) (syntax-ev term2 a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-subbagp-helper-fn
                              meta-subbagp)))
  :rule-classes (:rewrite :forward-chaining))

(defthm syntax-subbagp-implements-subbagp
  (implies (syntax-subbagp term1 term2)
           (subbagp (syntax-ev term1 a) (syntax-ev term2 a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (meta-subbagp syntax-subbagp-fn) (syntax-subbagp-helper-fn))))
  :rule-classes (:rewrite :forward-chaining))

;do we need this rule? previously, meta-subbagp was enabled (!), and so this rule probably didn't fire.
;yet we seem to have gotten by without it??
(defthm *meta*-syntax-ev-syntax-subbagp
  (equal (syntax-ev term a)
         (syntax-ev (syntax-subbagp-wrapper term) a))
  :rule-classes ((:meta :trigger-fns (meta-subbagp)))
  :hints (("Goal" :in-theory (enable syntax-subbagp-irrelevant meta-subbagp))))

(defthm syntax-subbagp-pair-implies-subbagp-pair-x
  (implies (syntax-subbagp-pair x1 x2 list1 list2)
           (subbagp-pair (syntax-ev x1 a)
                         (syntax-ev x2 a)
                         (syntax-ev list1 a)
                         (syntax-ev list2 a)))
  :hints (("Goal" :in-theory (enable subbagp-pair syntax-subbagp-pair-fn)))
  :rule-classes (:rewrite :forward-chaining))

(defthm *meta*-syntax-ev-subbagp-pair
  (equal (syntax-ev term a)
         (syntax-ev (syntax-subbagp-pair-wrapper term) a))
  :hints (("goal" :in-theory (enable SYNTAX-SUBBAGP-PAIR-irrelevant)))
  :rule-classes ((:meta :trigger-fns (subbagp-pair))))

;If we can tell syntactically that term1 and term2 have stuff in common,
;return an alist binding the name indicated by key to that stuff.  Otherwise,
;return nil.

(defun my-bind-common-elements (term1 term2 key)
  (declare (type t term1 term2 key)
           (xargs :guard (and (pseudo-termp term1)
                              (pseudo-termp term2)
                              (pseudo-termp key))))
  (let ((common (bag::syntax-intersection-fn nil term1 term2)))
    (if (equal common ''nil)
        nil
      `((,key . ,common)))))


;trying with this enabled...
;BOZO consider replacing this with a :meta rule that calls syntax-remove-bag?
(defthm my-perm-common-elimination
  (implies (and (bind-free (my-bind-common-elements list1 list2 'x) (x))
                (bag::meta-subbagp x list1)
                (bag::meta-subbagp x list2))
           (equal (perm list1 list2)
                  (perm (bag::meta-remove-bag x list1)
                        (bag::meta-remove-bag x list2))))
  :hints (("Goal" :in-theory (enable bag::meta-subbagp       ;BOZO why did I have to enable this?
                                     bag::meta-remove-bag))))


#|
(defun perm-cancel-metafunction (term)
  (declare (type t term))
  (if (and (consp term)
           (equal 'perm (car term))
           (consp (cdr term))
           (consp (cddr term))
           (null (cdddr term)))
      (met ((hit newarg1 newarg2) (syntax-remove-bag (cadr term) (caddr term)))
           (if hit
               `(perm ,newarg1 ,newarg2)
             term))
    term))


(thm
 (IMPLIES (VAL 0 (SYNTAX-REMOVE-BAG-1 TERM1 TERM2))
         (SUBBAGP (SYNTAX-EV TERM1 alist)
                  (SYNTAX-EV TERM2 alist))))

;expensive?
(defthm subbagp-other-way
  (implies (subbagp y x)
           (equal (subbagp x y)
                  (perm x y)))
  :hints (("Goal" :in-theory (enable subbagp perm))))

(thm
 (IMPLIES  (SUBBAGP (SYNTAX-EV (VAL 1 (SYNTAX-REMOVE-BAG TERM1 TERM2)) alist)
                    (REMOVE-1 (SYNTAX-EV elem alist)
                              (SYNTAX-EV (VAL 2 (SYNTAX-REMOVE-BAG TERM1 TERM2)) alist)))
           (SUBBAGP (SYNTAX-EV TERM1 alist)
                    (REMOVE-1 (SYNTAX-EV elem alist)
                              (SYNTAX-EV TERM2 alist))))
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
          :in-theory (enable syntax-remove-bag
                             subbagp))))

(thm
 (implies (subbagp (syntax-ev (val 1 (syntax-remove-bag term1 term2)) alist)
                   (syntax-ev (val 2 (syntax-remove-bag term1 term2)) alist))
          (subbagp (syntax-ev term1 alist)
                   (syntax-ev term2 a)))
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
          :in-theory (enable syntax-remove-bag
                             subbagp))))


(thm
 (implies (subbagp (syntax-ev term1 a)
                   (syntax-ev term2 a))
          (subbagp (syntax-ev (val 1 (syntax-remove-bag term1 term2)) a)
                   (syntax-ev (val 2 (syntax-remove-bag term1 term2)) a)))
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
          :in-theory (enable syntax-remove-bag perm))))


(thm
 (implies (perm (syntax-ev (val 1 (syntax-remove-bag term1 term2)) a)
                (syntax-ev (val 2 (syntax-remove-bag term1 term2)) a))
          (perm (syntax-ev term1 a)
                (syntax-ev term2 a)))
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
          :in-theory (enable syntax-remove-bag))))



(thm
 (implies (perm (syntax-ev term1 a)
                (syntax-ev term2 a))
          (perm (syntax-ev (val 1 (syntax-remove-bag term1 term2)) a)
                (syntax-ev (val 2 (syntax-remove-bag term1 term2)) a)))
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
          :in-theory (enable syntax-remove-bag perm))))

(thm
 (equal (perm (syntax-ev (val 1 (syntax-remove-bag term1 term2)) a)
              (syntax-ev (val 2 (syntax-remove-bag term1 term2)) a))
        (perm (syntax-ev term1 a)
              (syntax-ev term2 a)))
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
          :in-theory (enable syntax-remove-bag))))


(defthm meta-perm-cancel
  (equal (syntax-ev term a)
         (syntax-ev (perm-cancel-metafunction term) a))
  :rule-classes ((:meta :trigger-fns (perm))))




|#

#|


(defthm SYNTAX-REMOVE-BAG-kills-all-of-term1-means-subbagp
  (IMPLIES (EQUAL (VAL 1 (SYNTAX-REMOVE-BAG TERM1 TERM2))
                  ''NIL)
           (subbagp (SYNTAX-EV TERM1 a)
                    (SYNTAX-EV TERM2 a)
                    ))
  :hints (("Goal" :in-theory (enable SYNTAX-REMOVE-BAG))))


(thm
 (implies
  (val 0 (syntax-subbagp-helper term1 term2))
  (equal (val 1 (syntax-subbagp-helper term1 term2))
         (val 2 (syntax-remove-bag term1 term2))))
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
          :in-theory (enable syntax-remove-bag syntax-subbagp-helper))))


 (VAL
      0
      (SYNTAX-REMOVE-BAG-1 (CADDR TERM1)
                           (VAL 1
                                      (SYNTAX-SUBBAGP-HELPER (CADR TERM1)
                                                             TERM2)))))

(defthm syntax-remove-bag-kills-all-of-term1-means-subbagp
  (implies (equal (val 1 (syntax-remove-bag term1 term2))
                  ''nil)
           (mv-nth 0 (syntax-subbagp-helper term1 term2)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag syntax-subbagp-helper))))


(thm
 (IMPLIES (EQUAL (VAL 1 (SYNTAX-REMOVE-BAG TERM1 TERM2))
                 ''NIL)
          (PERM (SYNTAX-EV (SYNTAX-INTERSECTION TERM1 TERM2) a)
                (SYNTAX-EV TERM1 a)

                )))


|#

#|

(defthm REMOVE-1-car-remove-bag-under-perm
  (PERM
   (REMOVE-1 (CAR y) (REMOVE-BAG x y))
   (REMOVE-BAG x (CDR y))))

;prove this!  could we just code syntax-remove-bag this way?
;no! it involves consing up the intersection?  but the other way involves consing up new terms?
;we say perm because the final cdrs might not match?
(thm
 (perm (syntax-ev (val 1 (syntax-remove-bag term1 term2)) a)
       (remove-bag (syntax-ev (syntax-intersection term1 term2) a) (syntax-ev term1 a)))
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
          :in-theory (enable syntax-remove-bag
                             syntax-intersection
                             ))))
;sheesh.  do we really need a notion of syntactic perm?
(defthm not-syntax-memberp-means-not-in-syntactic-intersection-alt
  (equal (syntax-memberp elem (syntax-intersection x y))
         (syntax-memberp elem (syntax-intersection y x)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-intersection syntax-memberp))))




(defthm subbagp-from-subbagp-of-append-1
  (implies (subbagp (append x y) z)
           (subbagp x z))
  :hints (("Goal" :in-theory (enable subbagp))))

(defthm subbagp-from-subbagp-of-append-two
  (implies (subbagp (append x y) z)
           (subbagp x z))
  :hints (("Goal" :use subbagp-from-subbagp-of-append-1
           :in-theory (disable subbagp-from-subbagp-of-append-1))))

(defthm syntax-remove-bag-does-the-right-thing
  (implies (subbagp (syntax-ev term1 a) (syntax-ev term2 a))
           (subbagp (syntax-ev (v1 (syntax-remove-bag term1 term2)) a)
                    (syntax-ev (v2 (syntax-remove-bag term1 term2)) a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag;
                              ;subbagp
                              ))))


(defthm syntax-remove-bag-does-the-right-thing
  (equal (subbagp (syntax-ev term1 a) (syntax-ev term2 a))
         (subbagp (syntax-ev (v1 (syntax-remove-bag term1 term2)) a)
                  (syntax-ev (v2 (syntax-remove-bag term1 term2)) a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag ;
;subbagp
                              ))))


(thm
 (implies
    (< (syntax-count elem term1)
       (syntax-count elem term2))
    (equal (count elem (syntax-ev term1 a))
           (+ (syntax-count elem term1)
              (count elem
                     (syntax-ev (val 1 (syntax-remove-bag term1 term2)) a)))))
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
          :in-theory (enable syntax-remove-bag))))

(defthm syntax-remove-bag-does-the-right-thing-helper1
  (equal (count elem (syntax-ev (v1 (syntax-remove-bag term1 term2)) a))
         (- (count elem (syntax-ev term1 a))
            (min (syntax-count elem term1)
                 (syntax-count elem term2))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag))))


  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag; subbagp
                              ))))





prove these about remove-bag-1
(defthm count-of-syntax-remove-bag-1
  (equal (count (syntax-ev x a)
                (syntax-ev (val 1 (syntax-remove-bag-1 x y)) a))
         (if (syntax-memberp x y)
             (+ -1 (count (syntax-ev x a)
                          (syntax-ev y a)))
           (count (syntax-ev x a)
                  (syntax-ev y a))))
  :hints (("Goal" :in-theory (enable syntax-remove-1)
           :do-not '(generalize eliminate-destructors))))

(defthm count-of-syntax-remove-1-better
  (equal (count elem (syntax-ev (val 1 (syntax-remove-1 x y)) a))
         (if (equal elem (syntax-ev x a))
             (if (syntax-memberp x y)
                 (+ -1 (count (syntax-ev x a)
                              (syntax-ev y a)))
               (count (syntax-ev x a)
                      (syntax-ev y a)))
           (count elem (syntax-ev y a))))
  :hints (("Goal" :in-theory (enable syntax-remove-1)
           :do-not '(generalize eliminate-destructors))))

to handle

(IMPLIES
  (AND (NOT (CONSP TERM1))
       (VAL 0 (SYNTAX-REMOVE-BAG-1 TERM1 TERM2)))
  (EQUAL (+ (COUNT ELEM (SYNTAX-EV TERM1 a))
            (COUNT ELEM
                   (SYNTAX-EV (VAL 1 (SYNTAX-REMOVE-BAG-1 TERM1 TERM2)) a)))
         (COUNT ELEM (SYNTAX-EV TERM2 a))))
|#



;odd proof?
;move some of this stuff?
(defthm syntax-memberp-implements-memberp
  (implies (syntax-memberp v x)
           (memberp (syntax-ev v a)
                    (syntax-ev x a)))
  :rule-classes (:rewrite :forward-chaining))

(defthm memberp-of-syntax-ev-helper
  (implies (and (syntax-memberp x blah)
                (subbagp (syntax-ev blah a) y))
           (memberp (syntax-ev x a) y))
  :hints (("Goal" :use (:instance syntax-memberp-implements-memberp (v x) (x blah) (a a))
           :in-theory (e/d ( non-memberp-eric) (syntax-memberp-implements-memberp)))))
