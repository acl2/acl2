;;  
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "LINEAR")
(include-book "std/util/bstar" :dir :system)
(include-book "linear-xdoc")

(mutual-recursion
 (defun term-list-has-free-vars (list)
   (if (not (consp list)) nil
     (or (term-has-free-vars (car list))
         (term-list-has-free-vars (cdr list)))))
 (defun term-has-free-vars (term)
   (if (not (consp term)) (symbolp term)
     (case-match term
       (('quote &) nil)
       ((& . args)
        (term-list-has-free-vars args)))))
 )

(defun atomize-term (x res)
  (if (not (consp x)) res
    (case-match x
      (('binary-+ x y)
       (let ((res (atomize-term x res)))
         (atomize-term y res)))
      (('binary-* x y)
       (let ((res (atomize-term x res)))
         (atomize-term y res)))
      (('unary-/ x)
       (atomize-term x res))
      (('expt x &)
       (atomize-term x res))
      (('unary-- x)
       (atomize-term x res))
      (& (if (term-has-free-vars x)
             (if (member-equal x res) res
               (cons x res))
           res)))))

(defun atomize-term-list (list res)
  (if (not (consp list)) res
    (let ((res (atomize-term (car list) res)))
      (atomize-term-list (cdr list) res))))

(defun atomize-linear-term (term)
  (case-match term
    (('equal x y)
     (let ((res (atomize-term x nil)))
       (atomize-term y res)))
    (('< x y)
     (let ((res (atomize-term x nil)))
       (atomize-term y res)))
    (('not x)
     (atomize-linear-term x))))

(defun atomize-key (x res)
  (if (not (consp x)) res
    (case-match x
      (('binary-* x y)
       (let ((res (atomize-key x res)))
         (atomize-key y res)))
      (('unary-/ x)
       (atomize-key x res))
      (('expt x &)
       (atomize-key x res))
      (& (if (term-has-free-vars x)
             (if (member-equal x res) res
               (cons x res))
           res)))))

(defun atomize-alist (alist res)
  (if (not (consp alist)) res
    (let ((entry (car alist)))
      (let ((key (car entry)))
        (let ((res (atomize-key key res)))
          (atomize-alist (cdr alist) res))))))

(defun atomize-poly (poly res)
  (let ((alist (access acl2::poly poly :alist)))
    (atomize-alist alist res)))

(defun atomize-term-lst (poly-lst res)
  (if (not (consp poly-lst)) res
    (let ((res (atomize-poly (car poly-lst) res)))
      (atomize-term-lst (cdr poly-lst) res))))

(defun atomize-poly-pot (pot res)
  (let ((res (atomize-term-lst (access acl2::linear-pot pot :negatives) res)))
    (atomize-term-lst (access acl2::linear-pot pot :positives) res)))

(defun atomize-pot-list (pot-list res)
  (if (not (consp pot-list)) res
    (let ((res (atomize-poly-pot (car pot-list) res)))
      (atomize-pot-list (cdr pot-list) res))))

(mutual-recursion
 (defun find-foo-args (x)
   (case-match x
     (('quote &) nil)
     (('foo a)
      (cons a (find-foo-args a)))
     ((& . args)
      (find-foo-args-list args))))
 (defun find-foo-args-list (x)
   (if (not (consp x)) nil
     (append (find-foo-args (car x))
             (find-foo-args-list (cdr x)))))
 )

(defun lt-term (x y)
  `(< '0 (BINARY-+ ,y (BINARY-+ (BINARY-* '-1 ,x) '0))))

(set-state-ok t)

(defun check-compliance (x j plist mfc state)
  (declare (xargs :stobjs state
                  :verify-guards nil)
           (ignorable state))
  (if (equal x j) nil
    (let ((lt-term (lt-term `(foo ,x) `(foo ,j))))
      (if (member-equal lt-term plist) nil
        (let ((lt-check (lt-term x j)))
          (mfc-ap `(not ,lt-check) mfc state))))))

(defun first-compliant (xlist j plist mfc state)
  (declare (xargs :stobjs state
                  :verify-guards nil)
           (ignorable state))
  (if (not (consp xlist)) nil
    (let ((x (car xlist)))
      (if (check-compliance x j plist mfc state) x
        (first-compliant (cdr xlist) j plist mfc state)))))

(mutual-recursion
 (defun term-vars (term)
   (if (not (consp term))
       (and (symbolp term) (list term))
     (case-match term
       (('quote &) nil)
       ((& . args)
        (term-list-vars args))
       (& nil))))
 (defun term-list-vars (args)
   (if (not (consp args)) nil
     (append (term-vars (car args))
             (term-list-vars (cdr args)))))
 )

(defun update-alist (key val alist)
  (let ((hit (assoc key alist)))
    (if (not hit) (mv t (acons key val alist))
      (if (equal (cdr hit) val)
          (mv t alist)
        (mv nil nil)))))

(mutual-recursion
 (defun match-atom (pattern term alist)
   (if (not (consp pattern))
       (if (not (symbolp pattern)) (mv nil nil)
         (update-alist pattern term alist))
     (if (not (consp term)) (mv nil nil)
       (case-match pattern
         (('quote v) (if (not (quotep term)) (mv nil nil)
                       (mv (equal (cadr term) v) alist)))
         ((fn . args)
          (if (not (equal (car term) fn)) (mv nil nil)
            (match-atom-args args (cdr term) alist)))
         (& (mv nil nil))))))
 (defun match-atom-args (plist tlist alist)
   (if (and (consp plist) (consp tlist))
       (mv-let (hit alist) (match-atom (car plist) (car tlist) alist)
         (if hit (match-atom-args (cdr plist) (cdr tlist) alist)
           (mv nil nil)))
     (mv t alist)))
 )

(defun match-atom-atom*-alist (b atoms alist)
  (if (not (consp atoms)) (list alist) ;; We don't want b to hog all of the possible matches.
    (mv-let (hit xlist) (match-atom b (car atoms) alist)
      (if hit (cons xlist (match-atom-atom*-alist b (cdr atoms) alist))
        (match-atom-atom*-alist b (cdr atoms) alist)))))

(defun match-atom-atom*-alist* (b atoms alist-list)
  (if (not (consp alist-list)) nil
    (append (match-atom-atom*-alist b atoms (car alist-list))
            (match-atom-atom*-alist* b atoms (cdr alist-list)))))

(defun match-atom*-atom*-alist* (blist atoms alist-list)
  (if (not (consp blist)) alist-list
    (let ((alist-list (match-atom-atom*-alist* (car blist) atoms alist-list)))
      (match-atom*-atom*-alist* (cdr blist) atoms alist-list))))

(defun all-matches (binders atoms alist)
  (match-atom*-atom*-alist* binders atoms (list alist)))

(defun keep-free-vars (free-vars alist)
  (if (not (consp free-vars)) (mv t nil)
    (let ((hit (assoc (car free-vars) alist)))
      (if (not hit) (mv nil nil)
        (mv-let (ok alist) (keep-free-vars (cdr free-vars) alist)
          (mv ok (cons hit alist)))))))

(defun keep-free-vars-list (free-vars alist-list)
  (if (not (consp alist-list)) nil
    (mv-let (ok alist) (keep-free-vars free-vars (car alist-list))
      (if (not ok) (keep-free-vars-list free-vars (cdr alist-list))
        (cons alist (keep-free-vars-list free-vars (cdr alist-list)))))))

(defun linear-binder-fn (name binding-atoms free-vars mfc state)
  (declare (xargs :mode :program)
           (ignorable name state))
  (b* ((pot-list   (access acl2::metafunction-context mfc :simplify-clause-pot-lst))
       (pot-atoms  (atomize-pot-list pot-list nil))
       (alist      (mfc-unify-subst mfc))
       (alist-list (all-matches binding-atoms pot-atoms alist)))
    (keep-free-vars-list free-vars alist-list)))

(defmacro linear-binder (name binding-atoms free-vars)
  `(bind-free (linear-binder-fn ',name ',binding-atoms ',free-vars mfc state) ,free-vars))

(defun def-linear-fn-instance (name conclusion free-hyps hyps trigger binding-atoms free-vars)
  `(:linear
    :trigger-terms (,trigger)
    :corollary (implies
                (and
                 ,@free-hyps
                 ,@(and free-vars `((linear-binder ,name ,binding-atoms ,free-vars)))
                 ,@hyps)
                ,conclusion)))

(defun def-linear-fn-instance-list (name conclusion free-hyps hyps tbf-list)
  (if (not (consp tbf-list)) nil
    (let ((entry (car tbf-list)))
      (let ((trigger       (car entry))
            (binding-atoms (cadr entry))
            (free-vars     (caddr entry)))
        (prog2$
         (or free-vars
             (cw "~%")
             (cw "*** Note: No free variables to bind!~%")
             (cw "*** trigger: ~x0~%" trigger)
             (cw "*** binding atoms : ~x0~%" binding-atoms)
             (cw "*** def::linear may not be required to express this rule!~%")
             (cw "~%"))
         (cons (def-linear-fn-instance name conclusion free-hyps hyps trigger binding-atoms free-vars)
               (def-linear-fn-instance-list name conclusion free-hyps hyps (cdr tbf-list))))))))

(defun remove-vars (x y)
  (if (not (consp x)) y
    (let ((y (remove (car x) y)))
      (remove-vars (cdr x) y))))

(defun remove-subsumed-binders (free-vars binder-atoms)
  (if (not (consp binder-atoms)) nil
    (let ((binder (car binder-atoms)))
      (if (remove-vars free-vars (term-vars binder))
          (cons binder (remove-subsumed-binders free-vars (cdr binder-atoms)))
        (remove-subsumed-binders free-vars (cdr binder-atoms))))))
      
(defun compute-tbf-list (free-vars trigger-atoms binder-atoms)
  (if (not (consp trigger-atoms)) nil
    (let ((trigger (car trigger-atoms)))
      (let ((bound-vars (append free-vars (term-vars trigger))))
        (let ((blist (remove-subsumed-binders bound-vars binder-atoms)))
          (cons (list
                 trigger
                 blist
                 (remove-vars bound-vars (term-list-vars blist)))
                (compute-tbf-list free-vars (cdr trigger-atoms) binder-atoms)))))))

(defun and-body (term)
  (case-match term
    (('and . body) body)
    (& (list term))))

(defun split-implication (rule)
  (case-match rule
    (('implies hyps conclusion)
     (mv (and-body hyps) conclusion))
    (&
     (mv nil rule))))

(defun check-coverage (name trigger-atoms vars)
  (if (not (consp trigger-atoms)) t
    (let ((atom (car trigger-atoms)))
      (if (remove-vars (term-vars atom) vars)
          (hard-error name
"

The proposed rule ~x1 contains unexpected free variables.
The following variables are considered free : ~x0
Perhaps :free-hyps could be used to bind those variables?
If not, your proposed :linear rule may be malformed.
"
(acons #\1 name (acons #\0 vars nil)))
        (check-coverage name (cdr trigger-atoms) vars)))))

(defun to-rule-classes-list (rule-classes)
  (and rule-classes
       (if (consp rule-classes) rule-classes
         (list rule-classes))))

(defun def-linear-fn (name free-hyps free-vars hyps hyp-vars conclusion hints rule-classes trigger-terms binder-terms)
  (declare (ignorable hyp-vars))
  (b* ((rule-classes     (to-rule-classes-list rule-classes))
       (conclusion-atoms (atomize-linear-term conclusion))
       (trigger-atoms    (if trigger-terms (atomize-term-list trigger-terms nil)
                           conclusion-atoms))
       ;;(trigger-atoms    (keep-unique-atoms trigger-atoms))
       (binder-atoms     (if binder-terms (atomize-term-list binder-terms nil)
                           conclusion-atoms))
       (bound-vars       (append free-vars (term-list-vars binder-atoms)))
       (conclusion-vars  (term-vars conclusion))
       )
    (let ((zed (check-coverage name trigger-atoms (remove-vars bound-vars (append conclusion-vars hyp-vars)))))
      (declare (ignore zed))
      (let ((tbf-list (compute-tbf-list free-vars trigger-atoms binder-atoms)))
        (let ((corollaries (def-linear-fn-instance-list name conclusion free-hyps hyps tbf-list)))
          `(encapsulate
               ()
             
             (defthm ,name
               (implies
                (and
                 ,@free-hyps
                 ,@hyps)
                ,conclusion)
               ,@(and hints `(:hints ,hints))
               :rule-classes (,@rule-classes
                              ,@corollaries
                              ))
             ))))))

(defun translate-list (list wrld state)
  (declare (xargs :mode :program))
  (if (not (consp list)) (mv nil nil state)
    (mv-let (err1 term state) (acl2::translate (car list) t t t nil wrld state)
      (mv-let (err2 res state) (translate-list (cdr list) wrld state)
        (mv (or err1 err2) (cons term res) state)))))

;; If so inclined, we could pass other 'bind-equiv' relations into this macro ..
;;
;; Hmm .. perhaps linear rules don't support binding hyps?
;;
(defun remove-bind-equiv (hyps bvars)
  (if (not (consp hyps)) (mv nil bvars)
    (mv-let (res bvars) (remove-bind-equiv (cdr hyps) bvars)
      (let ((hyp (car hyps)))
        (case-match hyp
          (('iff bvar xhyp)
           (if (symbolp bvar)
               (mv (cons xhyp res) (cons bvar bvars))
             (mv (cons hyp res) bvars)))
          (('equal bvar xhyp)
           (if (symbolp bvar)
               (mv (cons xhyp res) (cons bvar bvars))
             (mv (cons hyp res) bvars)))
          (&
           (mv (cons hyp res) bvars)))))))

(defun def-linear-fn-wrapper (name body free-hyps hints trigger-terms binder-terms rule-classes state)
  (declare (xargs :mode :program))
  (mv-let (hyps conclusion) (split-implication body)
    (let ((free-hyps (and free-hyps (and-body free-hyps))))
      (b* (((mv xhyps bvars) (remove-bind-equiv hyps nil))
           ((mv err1 xhyps       state) (translate-list xhyps (w state) state))
           ((mv err2 xfree-hyps  state) (translate-list free-hyps (w state) state))
           ((mv err3 conclusion state) (acl2::translate conclusion t t t nil (w state) state))
           (free-vars (append bvars (term-list-vars xfree-hyps)))
           (hyp-vars  (term-list-vars xhyps)))
        (mv (or err1 err2 err3)
            (def-linear-fn name free-hyps free-vars
              hyps hyp-vars conclusion hints rule-classes trigger-terms binder-terms)
            state)))))

(defmacro def::linear (name
                       body
                       &key
                       (free-hyps 'nil)
                       (hints 'nil)
                       (trigger-terms 'nil)
                       (binder-terms 'nil)
                       (rule-classes 'nil))
  `(make-event (def-linear-fn-wrapper ',name ',body ',free-hyps
                 ',hints ',trigger-terms ',binder-terms ',rule-classes state)))

(encapsulate
    (
     ((test-linear) => *)
     )

  (local
   (defun test-linear () nil))
  
  (local
   (encapsulate
       ()
     

     (defun foo (x)
       x)

     (def::linear rule
       (implies
        (and
         (syntaxp (not (cw "(< ~x0 ~x1)~%" i j)))
         (< i j))
        (< (foo i) (foo j))))

     (in-theory (disable foo (foo)))

     ;; :monitor (:linear rule . 1) '(:target :go)
     ;; :monitor (:linear rule . 2) '(:target :go)
     ;; :brr t

     (defthmd test-1
       (< (foo i) (foo (+ 1 i))))

     (defthmd test-3
       (<= (foo i) (foo (+ 1 i))))

     (defthmd test-4
       (implies
        (and
         (< i j)
         (< (foo z) (foo q))
         (equal (foo k) (foo m))
         (<= (foo j) (foo i))
         (<= (foo a) (foo b)))
        (equal (foo c) (foo d))))

     (defthmd test-5
       (implies
        (and
         (< i j)
         (< (foo z) (foo q))
         (equal (foo k) (foo m))
         (< (foo j) (foo i))
         (<= (foo a) (foo b)))
        (equal (foo c) (foo d))))

     ;; Gotta admit .. that is pretty cool ..
     (defthmd test-6
       (implies
        (< i j)
        (< (foo (foo i)) (foo (foo j)))))

     (defthmd test-7
       (< (foo (foo i)) (foo (foo (+ 1 i)))))
          
     )))

#+joe
(encapsulate
    (
     ((foo *) => *)
     ((goo * *) => *)
     )
  (local (defun hoo (x) (declare (ignore x)) -1))
  (local (defun foo (x) (abs (rfix x))))
  (local (defun goo (x y) (declare (ignore y)) (rfix x)))

  ;; The following form generates an odd-seeming ACL2 error:
  ;;
  ;; ACL2 Error in ( DEFTHM JOKER ...):  Each term in the :TRIGGER-TERMS
  ;; of a :LINEAR rule should be a legal trigger for the rule generated
  ;; for each branch through the corollary.  But the the proposed trigger
  ;; (FOO X) for the :LINEAR rule JOKER is illegal for the branch 
  ;; (IMPLIES (BIND-FREE (LINEAR-BINDER-FN 'JOKER
  ;;                                       '((GOO X Y))
  ;;                                       '(Y)
  ;;                                       MFC STATE)
  ;;                     (Y))
  ;;          (< (FOO X) (GOO X Y)))
  ;; because it contains insufficient variables.  See :DOC linear.
  ;;

  (def::linear joker
    (<= (foo x) (goo x y)))

  )
    
    
