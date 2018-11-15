(in-package "ACL2")

;; ===================================================================
;;
;; Trying to use tau in an extended metafunction context
;;
;; ===================================================================

;; ===================================================================
;;
;; Functions to try to call into tau
;;
;; ===================================================================

;; We use this to compute a tau-alist from a list of triples.
;; Modified from (tau-clause1p triples tau-alist type-alist pot-lst ens wrld calist) in tau.lisp
(defun tau-alist-rec (triples tau-alist type-alist pot-lst ens wrld calist)
  (declare (xargs :mode :program))
  (cond
   ((endp triples) (mv tau-alist calist))
   (t (mv-let
       (contradictionp mbt mbf tau-alist calist)
       (tau-assume nil (caddr (car triples))
                   tau-alist type-alist pot-lst
                   ens wrld calist)
       (declare (ignore contradictionp mbf mbt))
       (tau-alist-rec (cdr triples) tau-alist type-alist pot-lst ens wrld calist)))))

;; We use this to compute a tau-alist from a clause.
;; Modified from (tau-clausep clause ens wrld state calist) in prove.lisp:
(defun tau-alist (clause type-alist pot-lst ens wrld)
  (declare (xargs :mode :program))
  (let ((triples (merge-sort-car-<
                  (annotate-clause-with-key-numbers clause
                                                    (len clause)
                                                    0 wrld))))
    (tau-alist-rec triples nil type-alist pot-lst ens wrld nil)))

;; A program mode function that returns the decoded tau of term 
(defun get-term-tau-program (term mfc ens wrld)
  (declare (xargs :mode :program))
  (let ((type-alist (mfc-type-alist mfc))
        (pot-lst    (access metafunction-context mfc :simplify-clause-pot-lst))
        (clause     (access rewrite-constant
                            (access metafunction-context mfc :rcnst)
                            :current-clause))
        )
    (mv-let (tau-alist calist) (tau-alist clause type-alist pot-lst ens wrld)
      (mv-let (tau calist) (tau-term term tau-alist type-alist pot-lst ens wrld calist)
        (declare (ignore calist))
        (decode-tau tau term)))))

(set-state-ok t)

;; We use this to jump the :logic / :program divide
(defun get-term-tau (term mfc state)
  (let ((ens        (f-get-global 'global-enabled-structure state))
        (wrld       (w state)))
    ;; I'm probably not doing this right ..
    (mv-let (hit res) (magic-ev-fncall 'get-term-tau-program `(,term ,mfc ,ens ,wrld) state t nil)
      (declare (ignore hit))
      res)))

;; ===================================================================
;;
;; A simple logical theory with a tau-like rule ..
;;
;; ===================================================================

(defun foo (x)
  (ifix x))

(defthm foo-signature
  (implies
   (natp x)
   (natp (foo x)))
  :rule-classes (:type-prescription))

(in-theory (disable foo))

(defstub pred (x) nil)

;; ===================================================================
;;
;; A drop dead simple extended meta-function that tries to compute
;; the tau of the given trigger term ..
;;
;; ===================================================================

(defevaluator tau-eval tau-eval-list
  (
   (foo x)
   (hide x)
   ))

(set-irrelevant-formals-ok t)

(defun mf-tau (term mfc state)
  (let ((zed (cw "computed tau : ~x0~%" (get-term-tau term mfc state))))
    (declare (ignore zed))
    `(hide ,term)))

(defun mf-tau-hyp (term mfc state)
  (declare (ignore term mfc state))
  *t*)

(defthm *meta*-mf-compute-tau
  (implies (and (pseudo-termp x)
                (alistp a)
                (tau-eval (mf-tau-hyp x mfc state) a) 
                )
           (equal (tau-eval x a)
                  (tau-eval (mf-tau x mfc state) a)))
  :hints (("Goal" :expand (:Free (x) (hide x))))
  :rule-classes ((:meta :trigger-fns (foo))))

;; ===================================================================
;;
;; We can watch all the action take place with the following (thm ..)
;;
;; ===================================================================

(trace$ mf-tau)

(thm 
 (implies
  (and
   (natp x)
   (pred (foo x)))
  (< 3 (foo x))))

