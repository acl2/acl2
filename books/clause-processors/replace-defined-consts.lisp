
(in-package "ACL2")


;; This book defines a computed hint REPLACE-DEFINED-CONSTS-HINT which looks in
;; the current clause for defined constants (see tools/defined-const.lisp) and
;; replaces them with their definitions (the ground terms which reduced to
;; those constants.)  It is important to turn off the executable-counterparts
;; of at least some functions in these definitions or no progress will be made.

(include-book "use-by-hint")
(include-book "multi-env-trick")
(include-book "std/util/bstar" :dir :system)
(include-book "tools/flag" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(include-book "clause-processors/join-thms" :dir :system)

(defevaluator replace-const-ev replace-const-ev-lst
  ((equal a b) (if a b c) (use-by-hint x) (not x)))

(def-join-thms replace-const-ev)


;; The alist here has key/val pairs of the form (value term . thmname), where
;; term is a ground term and thmname is the name of a theorem that states
;; (equal term value).
(mutual-recursion
 (defun replace-const-term (x alist thms clk)
   (declare (xargs :measure (make-ord 1 (1+ (nfix clk)) (acl2-count x))))
   (cond ((zp clk) (mv x thms))
         ((atom x) (mv x thms))
         ((eq (car x) 'quote)
          (let ((p (hons-assoc-equal (cadr x) alist)))
            (if p
                (replace-const-term (cadr p) alist
                                    (cons `((not (use-by-hint ',(cddr p)))
                                            (equal ,(cadr p) ,x))
                                          thms)
                                    (1- clk))
              (mv x thms))))
         ((consp (car x))
          (b* (((mv body thms)
                (replace-const-term (caddar x) alist thms clk))
               ((mv args thms)
                (replace-const-list (cdr x) alist thms clk)))
            (mv `((lambda ,(cadar x) ,body) . ,args)
                thms)))
         (t (b* (((mv args thms)
                  (replace-const-list (cdr x) alist thms clk)))
              (mv (cons (car x) args) thms)))))
 (defun replace-const-list (x alist thms clk)
   (declare (xargs :measure (make-ord 1 (1+ (nfix clk)) (acl2-count x))))
   (if (atom x)
       (mv x thms)
     (b* (((mv car thms) (replace-const-term (car x) alist thms clk))
          ((mv cdr thms) (replace-const-list (cdr x) alist thms clk)))
       (mv (cons car cdr) thms)))))


(mutual-recursion
 (defun replace-const-alists-term (x alist thms al als clk)
   (declare (xargs :measure (make-ord 1 (1+ (nfix clk)) (acl2-count x)))
            (ignorable alist thms))
   (cond ((zp clk) als)
         ((atom x) als)
         ((eq (car x) 'quote)
          (let ((p (hons-assoc-equal (cadr x) alist)))
            (if p
                (replace-const-alists-term
                 (cadr p) alist
                 (cons `((not (use-by-hint ',(cddr p)))
                         (equal ,(cadr p) ,x))
                       thms)
                 al (cons (list al) als) (1- clk))
              als)))
         ((consp (car x))
          (b* (((mv & thms1)
                (replace-const-term (caddar x) alist thms clk))
               (als (replace-const-alists-term
                           (caddar x) alist thms
                           (pairlis$ (cadar x)
                                     (replace-const-ev-lst (cdr x) al))
                           als clk)))
            (replace-const-alists-list (cdr x) alist thms1 al als clk)))
         (t (replace-const-alists-list (cdr x) alist thms al als clk))))
 (defun replace-const-alists-list (x alist thms al als clk)
   (declare (xargs :measure (make-ord 1 (1+ (nfix clk)) (acl2-count x)))
            (ignorable alist thms))
   (if (atom x)
       als
     (b* (((mv & thms1) (replace-const-term (car x) alist thms clk))
          (als (replace-const-alists-term (car x) alist thms al als clk)))
       (replace-const-alists-list (cdr x) alist thms1 al als clk)))))

(set-irrelevant-formals-ok t)
(flag::make-flag replace-const-alists-flag replace-const-alists-term)

(def-multi-env-fns replace-const-ev replace-const-ev-lst)


(defthm-replace-const-alists-flag
  replace-const-extends-thms
  (replace-const-alists-term
   (implies (clauses-apply-alists-replace-const-ev
             (mv-nth 1 (replace-const-term x alist thms clk))
             (replace-const-alists-term x alist thms al als clk))
            (clauses-apply-alists-replace-const-ev thms als)))
  (replace-const-alists-list
   (implies (clauses-apply-alists-replace-const-ev
             (mv-nth 1 (replace-const-list x alist thms clk))
             (replace-const-alists-list x alist thms al als clk))
            (clauses-apply-alists-replace-const-ev thms als)))
  :hints (("goal" :induct (replace-const-alists-flag flag x alist thms al als clk)
           :in-theory (enable conjoin-clauses))))

(defthm-replace-const-alists-flag
  replace-const-corr
  (replace-const-alists-term
   (mv-let (newx newthms)
     (replace-const-term x alist thms clk)
     (implies (clauses-apply-alists-replace-const-ev
               newthms (replace-const-alists-term x alist thms al als clk))
              (equal (replace-const-ev newx al)
                     (replace-const-ev x al)))))
  (replace-const-alists-list
   (mv-let (newx newthms)
     (replace-const-list x alist thms clk)
     (implies (clauses-apply-alists-replace-const-ev
               newthms (replace-const-alists-list x alist thms al als clk))
              (equal (replace-const-ev-lst newx al)
                     (replace-const-ev-lst x al)))))
  :hints (("goal" :induct (replace-const-alists-flag flag x alist thms al als clk))
          ("Subgoal *1/5" :in-theory (enable replace-const-ev-constraint-0))
          ("Subgoal *1/2"
           :use ((:instance
                  replace-const-extends-thms-replace-const-alists-term
                  (x (cadr (hons-assoc-equal (cadr x) alist)))
                  (thms (cons `((not (use-by-hint ',(cddr (hons-assoc-equal
                                                           (cadr x) alist))))
                                (equal ,(cadr (hons-assoc-equal (cadr x)
                                                                alist))
                                       ,x))
                              thms))
                  (als (cons (list al) als)) (clk (1- clk))))
           :in-theory (e/d (use-by-hint)
                           (replace-const-extends-thms-replace-const-alists-term)))))

(in-theory (disable replace-const-term replace-const-list
                    replace-const-alists-term
                    replace-const-alists-list))

(defthm replace-const-ev-disjoin-is-or-list-replace-const-ev-lst
  (iff (replace-const-ev (disjoin lst) al)
       (or-list (replace-const-ev-lst lst al)))
  :hints (("goal" :in-theory (enable (:induction disjoin)))))

(defun replace-consts-cp (clause alist)
  (mv-let (clause thms)
    (replace-const-list clause alist nil 10)
    (cons clause thms)))

(defun replace-consts-cp-alists (clause alist al)
  (cons (list al) (replace-const-alists-list clause alist nil al nil 10)))

(defthm replace-consts-cp-correct1
  (implies (clauses-apply-alists-replace-const-ev
            (replace-consts-cp clause alist)
            (replace-consts-cp-alists clause alist al))
           (replace-const-ev (disjoin clause) al)))

(in-theory (disable replace-consts-cp replace-consts-cp-alists
                    replace-const-ev-disjoin-is-or-list-replace-const-ev-lst))

(prove-multi-env-clause-proc
 replace-consts-cp-correct
 :ev replace-const-ev
 :evlst replace-const-ev-lst
 :clauseproc replace-consts-cp
 :alists (replace-consts-cp-alists clause alist al)
 :alist-name al)

(defun replace-consts-alist1 (table world omit)
  (if (atom table)
      nil
    (if (member-eq (caar table) omit)
        (replace-consts-alist1 (cdr table) world omit)
      (let* ((thmname (cdar table))
             (thm (getprop thmname 'theorem nil 'current-acl2-world world))
             (term (cadr thm))
             (val (cadr (caddr thm))))
        (cons (list* val term thmname)
              (replace-consts-alist1 (cdr table) world omit))))))

(defun replace-consts-alist (world omit)
  (replace-consts-alist1 (table-alist 'defined-const-table world) world omit))

(defun replace-defined-consts-hint-fn (world omit)
  `(:computed-hint-replacement
    ((use-by-computed-hint clause))
    :clause-processor
    (replace-consts-cp clause
                       ',(replace-consts-alist world omit))))

(defmacro replace-defined-consts-hint (&optional omit)
  `(replace-defined-consts-hint-fn world ,omit))





#|
Test.


(defun mklist (n)
  (if (zp n)
      nil
    (cons n (mklist (1- n)))))

(include-book ;; keep the rest on the line below for dependencies
 "tools/defined-const" :dir :system)

(defined-const *foo* (mklist 8))

(in-theory nil)

;; Fails:
(thm (equal *foo* (mklist 8)))

;; Succeeds:
(thm (equal *foo* (mklist 8))
     :hints ((replace-defined-consts-hint)))


||#

