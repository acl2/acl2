(in-package "DEFUN")

(include-book "mv-nth")
(include-book "defun-support")
(include-book "../symbol-fns/symbol-fns")

(defun syn-truep (x)
  (declare (type t x))
  (and (consp x)
       (equal (car x) 'quote)
       (consp (cdr x))
       (not (equal (cadr x) 'nil))))

(defun syn-true () 
  (declare (xargs :guard t))
  acl2::*t*)

(defun syn-falsep (x)
  (declare (type t x))
  (or (null x)
      (and (consp x)
	   (equal (car x) 'quote)
	   (consp (cdr x))
	   (equal (cadr x) 'nil))))

(defun syn-false ()
  (declare (xargs :guard t))
   acl2::*nil*)

(defun syn-if (x y z)
  (declare (type t x y z))
  `(if ,x ,y ,z))

(defun syn-lazy-if (x y z)
  (declare (type t x y))
  (cond
   ((syn-falsep x) z)
   ((syn-truep x)  y)
   (t 
    (syn-if x y z))))

(defun syn-not (x)
  (declare (type t x ))
  (cond
   ((syn-falsep x) (syn-true))
   ((syn-truep x)  (syn-false))
   ((and (consp x)
         (consp (cdr x))
         (equal (car x) 'not))
    (cadr x))
   (t `(not ,x))))

(defun syn-lazy-ite (x y z)
  (cond
   ((syn-falsep x) z)
   ((syn-truep x) y)
   ((equal y z)
    y)
   ((and (syn-falsep y)
	 (syn-truep z))
    (syn-not x))
   ((and (syn-truep y)
	 (syn-falsep z))
    (syn-not x))
   (t
    (syn-if x y z))))

(defun syn-conjoin (x y)
  (declare (type t x y))
  (cond
   ((syn-falsep x)
    (syn-false))
   ((syn-falsep y)
    (syn-false))
   ((syn-truep y)
    x)
   ((syn-truep x)
    y)
   (t
    (syn-if x y (syn-false)))))

(defun syn-and-fn (args)
  (declare (type t args))
  (if (consp args)
      `(syn-conjoin ,(car args) ,(syn-and-fn (cdr args)))
    `(syn-true)))

(defmacro syn-and (&rest args)
  (syn-and-fn args))

(defun syn-quote (v)
  `(quote ,v))

;; We are looking for "distinguishing if's" .. if expressions that
;; separate recursive calls from non-recursive calls.  The
;; form that we return looks like an if-then-else expression ..

(defun base-value (term)
  (mv (syn-true) term (syn-quote :ignore)))

(defun rec-value (term)
  (mv (syn-false) (syn-quote :ignore) term))

(mutual-recursion

 (defun lift-base-fn (flist term vars)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((not (consp term)) (mv (cdr (assoc term vars)) term))
    ((acl2::lambda-expr-p term)
     (met ((vars args) (lift-base-vars flist (lambda-formals term) (cdr term) vars))
       (met ((base body) (lift-base-fn flist (lambda-body term) vars))
	 (if (syn-falsep base) (mv (syn-false) :ignore)
	   (mv (make-lambda-application (strip-cars vars) base args)
	       (make-lambda-application (strip-cars vars) body args))))))
    ((equal (car term) 'quote) (mv (syn-true) term))
    ((member (car term) flist) (mv (syn-false) :ignore))
    ((equal (car term) 'if)
     (met ((bcase case) (lift-base-fn flist (cadr term) vars))
          (met ((bthen then) (lift-base-fn flist (caddr term) vars))
               (met ((belse else) (lift-base-fn flist (cadddr term) vars))
                    (cond
                     ((or (syn-falsep bcase) (and (syn-falsep bthen) (syn-falsep belse)))
                      (mv (syn-false) :ignore))
                     ((and (not (syn-falsep bthen)) (not (syn-falsep belse)))
                      (mv (syn-lazy-ite case (syn-and bcase bthen) (syn-and bcase belse))
                          (syn-lazy-if case then else)))
                     ((not (syn-falsep bthen))
                      (mv (syn-and bcase case bthen) then))
                     (t ; belse
                      (mv (syn-and bcase (syn-not case) belse) else)))))))
    
    (t
     (met ((base args) (lift-base-args flist (cdr term) vars))
          (if (syn-falsep base) (mv (syn-false) :ignore)
	    (mv base `(,(car term) ,@args)))))))
     
 (defun lift-base-args (flist args vars)
   (declare (xargs :measure (acl2-count args)))
   (if (consp args)
       (met ((tbase term) (lift-base-fn flist (car args) vars))
            (met ((abase args) (lift-base-args flist (cdr args) vars))
                 (mv (syn-and tbase abase) (cons term args))))
     (mv (syn-true) nil)))

 (defun lift-base-vars (flist vars args v0)
   (declare (xargs :measure (acl2-count args)))
   (if (consp args)
       (met ((tbase term) (lift-base-fn flist (car args) v0))
	 (let ((var (car vars)))
	   (met ((vars args) (lift-base-vars flist (cdr vars) (cdr args) v0))
	     (mv (cons (cons var tbase) vars) (cons term args)))))
     (mv nil nil)))

 )

(defun pair-args-with-true (args)
  (if (consp args)
      (cons (cons (car args) (syn-true))
            (pair-args-with-true (cdr args)))
    nil))

(defun lift-base (flist body args)
  (let ((vars (pair-args-with-true args)))
    (met ((case base) (lift-base-fn flist body vars))
      (let ((case (syn-not case)))
        (let ((case (or case (syn-false))))
          (mv case base))))))

(defun lift-recursion-guard (flist body args)
  (met ((case base) (lift-base flist body args))
    (syn-lazy-if case body base)))

;; duplo is intended to assist in defining induction schema for use in
;; congruence proofs.  

(mutual-recursion

 (defun duplo (flist valist term)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((atom term)
     (let ((nterm (cdr (assoc term valist))))
       (mv term nterm)))
    ((acl2::quotep term)
     (mv term term))
    ((member (car term) flist)
     (met ((args nargs) (duplo-args flist valist (cdr term)))
       (mv `(val 0 (,(car term) ,@args ,@nargs))
	   `(val 1 (,(car term) ,@args ,@nargs)))))
    ;; I think this must duplicate both argument lists ..
    ((acl2::lambda-expr-p term)
     (met ((args nargs) (duplo-args flist valist (lambda-args term)))
       (met ((vars nvars) (duplo-args flist valist (lambda-formals term)))
	 (met ((body nbody) (duplo flist valist (lambda-body term)))
	   (mv (make-lambda-application (append vars nvars) body  (append args nargs))
	       (make-lambda-application (append vars nvars) nbody (append args nargs)))))))
    (t
     (met ((args nargs) (duplo-args flist valist (cdr term)))
       (mv `(,(car term) ,@args)
	   `(,(car term) ,@nargs))))))

 (defun duplo-args (flist valist args)
   (declare (xargs :measure (acl2-count args)))
   (if (consp args)
       (met ((oargs nargs) (duplo-args flist valist (cdr args)))
	 (met ((term nterm) (duplo flist valist (car args)))
	   (mv (cons term oargs) (cons nterm nargs))))
     (mv nil nil)))
 
 )

(defun value-pair (x y)
  (list x y))

(defthm val-value-pair
  (and (equal (acl2::val 0 (value-pair x y))
	      x)
       (equal (acl2::val 1 (value-pair x y))
	      y)))

(defun duplo-spine (flist valist term)
  (cond
   ((atom term)
    (let ((nterm (cdr (assoc term valist))))
      `(value-pair ,term ,nterm)))
   ((acl2::quotep term)
    `(value-pair ,term ,term))
   ((member (car term) flist)
    (met ((args nargs) (duplo-args flist valist (cdr term)))
      `(,(car term) ,@args ,@nargs)))
   ((acl2::lambda-expr-p term)
    (met ((args nargs) (duplo-args flist valist (lambda-args term)))
      (met ((vars nvars) (duplo-args flist valist (lambda-formals term)))
	(let ((nbody (duplo-spine flist valist (lambda-body term))))
	  (make-lambda-application (append vars nvars) nbody (append args nargs))))))
   (t
    (met ((args nargs) (duplo-args flist valist (cdr term)))
      `(value-pair (,(car term) ,@args)
		   (,(car term) ,@nargs))))))

(mutual-recursion

 (defun term-vars (term res)
   (cond
    ((atom term)
     (if (member term res) res
       (cons term res)))
    ((acl2::quotep term)
     res)
    ((acl2::lambda-expr-p term)
     (let ((res (term-vars-args (lambda-args term) res)))
       (let ((res (term-vars-args (lambda-formals term) res)))
	 (term-vars (lambda-body term) res))))
    (t
     (term-vars-args (cdr term) res))))

 (defun term-vars-args (args res)
   (if (endp args) res
     (let ((res (term-vars (car args) res)))
       (term-vars-args (cdr args) res))))
 
 )

(mutual-recursion

 (defun term-var-sub (term valist)
   (cond
    ((atom term)
     (cdr (assoc term valist)))
    ((acl2::quotep term)
     term)
    ((acl2::lambda-expr-p term)
     (let ((args (term-var-sub-args (lambda-args term) valist)))
       (let ((formals (term-var-sub-args (lambda-formals term) valist)))
	 (let ((body (term-var-sub (lambda-body term) valist)))
	   (defun::make-lambda-application formals body args)))))
    (t
     (cons (car term) (term-var-sub-args (cdr term) valist)))))

 (defun term-var-sub-args (args valist)
   (if (endp args) nil
     (cons (term-var-sub (car args) valist)
	   (term-var-sub-args (cdr args) valist))))
 
 )

;; So .. we need gensym in order to do this well.  Perhaps we can get
;; away with some sort of cheat.  Sigh.  And at what point do we
;; finally just refactor our libraries?

(defun var-alist-rec (prefix vars omit res)
  (declare (ignorable omit))
  (if (endp vars) res
    (let ((res (acons (car vars) (symbol-fns::prefix prefix (car vars)) res)))
      (var-alist-rec prefix (cdr vars) omit res))))

(defun var-alist (prefix vars)
  (var-alist-rec prefix vars vars nil))

(defun duplicate-defun (prefix flist defun)
  (let ((body (defun-body defun)))
    (met ((doc decls body) (decompose-defun-body body))
      (let ((args (defun-args defun)))
	(let ((vars (term-vars body args)))
	  (let ((valist (var-alist prefix vars)))
	    (met ((c1 b1) (lift-base flist body args))
	      (declare (ignore b1))
	      (let ((b1 `(,(defun-name defun) ,@(defun-args defun))))
		(let ((c2 (term-var-sub c1 valist))
		      (b2 (term-var-sub b1 valist))
		      (xargs (term-var-sub-args args valist)))
		  (let ((cond (syn-not (syn-and c1 c2))))
		    (let ((base `(value-pair ,b1 ,b2)))
		      (let ((body (duplo-spine flist valist body)))
			(let ((body (syn-lazy-if cond base body)))
			  (make-defun (defun-type defun) (defun-name defun) (append (defun-args defun) xargs)
				      (make-defun-body doc decls body)))))))))))))))

(defun congruence-induction-function (defun)
  (let ((body (defun-body defun))
	(fn   (defun-name defun)))
    (met ((doc decls body) (decompose-defun-body body))
      (let ((measure (get-xarg-keys-from-decls :measure decls)))
	(let ((measure (and measure `((declare (xargs :measure ,@measure))))))
	  (let ((fn-induction (symbol-fns::suffix fn '-induction)))
	    (let ((body (replace-function-names `(,fn) '-induction body)))
	      (let ((defun (update-defun defun :body (make-defun-body doc measure body))))
		(let ((defun (duplicate-defun 'equiv- `(,fn-induction) defun)))
		  (let ((defun (update-defun defun :type 'defun :name fn-induction)))
		    defun))))))))))

(defun prefix-list (prefix list)
  (declare (type (satisfies symbol-listp) list)
	   (type symbol prefix))
  (if (consp list)
      (cons (symbol-fns::prefix (car list) prefix)
	    (prefix-list prefix (cdr list)))
    nil))

(defun congruence-induction-reduction-proof (fn-induction fn args)
  (declare (type (satisfies symbol-listp) args)
	   (type symbol fn-induction))
  (let* ((xargs        (prefix-list 'equiv- args))
	 (fn-induction-to-fn (symbol-fns::suffix fn-induction '-to- fn)))
    `(defthm ,fn-induction-to-fn
       (and (equal (acl2::val 0 (,fn-induction ,@args ,@xargs))
		   (,fn ,@args))
	    (equal (acl2::val 1 (,fn-induction ,@args ,@xargs))
		   (,fn ,@xargs)))
       :hints (("Goal" :in-theory '((:rewrite val-value-pair)
				    (:induction ,fn-induction)
				    (:definition ,fn-induction)
				    (:definition ,fn))
		:induct (,fn-induction ,@args ,@xargs))
	       (and acl2::stable-under-simplificationp
		    '(:in-theory (current-theory :here)))))))
