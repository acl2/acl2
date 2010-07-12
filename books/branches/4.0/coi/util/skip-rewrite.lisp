#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(include-book "misc/beta-reduce" :dir :system)

(defun unhide (x)
  (declare (type t x))
  x)

(defthm unhide-unhidden
  (implies
   (syntaxp (or (not (consp x)) (not (equal (car x) 'hide))))
   (equal (unhide x) x)))

(defthm unhide-hide
  (equal (unhide (hide x))
         x)
  :hints (("Goal" :expand (hide x))))

(defevaluator unhide-eval unhide-eval-list
  (
   (hide x)
   (unhide x)
   )
  )

(beta-reduction-theorem unhide-eval unhide-eval-list)

(defun unhide-p (term)
  (declare (type t term))
  (and (consp term)
       (equal (car term) 'unhide)
       (consp (cdr term))
       (null (cddr term))))

(defun hide-p (term)
  (declare (type t term))
  (and (consp term)
       (equal (car term) 'hide)
       (consp (cdr term))
       (null (cddr term))))

(defun beta-reduce-hide-wrapper (term)
  (declare (type (satisfies pseudo-termp) term))
  (if (hide-p term)
      (let ((arg (cadr term)))
        (if (lambda-expr-p arg)
            `(hide ,(beta-reduce-lambda-expr arg))
          term))
    term))

(defthm *meta*-beta-reduce-hide
  (implies
   (pseudo-termp term)
   (equal (unhide-eval term a)
          (unhide-eval (beta-reduce-hide-wrapper term) a)))
  :hints (("Goal" :expand (:Free (x) (hide x))))
  :rule-classes ((:meta :trigger-fns (hide))))


(defun unhide-hide-wrapper (term)
  (declare (type (satisfies pseudo-termp) term))
  (if (unhide-p term)
      (let ((arg (cadr term)))
        (if (hide-p arg)
            (let ((arg (cadr arg)))
              (if (lambda-expr-p arg)
                  `(unhide (hide ,(beta-reduce-lambda-expr arg)))
                term))
          term))
    term))

(defthm *meta*-unhide-hide
  (implies
   (pseudo-termp term)
   (equal (unhide-eval term a)
          (unhide-eval (unhide-hide-wrapper term) a)))
  :hints (("Goal" :expand (:Free (x) (hide x))))
  :rule-classes ((:meta :trigger-fns (unhide))))

(in-theory (disable unhide))

(defmacro skip-rewrite (x)
  `(unhide (hide ,x)))

(in-theory (disable unhide))

(local
(encapsulate
    ()

  ;; You can see these rules "doing their job" if you
  ;; watch this proof (and monitor unhide-hide-wrapper)

  (defun foo (x) (if (zp x) 2 (foo (1- x))))
  
  (defthm open-foo
    (implies
     (and
      (not (zp x))
      (equal v (1- x)))
     (equal (foo x) (skip-rewrite (foo v)))))
  
  (defthm foo-0
    (equal (foo 0) 2))
  
  (in-theory (disable foo (foo)))
  
  ;;(trace$ unhide-hide-wrapper)
  
  (defthm foo-10
    (equal (foo 10) 2))

  ))
