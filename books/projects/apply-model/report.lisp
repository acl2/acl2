; This file contains the events mentioned in the Examples section of the paper
; ``Limited Second Order Functionality in a First Order Setting''

; It currently resides in /u/moore/Desktop/toy7/report.lisp but ultimately
; belongs in the distributed apply books.

(in-package "MODAPP")

(include-book "apply")

(defun$ square (x) (* x x))

(defun$ cube (x) (* x (square x)))

(defun$ nats (n)
  (if (zp n)
      nil
      (cons n (nats (- n 1)))))

(defun$ rev (x)
  (if (endp x)
      nil
      (append (rev (cdr x)) (list (car x)))))

(defun$ flatten (x)
  (if (atom x)
      (list x)
      (append (flatten (car x))
              (flatten (cdr x)))))

(defun$ sum (fn lst)
  (cond ((endp lst) 0)
        (t (+ (apply$ fn (list (car lst)))
              (sum fn (cdr lst))))))

(defun$ filter (fn lst)
  (cond ((endp lst) nil)
        ((apply$ fn (list (car lst)))
         (cons (car lst) (filter fn (cdr lst))))
        (t (filter fn (cdr lst)))))

(defun$ foldr (lst fn init)
  (if (endp lst)
      init
      (apply$ fn
              (list (car lst)
                    (foldr (cdr lst) fn init)))))

(defun$ foldt (x fn init)
  (if (atom x)
      (apply$ fn (list x init))
      (apply$ fn (list x (foldt (car x) fn (foldt (cdr x) fn init))))))


(defun$ sum-squares (lst)
  (if (endp lst)
      0
      (+ (square (car lst))
         (sum-squares (cdr lst)))))

(defthm T1
  (implies (warrant square)
           (equal (sum-squares lst)
                  (sum 'square lst))))

(defthm T2
  (equal (sum fn (append a b))
         (+ (sum fn a) (sum fn b))))

(encapsulate nil
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm T3
    (implies (and (warrant square)
                  (natp n))
             (equal (sum 'SQUARE (nats n))
                    (/ (* n (+ n 1) (+ (* 2 n) 1))
                       6)))
    :hints (("Goal" :expand ((:free (x) (HIDE x)))))))

(defun$ sum-squares-of-evens (lst)
  (if (endp lst)
      0
      (if (evenp (car lst))
          (+ (square (car lst))
             (sum-squares-of-evens (cdr lst)))
          (sum-squares-of-evens (cdr lst)))))

(defthm T4
  (implies (warrant square)
           (equal (sum-squares-of-evens lst)
                  (sum 'square (filter 'evenp lst)))))

(defthm T5
  (equal (filter fn (append a b))
         (append (filter fn a) (filter fn b))))

(defthm T6
  (implies (warrant square)
           (equal (foldr lst
                         '(lambda (i a)
                            (if (evenp i)
                                (binary-+ (square i) a) ; <--- Discrepancy
                                a))
                         0)
                  (sum 'square (filter 'evenp lst)))))

(defthm T7
  (equal (foldr x 'cons y)
         (append x y)))

(defthm T8
  (implies (warrant foldr)
           (equal (foldr x
                         '(LAMBDA (X Y)
                                  (FOLDR Y 'CONS (CONS X 'NIL)))
                         nil)
                  (rev x))))

(defun$ ok-fnp (fn)
  (and (not (equal fn 'QUOTE))
       (not (equal fn 'IF))
       (tamep `(,fn X))))

(defthm T9
  (implies (ok-fnp fn)
           (equal (foldr lst `(lambda (x y) (binary-+ (,fn x) y)) 0) ; <--- Discrepancy
                  (sum fn lst))))

(defthm T10
  (implies (ok-fnp fn)
           (equal (foldr lst `(lambda (x y) (if (,fn x) (cons x y) y)) nil)
                  (filter fn lst))))

(defthm T11-lemma
  (implies (and (ok-fnp fn)
                (ok-fnp gn)
                (acl2-numberp init))
           (equal (foldr lst `(lambda (x y) (if (,fn x) (binary-+ (,gn x) y) y)) init)
                  (+ init (sum gn (filter fn lst))))))

(defthm T11
  (implies (and (ok-fnp fn)
                (ok-fnp gn))
           (equal (foldr lst `(lambda (x y) (if (,fn x) (binary-+ (,gn x) y) y)) 0)
                  (sum gn (filter fn lst)))))

(defthm T12-lemma
  (equal (foldt x '(lambda (x y)
                     (if (consp x)
                         y
                         (cons x y)))
                z)
         (append (flatten x) z)))

(defthm T12
  (equal (foldt x  '(lambda (x y)
                      (if (consp x)
                          y
                          (cons x y))) nil)
         (flatten x)))

(defun$ russell (fn x)
  (not (apply$ fn (list x x))))

(defthm T13
  (equal (russell 'equal 'equal) nil)
  :hints (("Goal" :expand ((:free (x) (hide x)))))
  :rule-classes nil)

; One might hope we could derive something about (russell 'russell 'russell),
; but nothing interesting can be proved about it.  Suppose we have the warrant
; for russell and consider (russell 'russell 'russell).  By the definitional
; equation for russell, this is equal to

; (not (apply$ 'russell '(russell russell)))

; The definition of apply$ reduces this to

; (not (apply$-userfn 'russell '(russell russell)))

; Only potential next step is to use the warrant.  But that just tells us the
; badge for russell and the fact:

;   (tamep-functionp (car args))
;  --> 
;   (apply$-userfn 'russell args) = (russell (car args) (cadr args))

; So to use the warrant we must prove (tamep-functionp (car '(russell
; russell))) which is (tamep-functionp 'russell) which is NIL.  Thus the
; warrant tells us nothing about this apply$-userfn and we can do no more.
