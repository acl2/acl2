(in-package "ACL2")

(defun parse-keyed-arguments (args)
  (cond ((atom args)
         (mv nil nil))
        ((equal (car args) '&key)
         (mv nil (cdr args)))
        (t (mv-let (non-keyed keyed)
             (parse-keyed-arguments (cdr args))
             (mv (cons (car args)
                       non-keyed)
                 keyed)))))

(defmacro defkun (name args body)

; The use of this macro defines a macro and function pair that allow a
; programming style of passing keyword arguments to function calls.

  (mv-let (non-keyed-args keyed-args)
    (parse-keyed-arguments args)
    (let* ((fname (packn (list name "-fn")))
           (args-list (append non-keyed-args keyed-args)))
      `(progn 
         (defun ,fname ,(append non-keyed-args keyed-args) 
           ,(subst name fname body))
         (defmacro ,name ,args 
           (list (quote ,fname)  ,@args-list))
         (add-macro-alias ,name ,fname)))))

#|
; Example forms:

(defkun food (x &key y) (+ x y))

(food 3 :y 4)
; ==>
; 7

(|FOOD-fn| 3 4)
; ==>
; 7

(defkun food (x y) (+ x y))
(defkun food (&key x y) (+ x y))

|#
