(in-package "ACL2")

; Original author: David Rager <ragerdl@cs.utexas.edu>

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

(defun fix-args-order-and-remove-keys (non-keyed-args keyed-args body)

; Fix the argument order for the current level of function call -- not for any
; recursive calls contained within the body.  Those recursive calls will be
; fixed in the function that calls this one.

  (declare (xargs :measure (+ (acl2-count non-keyed-args)
                              (acl2-count keyed-args))))
  (cond ((consp non-keyed-args)
         (cons (car body)
               (fix-args-order-and-remove-keys (cdr non-keyed-args)
                                               keyed-args
                                               (cdr body))))
        ((consp keyed-args)
         (let* ((keyword (car keyed-args))
                (keyword-value (cadr (member-equal
                                      (intern (symbol-name keyword) "KEYWORD")
                                      body))))
           (cons keyword-value
                 (fix-args-order-and-remove-keys non-keyed-args ; is nil
                                                 (cdr keyed-args)
                                                 body))))
        (t nil)))

(mutual-recursion
 (defun fix-defkun-recursive-call-args (original-name fname non-keyed-args keyed-args body)
   (declare (xargs :mode :program))
   (if (atom body)
       body
     (cons (fix-defkun-recursive-call original-name fname non-keyed-args keyed-args (car body))
           (fix-defkun-recursive-call-args original-name fname non-keyed-args keyed-args
                                           (cdr body)))))

 (defun fix-defkun-recursive-call (original-name fname non-keyed-args keyed-args body)
   (declare (xargs :mode :program))
   (cond ((atom body)
          body)
         ((equal (car body) original-name)
          (let ((body (fix-args-order-and-remove-keys non-keyed-args
                                                      keyed-args
                                                      (cdr body))))
            (cons fname
                  (fix-defkun-recursive-call-args original-name
                                                  fname
                                                  non-keyed-args
                                                  keyed-args
; We do not need to take the cdr of body because fix-args-order-and-remove-keys
; did that for us.
                                                  body))))
         (t (cons (car body)
                  (fix-defkun-recursive-call-args original-name
                                                  fname
                                                  non-keyed-args
                                                  keyed-args
                                                  (cdr body))))))
 )

(defmacro defkun (name args body)

; The use of this macro defines a macro and function pair that allow a
; programming style of passing keyword arguments to function calls.

; Defkun works for recursive functions, but if you forget to use the :keyword
; to specify a particular keyword's value in the recursive call, the function
; might still admit, even though you've really made a mistake.  I think the
; behavior is such that the keyword's value is nil.  You can issue a :trans1 of
; your defkun'd function to see the technical details behind this.

  (mv-let (non-keyed-args keyed-args)
    (parse-keyed-arguments args)
    (let* ((fname (packn (list name "-fn")))
           (args-list (append non-keyed-args keyed-args))
           (new-body (fix-defkun-recursive-call name
                                                fname
                                                non-keyed-args
                                                keyed-args
                                                body))
           )
      `(progn
         (defun ,fname ,(append non-keyed-args keyed-args)
           ,new-body)
         (defmacro ,name ,args
           (list (quote ,fname) ,@args-list))
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

; "Obviously" the following two definitions will not admit unless you define
; the subfunctions

(defkun make-declare-assocs (&key vars kind type)
  (if (atom vars)
      nil
    (let* ((key (car vars)))
      (cons (cond ((equal kind 'ignore)
                   (make declare-assoc :key key :ignore t))
                  ((equal kind 'ignorable)
                   (make declare-assoc :key key :ignorable t))
                  ((equal kind 'type)
                   (make declare-assoc :key key :type type))
                  (t (assert$ nil "Problem with make-declare-assocs arg")))
            (make-declare-assocs :kind kind :vars (cdr vars) :type type)))))

(defkun top-level-mv-bindings (mvs alist &key futurize)
  (if (endp mvs)
      nil
    (let* ((key (caar mvs))
           (obscure-varname
            (access mv-assoc (key-equal key alist) :value))
           (computation (cadar mvs)))
      (cons (if futurize
                (list obscure-varname `(future (mv-list ,(length key) ,computation)))
              (list obscure-varname `(mv-list ,(length key) ,computation)))
            (top-level-mv-bindings (cdr mvs) alist :futurize futurize)))))
|#
