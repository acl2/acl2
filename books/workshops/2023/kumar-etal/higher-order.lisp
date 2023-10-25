#|$ACL2s-Preamble$;
(begin-book t :ttags :all);$ACL2s-Preamble$|#

#|

This is a preliminary version of a project to add
simple "higher-order" capabilities to ACL2.

This is done with the use of macros. My focus is on adding
support for common types of idioms, all without any extensions to
ACL2.

This file contains a subset of the current version of
higher-order.lisp.

|#

(in-package "ACL2S")

(include-book "std/strings/pretty" :dir :system)

(defun to-string (l)
  (if (endp l)
      ()
    (cons (str::pretty
           (car l)
           :config
           (str::make-printconfig
            :flat-right-margin 100000
            :home-package (pkg-witness "ACL2S")))
    (to-string (cdr l)))))

(defun l-to-string (l)
  (intern-in-package-of-symbol
   (string-append-lst (to-string l))
   'x))

; (l-to-string '(a - b - c - d))
; (l-to-string '(a - (lambda (x) (+ 1 x)) - b - c - d))

(defmacro create-map* (fun lst-type return-type &rest rst)
  (b* ((name (assoc-equal :name rst))
       (name (and name (second name)))
       (mname (or name fun))
       (f* (l-to-string `(map *-* ,mname)))
       (fixed-vars-types (assoc-equal :fixed-vars rst))
       (fixed-vars-types
        (and fixed-vars-types (second fixed-vars-types)))
       (fixed-vars (strip-cars (strip-cdrs fixed-vars-types)))
       (ic (if fixed-vars-types
               (append `(and (,lst-type l)) fixed-vars-types)
             `(,lst-type l)))
       (args `(l ,@fixed-vars))
       (oc `(,return-type (,f* ,@args))))
      `(defuncd ,f* ,args
         :input-contract ,ic
         :output-contract ,oc
         (if (endp l)
             ()
           (cons (,fun (car l) ,@fixed-vars)
                 (,f* (cdr l) ,@fixed-vars))))))
  
#|
(defmacro create* (x &rest rst)
  `(list ',x ',rst))

(create* x ((r y)))
(create* x (r y) (z a))
(create* x)

|#
 
(defmacro map* (fun lst &rest rst)
  (let ((f* (l-to-string `(map *-* ,fun))))
    `(,f* ,lst ,@rst)))

#|
;Examples

(defdata lol (listof true-list))
(defdata lon (listof nat))
(defdata lor (listof rational))

:trans1 (create-map* len lolp lonp)
(create-map* len lolp lonp)
(create-map* rev lolp lolp)

(defdata llol (listof lol))

(create-map* map*-*rev llolp llolp)
:trans1 (create-map* 1+ lorp lorp)

; and now I can write things like

(map* len '((1) (1 2)))
(map* rev '((0 1) (1 2)))
(map* map*-*rev '(((0 1) (1 2)) ((3 4))))

(len (map* len '((1) (1 2))))

:trans1 (create-map* + lorp lorp 
                     (:fixed-vars ((rationalp y))) (:name +y))
:trans1 (create-map* (lambda (x) (+ x 3)) lorp lorp)

(create-map* + lorp lorp 
             (:fixed-vars ((rationalp y))) (:name +y))
(create-map* (lambda (x) (+ x 3)) lorp lorp)

; Notice that I use the name +y here, not +
(map* +y '(1/2 -2 -17/2) 3)
(map* (lambda (x) (+ x 3)) '(1/2 -2 -17/2))

(defmacro create-reduce* (f et lt &rest rst)
  (b* ((name (assoc-equal :name rst))
       (name (and name (second name)))
       (f* (if name name (l-to-string `(reduce *-* ,f))))
       (fixed-vars-types (assoc-equal :fixed-vars rst))
       (fixed-vars-types (and fixed-vars-types (second fixed-vars-types)))
       (fixed-vars (strip-cars (strip-cdrs fixed-vars-types)))
       (ic (append `(and (,et e) (,lt l) ,@fixed-vars-types)))
       (args `(e l ,@fixed-vars))
       (oc `(,et (,f* ,@args))))
      `(defunc ,f* ,args
         :input-contract ,ic
         :output-contract ,oc
         (if (endp l)
             e
           (,f (car l) (,f* e (rest l) ,@fixed-vars) ,@fixed-vars)))))
|#

;; Proof that list is a Functor
;; 0. associates each object to a list containing that object
(property list-functor (x :all)
          (== (list x) `(,x))
          :rule-classes nil)

;; create-map* lifts a function to lists.
;; We prove that it is the list functor.
;; 1. create-map* preserves identity function
(definec id (x :all) :all
  x)

(create-map* id tlp tlp)

;; id is identity for true-lists
(property id-tl (xs :tl)
          (== (id xs) xs))

(property functor-id (xs :tl)
          (== (map* id xs)
              ;; From id-tl, we can use id
              (id xs))
          :hints (("Goal" :in-theory
                   (enable map*-*id))))

;; 2. create-map* preserves function compositions
(defstub f (*) => *)
(defstub g (*) => *)
(definec gof (x :all) :all
  (g (f x)))

(create-map* f tlp tlp)
(create-map* g tlp tlp)
(create-map* gof tlp tlp)

(property functor-comp (xs :tl)
          (== (map* gof xs)
              (map* g (map* f xs)))
          :hints (("Goal" :in-theory
                   (enable map*-*f map*-*g map*-*gof))))


(defmacro create-map2* (fun lst1-type lst2-type return-type &rest rst)
  (b* ((name (assoc-equal :name rst))
       (name (and name (second name)))
       (mname (or name fun))
       (f* (l-to-string `(map2 *-* ,mname)))
       (fixed-vars-types (assoc-equal :fixed-vars rst))
       (fixed-vars-types
        (and fixed-vars-types (second fixed-vars-types)))
       (fixed-vars (strip-cars (strip-cdrs fixed-vars-types)))
       (ic (append `(and (,lst1-type l1) (,lst2-type l2)) fixed-vars-types))
       (args `(l1 l2 ,@fixed-vars))
       (oc `(,return-type (,f* ,@args))))
      `(defuncd ,f* ,args
         :input-contract ,ic
         :output-contract ,oc
         (if (or (endp l1)
                 (endp l2))
             ()
           (cons (,fun (car l1) (car l2) ,@fixed-vars)
                 (,f* (cdr l1) (cdr l2) ,@fixed-vars))))))

(defmacro map2* (fun lst1 lst2 &rest rst)
  (let ((f* (l-to-string `(map2 *-* ,fun))))
    `(,f* ,lst1 ,lst2 ,@rst)))

#|
;Examples

:trans1 (create-map2* + lorp lorp lorp)
(create-map2* + lorp lorp lorp)
(create-map2* * lorp lorp lorp)
(create-map2* * lorp lorp lorp (:name 2*))
(create-map2* * lorp lorp lorp (:name *2))

(map2* +  '(1 1/2 4 2) '(-3 2 1/2 1))
(map2* *  '(1 1/2 4 2) '(-3 2 1/2 1))
(map2* 2* '(1 1/2 4 2) '(-3 2 1/2 1))
(map2* *2 '(1 1/2 4 2) '(-3 2 1/2 1))

(map2* + 
       (map2* * '(1 1/2 4 2) '(-3 2 1/2 1))
       (map2* + '(1 1/2 4 2) '(-3 2 1/2 1)))
       
|#

(defmacro create-reduce* (fun base-type lst-type &rest rst)
  (b* ((name (assoc-equal :name rst))
       (name (and name (second name)))
       (mname (or name fun))
       (f* (l-to-string `(reduce *-* ,mname)))
       (fixed-vars-types (assoc-equal :fixed-vars rst))
       (fixed-vars-types (and fixed-vars-types (second fixed-vars-types)))
       (fixed-vars (strip-cars (strip-cdrs fixed-vars-types)))
       (ic (append `(and (,base-type e) (,lst-type l) ,@fixed-vars-types)))
       (args `(e l ,@fixed-vars))
       (oc `(,base-type (,f* ,@args))))
      `(defuncd ,f* ,args
         :input-contract ,ic
         :output-contract ,oc
         (if (endp l)
             e
           (,fun (car l) (,f* e (cdr l) ,@fixed-vars) ,@fixed-vars)))))

(defmacro reduce* (fun base-element l &rest rst)
  (let ((f* (l-to-string `(reduce *-* ,fun))))
    `(,f* ,base-element ,l ,@rst)))


#|

; Examples

:trans1 (create-reduce* + rationalp lorp)
:trans1 (create-reduce* 
         + rationalp lorp
         (:fixed-vars ((rationalp x) (rationalp y)))
         (:name 2+))

(create-reduce* + rationalp lorp)
(create-reduce* 
         + rationalp lorp
         (:fixed-vars ((rationalp x) (rationalp y)))
         (:name 2+))

(1+ (reduce* + 0 (map* len '((1) (1 2) (1 2 3) (1 2 3 4)))))

(1+ (reduce* 2+ 0 (map* len '((1) (1 2) (1 2 3) (1 2 3 4))) 0 0))
(1+ (reduce* 2+ 0 (map* len '((1) (1 2) (1 2 3) (1 2 3 4))) 1 2))

(create-reduce* (lambda (x y) (+ x y 2)) rationalp lorp)

(1+ (reduce* (lambda (x y) (+ x y 2)) 0 (map* len '((1) (1 2) (1 2 3) (1 2 3 4)))))

(defun foo (l)
  (1+ (reduce* + 0 (map* len l))))

(foo '((1) (2 3)))

|#

(defmacro create-filter* (fun lst-type &rest rst)
  (b* ((name (assoc-equal :name rst))
       (name (and name (second name)))
       (mname (or name fun))
       (f* (l-to-string `(filter *-* ,mname)))
       (fixed-vars-types (assoc-equal :fixed-vars rst))
       (fixed-vars-types (and fixed-vars-types (second fixed-vars-types)))
       (fixed-vars (strip-cars (strip-cdrs fixed-vars-types)))
       (ic (if fixed-vars-types
               (append `(and (,lst-type l)) fixed-vars-types)
             `(,lst-type l)))
       (args `(l ,@fixed-vars))
       (oc `(,lst-type (,f* ,@args))))
      `(defuncd ,f* ,args
         :input-contract ,ic
         :output-contract ,oc
         (cond ((endp l) ())
               ((,fun (car l) ,@fixed-vars)
                (cons (car l) (,f* (cdr l) ,@fixed-vars)))
               (t (,f* (cdr l) ,@fixed-vars))))))

(defmacro filter* (fun lst &rest rst)
  (let ((f* (l-to-string `(filter *-* ,fun))))
    `(,f* ,lst ,@rst)))

#|

; Examples

:trans1 (create-filter* <= lorp (:fixed-vars ((rationalp y))))
(create-filter* <= lorp (:fixed-vars ((rationalp y))))

:trans1 (create-filter* (lambda (x) (<= x 3)) lorp)
(create-filter* (lambda (x) (<= x 3)) lorp)

(map* len '((1) (1 2) (1 2 3) (1 2 3 4)))
(filter* <= (map* len '((1) (1 2) (1 2 3) (1 2 3 4))) 2)
(filter* <= (map* len '((1) (1 2) (1 2 3) (1 2 3 4))) 4)

(filter* <= (map* len '((1) (1 2) (1 2 3) (1 2 3 4))) 3)
(filter* (lambda (x) (<= x 3))
         (map* len '((1) (1 2) (1 2 3) (1 2 3 4))))

(defunc len-less (l y)
  :input-contract (and (true-listp l) (natp y))
  :output-contract (booleanp (len-less l y))
  (<= (len l) y))

:trans1 (create-filter* len-less lolp (:fixed-vars ((natp y))))
(create-filter* len-less lolp (:fixed-vars ((natp y))))

:trans1 (create-filter* (lambda (x) (<= (len x) 3)) lolp)
(create-filter* (lambda (x) (<= (len x) 3)) lolp)

(filter* len-less '((1) (1 2) (1 2 3) (1 2 3 4)) 2)
(filter* len-less '((1) (1 2) (1 2 3) (1 2 3 4)) 4)

(filter* len-less '((1) (1 2) (1 2 3) (1 2 3 4)) 3)
(filter* (lambda (x) (<= (len x) 3))
         '((1) (1 2) (1 2 3) (1 2 3 4)))
 
|#



;;some cool things to implement : compose, partial-apply, scanl, [functor, applicative, monad]?

(defmacro create-compose* (fun1 fun2 in-type out-type &rest rst)
  (b* ((name (assoc-equal :name rst))
       (name (and name (second name)))
       (mname (or name `(,fun1 *-* ,fun2)))
       (f* (l-to-string `(comp *-* ,mname)))
       (ic `(,in-type x))
       (args `(x))
       (oc `(,out-type (,f* ,@args))))
      `(defunc ,f* ,args
         :input-contract ,ic
         :output-contract ,oc
         (,fun1 (,fun2 x)))))


#|
; Examples

:trans1 (create-compose* + - natp natp (:name +-))
(create-compose* + - intp intp (:name +-))

;;Call directly with composed function name
(comp*-*+- 5)


(definec i->b (x :nat) :boolean
  (if (= x 0) nil t))

(definec b->i (b :boolean) :nat
  (if b 1 0))

(create-compose* b->i i->b natp natp)

(|COMP*-*(B->I *-* I->B)| 100)
(|COMP*-*(B->I *-* I->B)| 0)

|#

(defmacro partial-app* (fun args in-argtypes out-type &rest rst)
  (b* ((name (assoc-equal :name rst))
       (name (and name (second name)))
       (mname (or name fun))
       (f* (l-to-string `(partial *-* ,mname)))
       (ic (if (<= (len in-argtypes) 1)
	       (car in-argtypes)
	     (cons 'and in-argtypes)))
       (rem-args (strip-cars (strip-cdrs in-argtypes)))
       (oc `(,out-type (,f* ,@rem-args))))
      `(defunc ,f* ,rem-args
         :input-contract ,ic
         :output-contract ,oc
         (,fun ,@args ,@rem-args))))

#|
; Examples
:trans1 (partial-app* + (2) ((natp x)) natp)

(partial-app* + (2) ((natp x)) natp (:name plus2))
(check= (PARTIAL*-*PLUS2 4) 6)
|#


(defmacro lift* (fun in-type out-type &rest rst)
  (b* ((name (assoc-equal :name rst))
       (name (and name (second name)))
       (mname (or name fun))
       (f* (l-to-string `(lift *-* ,mname)))
       (lifted-in-type (l-to-string `(lo ,in-type)))
       (lifted-out-type (l-to-string `(lo ,out-type)))
       (lifted-in-typep (l-to-string `(,lifted-in-type p)))
       (lifted-out-typep (l-to-string `(,lifted-out-type p)))
       (ic `(,lifted-in-typep l))
       (args `(l))
       (oc `(,lifted-out-typep (,f* ,@args))))
    `(progn
       (defdata ,lifted-in-type (listof ,in-type))
       (defdata ,lifted-out-type (listof ,out-type))
       (defunc ,f* ,args
	 :input-contract ,ic
	 :output-contract ,oc
	 (if (endp l) ()
	   (cons (,fun (car l)) (,f* (cdr l))))))))

#|
;Examples
:trans1 (lift* 1+ rational rational)

(lift* 1+ rational rational)
(check= (lift*-*1+ '(1 2 3 4)) '(2 3 4 5))
|#


(defmacro lift2* (fun in1-type in2-type out-type &rest rst)
  (b* ((name (assoc-equal :name rst))
       (name (and name (second name)))
       (mname (or name fun))
       (f* (l-to-string `(lift2 *-* ,mname)))
       (lifted-in1-type (l-to-string `(lo ,in1-type)))
       (lifted-in2-type (l-to-string `(lo ,in2-type)))
       (lifted-out-type (l-to-string `(lo ,out-type)))
       (lifted-in1-typep (l-to-string `(,lifted-in1-type p)))
       (lifted-in2-typep (l-to-string `(,lifted-in2-type p)))
       (lifted-out-typep (l-to-string `(,lifted-out-type p)))
       (ic `(and (,lifted-in1-typep l1) (,lifted-in2-typep l2)))
       (args `(l1 l2))
       (oc `(,lifted-out-typep (,f* ,@args))))
    `(progn
       (defdata ,lifted-in1-type (listof ,in1-type))
       (defdata ,lifted-in2-type (listof ,in2-type))
       (defdata ,lifted-out-type (listof ,out-type))
       (defunc ,f* ,args
	 :input-contract ,ic
	 :output-contract ,oc
	 (if (or (endp l1) (endp l2)) ()
	   (cons (,fun (car l1) (car l2)) (,f* (cdr l1) (cdr l2))))))))

#|
;Examples
:trans1 (lift2* + rational rational rational)

(lift2* + rational rational rational)
(check= (lift2*-*+ '(1 2 3 4 5) '(5 4 3 2 1)) '(6 6 6 6 6))
|#

(defmacro create-tuple* (&rest types)
  (b* ((name (l-to-string types)))
    `(defdata ,name ,(cons 'list types))))

(defmacro tuple* (&rest types)
  (l-to-string (append types '(p))))
    
  
