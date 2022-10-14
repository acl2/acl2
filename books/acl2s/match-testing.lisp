#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

;; Author: Pete Manolios

(in-package "ACL2S")
(include-book "acl2s/custom" :dir :system :ttags :all)
(set-termination-method :ccg)
;(acl2s-defaults :set testing-enabled nil)

;; Examples from the documentation

(definec int-class (x :int) :pos
  (match x
    (:pos 1)
    (:even 2)
    (:neg 3)))

(definec int-class2 (x :int) :pos
  (match x
    (:pos 
     (:even 1)
     (:odd 2))
    (:neg
     (:even 3)
     (:odd 4))
    (0 5)))
    
(definec int-class3 (x :int) :pos
  (match x
    (:pos 
     (:even 1)
     (& 2))
    (:neg
     (:even 3)
     (& 4))
    (& 5)))

(property (x :int)
  (== (int-class2 x) (int-class3 x)))

(must-fail
  (definec int-class4 (x :int) :pos
    (match x
      (:pos 
       (:even 1)
       (& 2))
      (:neg
       (:even 3)
       (:nat 4))
      (& 5))))

(definec fact (n :nat) :pos
  (match n
    (0 1)
    (& (* n (fact (1- n))))))

(definec fact1 (n :nat) :pos
  (match n
    ((:t (< n 2)) 1)
    (& (* n (fact1 (1- n))))))

(property (n :nat)
  (== (fact1 n) (fact n)))

(definec fib (n :nat) :pos
  :skip-tests t
  (match n
    ((:or 0 1) 1)
    (& (+ (fib (1- n)) (fib (- n 2))))))
  
(definec fib2 (n :nat) :pos
  :skip-tests t
  (match n
    (0 1)
    (1 1)
    (& (+ (fib2 (1- n)) (fib2 (- n 2))))))

(definec fib3 (n :nat) :pos
  :skip-tests t
  (match n
    ((:t (< n 2)) 1)
    (& (+ (fib3 (1- n)) (fib3 (- n 2))))))

(property (n :nat)
  :testing? nil
  (and (== (fib3 n) (fib n))
       (== (fib2 n) (fib n))))

(definec pascal (i :nat j :nat) :pos
  :skip-tests t
  (match (list i j)
    ((:or (0 &) (& 0) (& !i)) 1)
    (& (+ (pascal (1- i) (1- j))
          (pascal (1- i) j)))))

(definec pascal2 (i :nat j :nat) :pos
  :skip-tests t
  (match (list i j)
    ((0 &) 1)
    ((& 0) 1)
    ((!i !i) 1)
    (& (+ (pascal2 (1- i) (1- j))
          (pascal2 (1- i) j)))))

(property (i :nat j :nat)
  :testing? nil
  (== (pascal i j) (pascal2 i j)))

(definec mem (e :all x :tl) :bool
  (match x
    (nil nil)
    ((!e . &) t)
    ((& . r) (mem e r))))

(definec subset (x :tl y :tl) :bool
  (match x
    (nil t)
    ((f . r) (and (mem f y) (subset r y)))))

#|
Have to use acl2::x to redefine, but here is the definition.

(defun acl2-count (x)
  (declare (xargs :guard t :mode :program))
  (if (consp x)
      (+ 1 (acl2-count (car x))
         (acl2-count (cdr x)))
    (if (rationalp x)
        (if (integerp x)
            (integer-abs x)
          (+ (integer-abs (numerator x))
             (denominator x)))
      (if (complex/complex-rationalp x)
          (+ 1 (acl2-count (realpart x))
             (acl2-count (imagpart x)))
        (if (stringp x)
            (length x)
          0)))))
|#

(definec acl2-count2 (x :all) :nat
  (match x
    ((a . b) (+ 1 (acl2-count2 a) (acl2-count2 b)))
    (:rational
     (:integer (integer-abs x))
     (& (+ (integer-abs (numerator x))
           (denominator x))))
    ((:r complex/complex-rationalp)
     (+ 1 (acl2-count2 (realpart x))
        (acl2-count2 (imagpart x))))
    (:string (length x))
    (& 0)))
 
(property (x :all)
  (== (acl2-count2 x) (acl2-count x)))

#|

(defun acl2s-size (x)
  (declare (xargs :guard t))
  (cond ((consp x)
         (+ 1 (acl2s-size (car x))
            (acl2s-size (cdr x))))
        ((rationalp x)
         (integer-abs (numerator x)))
        ((stringp x) (length x))
        (t 0)))

|#

(definec acl2s-size2 (x :all) :nat
  (match x
    ((a . b) (+ 1 (acl2s-size2 a) (acl2s-size2 b)))
    (:rational (integer-abs (numerator x)))
    ((:r stringp) (length x))
    (& 0)))

(property (x :all)
  (== (acl2s-size2 x) (acl2s-size x)))
