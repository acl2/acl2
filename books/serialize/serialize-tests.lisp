(in-package "ACL2")
(include-book "serialize" :ttags :all)

(defmacro test-serialize (x)
  (declare (ignorable x))
  `(make-event
    #+gcl
    (value `(value-triple :does-not-work-on-gcl))
    #-gcl
    (let ((state (serialize::write "test.sao" ,x :verbosep t)))
      (mv-let (obj state)
              (serialize::read "test.sao" :verbosep t)
              (if (equal ,x obj)
                  (value `(value-triple :test-passed))
                (er soft 'test-serialize
                    "Test failed for ~x0.~%" ,x))))))

(test-serialize 0)
(test-serialize 1)
(test-serialize -1 )
(test-serialize 128308190248190238190283901283901283901283901823901 )

(test-serialize 1/2 )
(test-serialize -1/2 )

(test-serialize #c(0 1) )
(test-serialize #c(-1 1/3) )

(test-serialize #\a )
(test-serialize #\z )

(test-serialize "foo" )
(test-serialize "bar" )
(test-serialize "" )
(test-serialize (code-char 0) )

(test-serialize nil )
(test-serialize t )

(test-serialize '(nil . nil))
(test-serialize '(t . nil))



;; Now I'm going to make a big object with lots of all kinds of atoms.


(defun nats (i j)
  (declare (xargs :mode :program))
  (if (= i j)
      (list j)
    (cons i (nats (+ i 1) j))))

(defun map-code-char (x)
  (if (consp x)
      (cons (code-char (car x))
            (map-code-char (cdr x)))
    nil))

(defun map-negate (x)
  (if (consp x)
      (cons (- (car x))
            (map-negate (cdr x)))
    nil))

(defun map-make-rational1 (num dens)
  (if (consp dens)
      (cons (/ num (car dens))
            (map-make-rational1 num (cdr dens)))
    nil))

(defun map-make-rational (nums dens)
  (if (consp nums)
      (append (map-make-rational1 (car nums) dens)
              (map-make-rational (cdr nums) dens))
    nil))

(defun map-make-complex1 (real imags)
    (if (consp imags)
      (cons (complex real (car imags))
            (map-make-complex1 real (cdr imags)))
    nil))

(defun map-make-complex (reals imags)
  (if (consp reals)
      (append (map-make-complex1 (car reals) imags)
              (map-make-complex (cdr reals) imags))
    nil))

(defun make-strs (base n)
  (if (zp n)
      (list base)
    (cons (concatenate 'string base "-" (coerce (explode-atom n 10) 'string))
          (make-strs base (- n 1)))))

(defun map-intern (base strs)
  (if (consp strs)
      (cons (intern-in-package-of-symbol (car strs) base)
            (map-intern base (cdr strs)))
    nil))

(defconst *test* 
  (let* ((nats         (nats 0 1000))
         (negatives    (map-negate nats))
         (chars        (map-code-char (nats 0 255)))
         (numerators   (nats 0 30))
         (nnumerators  (map-negate numerators))
         (denominators (nats 15 20))
         (rats         (append (map-make-rational nnumerators denominators)
                               (map-make-rational numerators denominators)))
         (complexes    (map-make-complex rats
                                         (map-make-rational (nats 0 10)
                                                            (nats 1 5))))
         (strs         (append (make-strs "foo" 100)
                               (make-strs "bar" 100)
                               (make-strs "baz" 100)))
         (syms         (append (map-intern 'acl2::foo strs)
                               (map-intern 'serialize::foo strs)
                               (map-intern 'common-lisp::foo strs)))
         (stuff
          (list nats negatives chars rats complexes strs syms))
         (more-stuff
          (list stuff stuff stuff stuff stuff stuff stuff stuff stuff)))
    more-stuff))
    
(test-serialize *test*)

