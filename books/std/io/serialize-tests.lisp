; Serializing ACL2 Objects
; Copyright (C) 2009-2012 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "unsound-read" :ttags :all)
(include-book "std/util/bstar" :dir :system)
(set-compile-fns t)

(defmacro test-serialize (x &rest write-args)
  (declare (ignorable x write-args))
  `(make-event
    (b* ((- (cw ">>> Writing file with serialize-write~%"))
         (state (serialize-write "test.sao" ,x :verbosep t))

         (- (cw ">>> Reading with serialize-read~%"))
         ((mv obj1 state) (serialize-read "test.sao" :verbosep t))
         (- (or (equal ,x obj1) (cw "serialize-read returned bad result: ~x0~%" obj1)))

         (- (cw ">>> Reading with unsound-read~%"))
         (obj2 (unsound-read "test.sao" :verbosep t))
         (- (or (equal ,x obj2) (cw "unsound-read returned bad result: ~x0~%" obj2)))

         ((unless (and (equal ,x obj1)
                       (equal ,x obj2)))
          (er soft 'test-serialize "Test failed for ~x0.~%" ,x)))

      (value `(value-triple :test-passed)))))


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

(defun make-strs (base n acc)
  (if (zp n)
      (cons base acc)
    (make-strs base (- n 1)
               (cons (concatenate 'string base "-" (coerce (explode-atom n 10) 'string))
                     acc))))

(defun map-intern (base strs)
  (if (consp strs)
      (cons (intern-in-package-of-symbol (car strs) base)
            (map-intern base (cdr strs)))
    nil))

(comp t) ; at the least, need to compile nats for GCL on a Mac

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
         (strs         (append (make-strs "foo" 100 nil)
                               (make-strs "bar" 100 nil)
                               (make-strs "baz" 100 nil)))
         (syms         (append (map-intern 'acl2::foo strs)
                               (map-intern 'acl2-output-channel::foo strs)
                               (map-intern 'common-lisp::foo strs)))
         (stuff
          (list nats negatives chars rats complexes strs syms))
         (more-stuff
          (list stuff stuff stuff stuff stuff stuff stuff stuff stuff)))
    more-stuff))

(test-serialize *test*)



(local
 (encapsulate
   ()
   ;; Write NIL to test.sao
   (make-event
    (let ((state (serialize-write "test.sao" nil)))
      (value '(value-triple :invisible))))

   ;; Prove that test.sao contains NIL.
   (defthm lemma-1
     (equal (unsound-read "test.sao") nil)
     :rule-classes nil)

   ;; Write T to test.sao
   (make-event
    (let ((state (serialize-write "test.sao" t)))
      (value '(value-triple :invisible))))

   ;; Prove that test.sao contains T.
   (defthm lemma-2
     (equal (unsound-read "test.sao") t)
     :rule-classes nil)

   ;; Arrive at our contradiction.
   (defthm qed
     nil
     :rule-classes nil
     :hints(("Goal"
             :use ((:instance lemma-1)
                   (:instance lemma-2))
             :in-theory (disable (unsound-read-fn)))))))


(make-event
 '(defconst *foo* (make-fast-alist (pairlis$ '(1 2 3 4) '(a b c d)))))

(make-event
 '(defconst *foo2* (make-fast-alist (list (cons "blah" 1)
                                          (cons (concatenate 'string "bl" "ah") 2)
                                          (cons "black" 3)
                                          (cons (concatenate 'string "bl" "ack") 3)
                                          (cons "sheep" 4)))))

(local (set-slow-alist-action :break))

(value-triple (hons-get '1 *foo*))
(value-triple (hons-get "blah" *foo*))

(defconst *bar* '((1 . 2)))

#||

;; Well, even with compilation on, gcl and sbcl and even ccl are having
;; overflows here.  Stupidity.  Stupidity.  I comment out the test.

(defconst *test2*
  (append (make-strs "foo" 100000 nil)
          (make-strs "foo" 100000 nil)
          (make-strs "bar" 100000 nil)
          (make-strs "bar" 100000 nil)
          (make-strs "baz" 100000 nil)
          (make-strs "baz" 100000 nil)))

(test-serialize *test2*
                ;; This test shows some warnings about the string and cons
                ;; tables begin resized, and takes 7.6 seconds on fv-1
                )

(test-serialize *test2*
                :cons-table-size (expt 2 21)
                :string-table-size (expt 2 21)
                ;; This prints no such messages and reduces the time needed
                ;; to 5.0 seconds.
                )

||#


