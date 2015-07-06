(in-package "ACL2")

; SOFT (Second-Order Functions and Theorems) Examples
;
; Copyright (C) 2015 Kestrel Institute (http://www.kestrel.edu)
;
; License (an MIT license):
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
; Original author: Alessandro Coglio (coglio@kestrel.edu)

; Overview:
;
;   This file contains examples of use of SOFT
;   (Second-Order Functions and Theorems).

(include-book "soft")

; Two unary function variables.
; Starting function variable names with ? provides a visual cue
; for their function variable status,
; but SOFT does not enforce this naming convention.

(defunvar ?f (*) => *)

(defunvar ?p (*) => *)

; A plain non-recursive second-order function
; to apply its function paramete to its individual parameter four times.

(defun2 quad-?f (?f) (x)
  (declare (xargs :guard t))
  (?f (?f (?f (?f x)))))

; A plain recursive second-order predicate (i.e. boolean-valued function)
; to recognize NIL-terminated lists
; whose elements all satisfy the predicate parameter.

(defun2 all-?p (?p) (l)
  (declare (xargs :guard t))
  (cond ((atom l) (null l))
        (t (and (?p (car l)) (all-?p (cdr l))))))

; A plain recursive second-order function
; to homomorphically lift ?F to operate
; on NIL-terminate lists whose elements satisfy ?P.
; The predicate parameter ?P only appears in the guard, not in the body.

(defun2 map-?f-?p (?f ?p) (l)
  (declare (xargs :guard (all-?p l)))
  (cond ((endp l) nil)
        (t (cons (?f (car l)) (map-?f-?p (cdr l))))))

; A choice second-order function
; to retun a fixed point of ?F, if any exists.

(defchoose2 fixpoint-?f x (?f) () (equal (?f x) x))

; A quantifier second-order predicate to recognize injective functions.

(defun-sk2 injective-?f (?f) ()
  (forall (x y) (implies (equal (?f x) (?f y)) (equal x y))))

; An instance of a second-order function
; to wrap a value (into a singleton list) four times.

(defn wrap (x) (list x))

(defun-inst quad-wrap (quad-?f (?f . wrap)))

; An instance of a second-order function
; to recognize NIL-terminated lists of octets.

(defn octetp (x) (and (natp x) (< x 256)))

(defun-inst all-octetp (all-?p (?p . octetp)))

; An instance of a second-order function
; to translate list of octets to lists of corresponding characters.
; Since the guard of CODE-CHAR is equivalent to OCTETP,
; the instantiated guard of MAP-CODE-CHAR is proved.

(defun-inst map-code-char (map-?f-?p (?p . octetp) (?f . code-char)))

; An instance of a second-order function
; to return a fixed point of a function that doubles its argument.

(defn twice (x) (* 2 (fix x)))

(defun-inst fixpoint-twice (fixpoint-?f (?f . twice)))

; An instance of a second-order function
; to recognize functions whose four-fold application is injective.

(defun-inst injective-quad-?f (?f) (injective-?f (?f . quad-?f)))

; A second-order theorem asserting that
; the homomorphic lifting of ?F to lists of ?P values
; preserves the length of the list,
; for every functin ?F and predicate ?P.

(defthm len-map-?f-?p (equal (len (map-?f-?p l)) (len l)))

; A second-order theorem asserting that
; the four-fold application of an injective function is injective.

(defthm injective-quad-?f-when-injective-?f
  (implies (injective-?f) (injective-quad-?f))
  :hints
  (("Goal"
    :use
    ((:instance injective-?f-necc
                (x (?f (?f (?f (?f (mv-nth 0 (injective-quad-?f-witness)))))))
                (y (?f (?f (?f (?f (mv-nth 1 (injective-quad-?f-witness))))))))
     (:instance injective-?f-necc
                (x (?f (?f (?f (mv-nth 0 (injective-quad-?f-witness))))))
                (y (?f (?f (?f (mv-nth 1 (injective-quad-?f-witness)))))))
     (:instance injective-?f-necc
                (x (?f (?f (mv-nth 0 (injective-quad-?f-witness)))))
                (y (?f (?f (mv-nth 1 (injective-quad-?f-witness))))))
     (:instance injective-?f-necc
                (x (?f (mv-nth 0 (injective-quad-?f-witness))))
                (y (?f (mv-nth 1 (injective-quad-?f-witness)))))
     (:instance injective-?f-necc
                (x (mv-nth 0 (injective-quad-?f-witness)))
                (y (mv-nth 1 (injective-quad-?f-witness))))))))

; An instance of a second-order theorem asserting that
; the translator of lists of octets to lists of characters
; preserves the length of the list.

(defthm-inst len-map-code-char
  (len-map-?f-?p (?f . code-char) (?p . octetp)))

; An instance of a second-order theorem asserting that
; the four-fold application of the function
; that wraps its argument into a singleton list
; is injective.

(defun-inst injective-quad-wrap (injective-quad-?f (?f . wrap)))

(defun-inst injective-wrap (injective-?f (?f . wrap)))

(defthm-inst injective-quad-wrap-when-injective-wrap
  (injective-quad-?f-when-injective-?f (?f . wrap)))
