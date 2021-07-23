; Operand stacks
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Note: Portions of this file may be taken from books/models/jvm/m5.  See the
; LICENSE file and authorship information there as well.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

(include-book "types") ;for *two-slot-types*
(include-book "kestrel/lists-light/reverse-list" :dir :system)
(include-book "kestrel/utilities/myif-def" :dir :system)

;;;
;;; operand stacks
;;;

(defund operand-stackp (stack) (declare (xargs :guard t)) (true-listp stack)) ;fixme define a notion of a typed-stack!
(defund empty-operand-stack () (declare (xargs :guard t)) nil) ; was a macro
(defund empty-operand-stackp (stack) (declare (xargs :guard (operand-stackp stack) :guard-hints (("Goal" :in-theory (enable operand-stackp))))) (endp stack)) ; was a macro

(defthm operand-stackp-of-empty-operand-stack
  (operand-stackp (empty-operand-stack))
  :hints (("Goal" :in-theory (enable empty-operand-stack operand-stackp))))

;fixme define an operandp??

(defund push-operand (obj stack)
  (declare (xargs :guard (operand-stackp stack)))
  (cons obj stack))

;guard to require a non-empty-stack?
(defund top-operand (stack)
  (declare (xargs :guard (operand-stackp stack) :guard-hints (("Goal" :in-theory (enable operand-stackp)))))
  (car stack))

;guard to require a non-empty-stack?
(defund pop-operand (stack)
  (declare (xargs :guard (operand-stackp stack) :guard-hints (("Goal" :in-theory (enable operand-stackp)))))
  (cdr stack))

(defthm operand-stackp-of-pop
  (implies (and (operand-stackp stack)
                ;; fixme require non-empty
                )
           (operand-stackp (pop-operand stack)))
  :hints (("Goal" :in-theory (enable operand-stackp pop-operand))))

(defthm push-operand-equal-rewrite
  (equal (equal (push-operand a x) (push-operand b y))
         (and (equal a b)
              (equal x y)))
  :hints (("Goal" :in-theory (enable push-operand))))

(defund operand-stack-size (stack)
  (declare (xargs :guard (operand-stackp stack) :guard-hints (("Goal" :in-theory (enable operand-stackp)))))
  (len stack))

(defthm operand-stack-size-of-empty-operand-stack
  (equal (operand-stack-size (empty-operand-stack))
         0)
  :hints (("Goal" :in-theory (enable empty-operand-stack))))

(defthm operand-stack-size-of-push-operand
  (equal (operand-stack-size (push-operand obj stack))
         (+ 1 (operand-stack-size stack)))
  :hints (("Goal" :in-theory (enable push-operand operand-stack-size))))

(defthm operand-stack-size-of-pop-operand
  (implies (not (empty-operand-stackp stack))
           (equal (operand-stack-size (pop-operand stack))
                  (+ -1 (operand-stack-size stack))))
  :hints (("Goal" :in-theory (enable pop-operand operand-stack-size empty-operand-stackp))))

;which do we prefer?
(defthm operand-stack-size-of-pop-operand-2
  (implies (< 0 (operand-stack-size stack))
           (equal (operand-stack-size (pop-operand stack))
                  (+ -1 (operand-stack-size stack))))
  :hints (("Goal" :in-theory (enable pop-operand operand-stack-size))))

(defthm top-operand-of-push-operand
  (equal (top-operand (push-operand x s))
         x)
  :hints (("Goal" :in-theory (enable top-operand push-operand))))

(defthm pop-operand-of-push-operand
  (equal (pop-operand (push-operand x s))
         s)
  :hints (("Goal" :in-theory (enable pop-operand push-operand))))

(defthm push-operand-onto-x-cant-equal-x
  (not (equal (push-operand a x) x))
  :hints (("Goal" :in-theory (enable push-operand))))

(defthm operand-stackp-of-push-operand
  (equal (operand-stackp (push-operand item stack))
         (and (operand-stackp stack)
              ;; fixme require the item pushed to be okay?
              ))
  :hints (("Goal" :in-theory (enable operand-stackp push-operand))))

;;;
;;; topn-operands
;;;

;returns a list of the top n items on the stack (topmost element first):
(defund topn-operands (n stack)
  (declare (xargs :guard (and (natp n) (operand-stackp stack))))
  (if (zp n)
      nil
    (cons (top-operand stack)
          (topn-operands (+ -1 n) (pop-operand stack)))))

(defthm topn-operands-of-push-operand
  (implies (posp n)
           (equal (topn-operands n (push-operand item stack))
                  (cons item (topn-operands (+ -1 n) stack))))
  :hints (("Goal":in-theory (enable topn-operands push-operand top-operand pop-operand))))

(defthm topn-operands-of-0
  (equal (topn-operands 0 stack)
         nil)
  :hints (("Goal" :in-theory (enable topn-operands))))

;;;
;;; popn-operands
;;;

;fixme when the number of frames to pop is a constant, we could use a macro instead of this (saving the time of using the popn opener and base rules..)
;todo: handle longs/doubles better here, if we can.  see pop-items-off-stack.
(defund popn-operands (n stack)
  (declare (type (integer 0 *) n)
           (xargs :guard (and (operand-stackp stack) (<= n (operand-stack-size stack)))
                  :guard-hints (("Goal" :in-theory (enable operand-stackp pop-operand operand-stack-size)))))
  (if (zp n)
      stack
      (popn-operands (- n 1) (pop-operand stack))))

(defthm popn-operands-base
  (implies (zp n)
           (equal (popn-operands n stack)
                  stack))
  :hints (("Goal" :in-theory (enable popn-operands))))

;yuck? use popn-operands-of-push-operand?
(defthm popn-operands-opener
  (implies (not (zp n))
           (equal (popn-operands n stack)
                  (popn-operands (- n 1) (pop-operand stack))))
  :hints (("Goal" :in-theory (enable popn-operands))))

(defthm operand-stackp-of-popn-operands
  (implies (and (operand-stackp stack)
                ;; fixme require stack big enough
                )
           (operand-stackp (popn-operands n stack)))
  :hints (("Goal" :in-theory (enable operand-stackp popn-operands))))

(defthm popn-operands-of-push-operand
  (implies (posp n)
           (equal (popn-operands n (push-operand item stack))
                  (popn-operands (+ -1 n) stack)))
  :hints (("Goal" :in-theory (enable popn-operands))))


;;
;; Helpers for java's "long" data type:
;;

;NOTE on longs/doubles: (fixme do these all apply to doubles as well as longs?)
;On the operand stack, longs (and, eventually, double floats?) are stored as two stack values, with the upper value being 0 and the lower value having all 64 bits of the data. (Presumably, it is not possible for an operation to split a long/double by accessing just half of it.)
;Instructions like DUP_X2 would not work right if we stored longs/doubles as single stack values.
;All stack operations on longs / doubles should use these functions:
;fixme make sure i am consistent about this usage

;; In the local variables of a frame, the entire long/double value is
;; stored in the first of the two local slots reserved for it.

;; TODO: Make these into functions:

;guard to require a non-empty-stack?
(defund top-long (stack)
  (declare (xargs :guard (operand-stackp stack) :guard-hints (("Goal" :in-theory (enable operand-stackp)))))
  (top-operand (pop-operand stack)))

;guard to require a non-empty-stack?
(defund pop-long (stack)
  (declare (xargs :guard (operand-stackp stack) :guard-hints (("Goal" :in-theory (enable operand-stackp)))))
  (pop-operand (pop-operand stack)))

(defthm operand-stackp-of-pop-long
  (implies (operand-stackp stack)
           (operand-stackp (pop-long stack)))
  :hints (("Goal" :in-theory (enable pop-long))))

(defthm operand-stack-size-of-pop-long
  (implies (< 1 (operand-stack-size stack))
           (equal (operand-stack-size (pop-long stack))
                  (+ -2 (operand-stack-size stack))))
  :hints (("Goal" :in-theory (enable pop-long; operand-stack-size
                                     ))))

(defund push-long (val stack)
  (declare (xargs :guard (operand-stackp stack) :guard-hints (("Goal" :in-theory (enable operand-stackp)))))
  (push-operand 0 (push-operand val stack)))

(defthm operand-stackp-of-push-long
  (equal (operand-stackp (push-long val stack))
         (operand-stackp stack))
  :hints (("Goal" :in-theory (enable push-long))))

(defthm operand-stack-size-of-push-long
  (equal (operand-stack-size (push-long obj stack))
         (+ 2 (operand-stack-size stack)))
  :hints (("Goal" :in-theory (enable push-long))))

(defthm top-long-of-push-long
  (equal (top-long (push-long val stack))
         val)
  :hints (("Goal" :in-theory (enable top-long push-long))))

(defthm pop-long-of-push-long
  (equal (pop-long (push-long val stack))
         stack)
  :hints (("Goal" :in-theory (enable pop-long push-long))))

;may be needed for instructions like DUP2 that break the stack typing abstraction wrt longs/doubles
(defthm pop-operand-of-pop-operand-of-push-long
  (equal (pop-operand (pop-operand (push-long val stack)))
         stack)
  :hints (("Goal" :in-theory (enable pop-long push-long))))

;;;
;;; Popping items off the stack, given a list of types
;;;

(defun pop-items-off-stack-aux (item-types ;; early ones correspond to shallower stack items
                                stack)
  (declare (xargs :guard (and (all-typep item-types)
                              (true-listp item-types)
                              (operand-stackp stack))))
  (if (endp item-types)
      stack
    (let* ((item-type (first item-types))
           (stack (if (member-eq item-type *two-slot-types*)
                      (pop-long stack)
                    (pop-operand stack))))
      (pop-items-off-stack-aux (rest item-types) stack))))

(defun pop-items-off-stack (rev-item-types ;; early ones correspond to deeper stack items
                            stack)
  (declare (xargs :guard (and (all-typep rev-item-types)
                              (true-listp rev-item-types)
                              (operand-stackp stack))))
  (pop-items-off-stack-aux (acl2::reverse-list rev-item-types) stack))

;;;
;;; If-lifting rules
;;;

;helps with lifting programs with conditional branches
(defthm top-operand-of-myif
  (equal (top-operand (myif test x y))
         (myif test (top-operand x) (top-operand y)))
  :hints (("Goal" :in-theory (enable myif))))

;helps with lifting programs with conditional branches
(defthm pop-operand-of-myif
  (equal (pop-operand (myif test x y))
         (myif test (pop-operand x) (pop-operand y)))
  :hints (("Goal" :in-theory (enable myif))))

;helps with lifting programs with conditional branches
(defthm top-long-of-myif
  (equal (top-long (myif test x y))
         (myif test (top-long x) (top-long y)))
  :hints (("Goal" :in-theory (enable myif))))

;helps with lifting programs with conditional branches
(defthm pop-long-of-myif
  (equal (pop-long (myif test x y))
         (myif test (pop-long x) (pop-long y)))
  :hints (("Goal" :in-theory (enable myif))))
