#|$ACL2s-Preamble$;

;;; Script for the ACL2 Workshop 2007
;;; Work of Rober Krug adapted to work with the most recent version
;;; of Destiny.
;;; Adaptation by Frank Rimlinger


;; We begin with Robert's model of Destiny.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; destiny-model.lisp
;;;
;;; We model those aspects of Destiny's JVM model that leak
;;; out into ACL2.
;;; We also define a few functions we will need for the
;;; bind-free rules that we will generate.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2")

#|
 We model:

 Predicates:
   array-p
   heap-p
   heap-counter-p
   stack-p
   static-area-p
   unknown-type-p
   boolean-p

 heap stuff:
   refh
   valueh
   pushh
   getstatic

 stack stuff:
   pushFrame --- formerly pushf
   popFrame --- formerly popf
   topFrame --- formerly topframe

 stack frame stuff:
   storeLocalVar1 --- formerly storelocalvar1
   storeCat2 --- formerly storelocalvar2
   getLocal --- formerly ???

   pushOpStack1 --- formerly pushop1
   pushCat2 --- formerly pushop2
   getOp
   popOp

We do all this inside an encapsulate, so that we can ensure that
ACL2 knows only waht it is supposed to about these functions.  We
do not care about executability.

This encapsulate runs through this file all the way to the section
of Bind-free stuff at the end.
|#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate ((stack-p (x) t)
          (frame-p (x) t)
              (static-area-p (x) t)
              (heap-p (x) t)
              (heap-counter-p (x) t)
          (array-p (name type arity) t)
          (boolean-p (x) t)
              (unknown-type-p (x) t)

              (refh (name subaddress) t)
              (valueh (ref heap) t)
              (pushh (ref value heap) t)
          (getstatic (x y) t)

              (pushFrame (frame stack) t)
              (popFrame (stack) t)
              (topFrame (stack) t)
              (storeLocalVar1 (var value frame) t)
              (storeCat2 (var value frame) t)
          (getLocal (offset frame) t)
              (pushOpStack1 (value frame) t)
              (pushCat2 (value frame) t)
              (getop (frame) t)
              (popop (frame) t)

              (ref-p (x) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Local definitions
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The main ones

(local
 (defun frame-p (x)
   ;; For present purposes, a frame consists of
   ;; an operand stack and a local variable array.
   ;; The operand stack is modeled as a simple push-down
   ;; stack, and the local variable array as a list with
   ;; the indices coresponding to position.
   (and (consp x)
    (true-listp (car x))
    (consp (cdr x))
    (true-listp (cadr x))
    (null (cddr x)))))

(local
 (defun stack-p (x)
   ;; The stack of call frames
   (cond ((equal x 'dummy-stack)
      t)
     ((null (cdr x))
      (frame-p (car x)))
     (t
      (and (frame-p (car x))
           (stack-p (cdr x)))))))

(local
 (defun static-area-p (x)
   (declare (ignore x))
   nil))

(local
 (defun heap-p (x)
   (alistp x)))

(local
 (defun heap-counter-p (x)
   (and (integerp x)
        (<= 0 x))))

(local
 (defun array-p (name type arity)
   (declare (ignore name type arity))
   nil))

(local
 (defun boolean-p (x)
   (declare (ignore x))
   t))

(local
 (defun unknown-type-p (x)
   (declare (ignore x))
   nil))

(local
 (defun refh (name subaddress)
   (list name subaddress)))

(local
 (defun valueh (ref heap)
   ;; Look up the value of ref in the heap
  (cdr (assoc-equal ref heap))))

(local
 (defun getstatic (x y)
   ;; ???
   (cons x y)))

(local
 (defun pushh (ref value heap)
   ;; Push the value of ref onto the heap
  (cons (cons ref value) heap)))

(local
 (defun pushFrame (frame stack)
   ;; push a frame onto the call stack
   (if (equal stack 'dummy-stack)
       (list frame)
     (cons frame stack))))

(local
 (defun popFrame (stack)
   ;; pop a frame from the call stack
   (cond ((equal stack 'dummy-stack)
      stack)
     ((null (cdr stack))
      'dummy-stack)
     (t
      (cdr stack)))))

(local
 (defun topFrame (stack)
   ;; get the top frame from the call stack
   (if (equal stack 'dummy-stack)
       '(() ())  ;;; The empty frame
     (car stack))))

(local
 (defun store-in-local-variable-array (value offset array)
   (if (zp offset)
       (cons value (cdr array))
     (cons (car array)
       (store-in-local-variable-array value
                      (+ -1 offset)
                      (cdr array))))))

(local
 (defthm true-listp-store-in-local-variable-array
   (implies (true-listp array)
        (true-listp (store-in-local-variable-array value offset array)))))

(local
 (defun storeLocalVar1 (value offset frame)
   ;; store a value in the local variable array
   (list (car frame)
     (store-in-local-variable-array value offset (cadr frame)))))

(local
 (defun storeCat2 (value offset frame)
   ;; store a value in the local variable array
   (list (car frame)
     (store-in-local-variable-array value offset (cadr frame)))))

(local
 (defun get-from-local-variable-array (offset array)
   (if (zp offset)
       (car array)
     (get-from-local-variable-array (+ -1 offset) (cdr array)))))

(local
 (defun getLocal (offset frame)
   ;; get a value from the local variable array
   (get-from-local-variable-array offset (cadr frame))))

(local
 (defun pushOpStack1 (value frame)
   ;; push a value onto the operand stack
   (list (cons value (car frame))
     (cadr frame))))

(local
 (defun pushCat2 (value frame)
   ;; push a value onto the operand stack
   (list (cons value (car frame))
     (cadr frame))))

(local
 (defun getOp (frame)
   ;; get a value from the operand stack
   (car (car frame))))

(local
 (defun popOp (frame)
   ;; pop a value from the operand stack
   ;; and return the new frame
   (list (cdr (car frame))
     (cadr frame))))

;;; Helper functions:

(local
 (defun ref-p (x)
   (declare (ignore x))
   t))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Simple theorems about types
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm booleanp-stack-p
  (booleanp (stack-p x)))

(defthm booleanp-frame-p
  (booleanp (frame-p x)))

(defthm booleanp-static-area-p
  (booleanp (static-area-p x)))

(defthm booleanp-heap-p
  (booleanp (heap-p x)))

(defthm booleanp-heap-counter-p
  (booleanp (heap-counter-p x)))

(defthm booleanp-array-p
  (booleanp (array-p name type arity)))

(defthm booleanp-boolean-p
  (booleanp (boolean-p x)))

(defthm booleanp-unknown-type-p
  (booleanp (unknown-type-p x)))

(defthm booleanp-ref-p
  (booleanp (ref-p x)))

(defthm ref-p-refh
  ;; This should be made stronger.
  ;; Is a name always a symbol?
  ;; What do subaddresses look like?
  (ref-p (refh name subaddress)))

(defthm heap-counter-p-incremented
  (implies (and (heap-counter-p nH)
        (integerp n)
        (<= 0 n))
       (heap-counter-p (+ n nH))))

;;; valueh returns a value.  Not much to say.

(defthm heap-p-pushh
  ;; Should we care about value?
  (implies (and (ref-p ref)
                (heap-p heap))
           (heap-p (pushh ref value heap))))

(defthm stack-p-dummy-stack
  (stack-p 'dummy-stack))

(defthm stack-p-pushFrame
  (implies (and (frame-p frame)
                (stack-p stack))
           (stack-p (pushFrame frame stack))))

(defthm stack-p-popFrame
  (implies (and (stack-p stack))
           (stack-p (popFrame stack))))

(defthm frame-p-topFrame
  (implies (stack-p stack)
           (frame-p (topFrame stack))))

(defthm frame-p-storeLocalVar1
  (implies (frame-p frame)
           (frame-p (storeLocalVar1 var value frame))))

(defthm frame-p-storeCat2
  (implies (frame-p frame)
           (frame-p (storeCat2 var value frame))))

(defthm frame-p-pushOpStack1
  (implies (frame-p frame)
           (frame-p (pushOpStack1 value frame))))

(defthm frame-p-pushCat2
  (implies (frame-p frame)
           (frame-p (pushCat2 value frame))))

(defthm frame-p-popop
  (implies (frame-p frame)
           (frame-p (popop frame))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; storeLocalVar1, storeCat2, getLocal
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
(defthm foo
  (IMPLIES (AND (TRUE-LISTP FRAME3)
              (INTEGERP OFFSET1)
              (<= 0 OFFSET1))
         (EQUAL (GET-FROM-LOCAL-VARIABLE-ARRAY
                     OFFSET1
                     (STORE-IN-LOCAL-VARIABLE-ARRAY VALUE OFFSET1 FRAME3))
                VALUE))))

(defthm getLocal-storeLocalVar1-same
  (implies (and (frame-p frame)
        (integerp offset1)
        (<= 0 offset1)
        (integerp offset2)
        (<= 0 offset2)
        (equal offset1 offset2))
       (equal (getLocal offset2 (storeLocalVar1 value offset1 frame))
          value)))

(defthm getLocal-storeCat2-same
  (implies (and (frame-p frame)
        (integerp offset1)
        (<= 0 offset1)
        (integerp offset2)
        (<= 0 offset2)
        (equal offset1 offset2))
       (equal (getLocal offset2 (storeCat2 value offset1 frame))
          value)))

(local
(defthm bar
  (IMPLIES (AND (TRUE-LISTP FRAME3)
              (INTEGERP OFFSET1)
              (<= 0 OFFSET1)
              (INTEGERP OFFSET2)
              (<= 0 OFFSET2)
              (NOT (EQUAL OFFSET1 OFFSET2)))
         (EQUAL (GET-FROM-LOCAL-VARIABLE-ARRAY
                     OFFSET2
                     (STORE-IN-LOCAL-VARIABLE-ARRAY VALUE OFFSET1 FRAME3))
                (GET-FROM-LOCAL-VARIABLE-ARRAY OFFSET2 FRAME3)))))

(defthm getLocal-storeLocalVar1-different
  (implies (and (frame-p frame)
        (integerp offset1)
        (<= 0 offset1)
        (integerp offset2)
        (<= 0 offset2)
        (not (equal offset1 offset2)))
       (equal (getLocal offset2 (storeLocalVar1 value offset1 frame))
          (getLocal offset2 frame))))

(defthm getLocal-storeCat2-different
  (implies (and (frame-p frame)
        (integerp offset1)
        (<= 0 offset1)
        (integerp offset2)
        (<= 0 offset2)
        (not (equal offset1 offset2)))
       (equal (getLocal offset2 (storeCat2 value offset1 frame))
          (getLocal offset2 frame))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; pushOpStack1, pushCat2, getOp, popOp
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm getOp-pushOpStack1
  (implies (frame-p frame)
       (equal (getOp (pushOpStack1 value frame))
          value)))

(defthm getOp-pushCat2
  (implies (frame-p frame)
       (equal (getOp (pushCat2 value frame))
          value)))

(defthm popOp-pushOpStack1
  (implies (frame-p frame)
       (equal (popOp (pushOpStack1 value frame))
          frame)))

(defthm popOp-pushCat2
  (implies (frame-p frame)
       (equal (popOp (pushCat2 value frame))
          frame)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; getOp, popOp
;;; commute with
;;; storeLocalVar1, storeCat2
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm getOp-storeLocalVar1
  (implies (and (frame-p frame)
        (integerp offset)
        (<= 0 offset))
       (equal (getOp (storeLocalVar1 value offset frame))
          (getOp frame))))

(defthm getOp-storeCat2
  (implies (and (frame-p frame)
        (integerp offset)
        (<= 0 offset))
       (equal (getOp (storeCat2 value offset frame))
          (getOp frame))))

(defthm popOp-storeLocalVar1
  (implies (and (frame-p frame)
        (integerp offset)
        (<= 0 offset))
       (equal (popOp (storeLocalVar1 value offset frame))
          (storeLocalVar1 value offset (popOp frame)))))

(defthm popOp-storeCat2
  (implies (and (frame-p frame)
        (integerp offset)
        (<= 0 offset))
       (equal (popOp (storeCat2 value offset frame))
          (storeCat2 value offset (popOp frame)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; getLocal
;;; commutes with
;;; pushOpStack1, pushCat2, popOp
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm getLocal-pushOpStack1
  (implies (and (frame-p frame)
        (integerp offset)
        (<= 0 offset))
       (equal (getLocal offset (pushOpStack1 value frame))
          (getLocal offset frame))))

(defthm getLocal-pushCat2
  (implies (and (frame-p frame)
        (integerp offset)
        (<= 0 offset))
       (equal (getLocal offset (pushCat2 value frame))
          (getLocal offset frame))))

(defthm getLocal-popOp
  (implies (and (frame-p frame)
        (integerp offset)
        (<= 0 offset))
       (equal (getLocal offset (popOp frame))
          (getLocal offset frame))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; pushFrame, popFrame, topFrame
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm popFrame-pushFrame
  (implies (and (frame-p frame)
                (stack-p stack))
           (equal (popFrame (pushFrame frame stack))
                  stack)))

(defthm topFrame-pushFrame
  (implies (and (frame-p frame)
                (stack-p stack))
           (equal (topFrame (pushFrame frame stack))
                  frame)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; pushh, valueh, refh
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; RBK: Note
;;; I would like to add some heap-p and ref-p hyps to
;;; the below theorems, but I do not see how to easily
;;; prove the meta-theorem ``good'' below in that case.

(defthm valueh-pushh-same
  (implies (and (equal ref1 ref2))
           (equal (valueh ref2 (pushh ref1 value heap))
                  value)))

(defthm valueh-pushh-different
  (implies (and (not (equal ref1 ref2)))
           (equal (valueh ref2 (pushh ref1 value heap))
                  (valueh ref2 heap))))

(defthm refh-equal
  (equal (equal (refh x1 y1) (refh x2 y2))
         (and (equal x1 x2)
              (equal y1 y2))))

(defthm refh-not-equal-1
  (implies (not (equal x1 x2))
       (not (equal (refh x1 y1)
               (refh x2 y2)))))

(defthm refh-not-equal-2
  (implies (not (equal y1 y2))
       (not (equal (refh x1 y1)
               (refh x2 y2)))))


)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; pushh, valueh, refh meta rule
;;;
;;; We strip out irrelevant PUSHH
;;; expressions from the heap.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defevaluator evl evl-list
   ((pushh ref value heap)
    (valueh ref heap)
    (refh x y)
    (not x)
    (equal x y)
    (if x y z)))

(set-state-ok t)

(defun find-to-remove-1 (value-ref heap mfc state)
  (declare (xargs :guard t))
  (case-match heap
    (('PUSHH push-ref
         value
         h)
     (declare (ignore value))
     (if (equal (mfc-rw `(NOT (EQUAL ,value-ref ,push-ref))
            t t mfc state)
        *t*)
     push-ref
       (find-to-remove-1 value-ref h mfc state)))
    (&
     nil)))

(defun find-to-remove (x mfc state)
  (declare (xargs :guard t))
  (case-match x
    (('VALUEH ref
          h)
     (find-to-remove-1 ref h mfc state))
    (&
     x)))

(defun remove-pushh-1 (remove heap)
  (declare (xargs :guard t))
  (case-match heap
    (('PUSHH !remove
         value
         h)
     (declare (ignore value))
     h)
    (('PUSHH other
         value
         h)
     (list 'PUSHH other value (remove-pushh-1 remove h)))
    (&
     heap)))

(defun remove-pushh (x mfc state)
  (declare (xargs :guard t))
  (let ((remove (find-to-remove x mfc state)))
    (if remove
    (case-match x
      (('VALUEH ref
            h)
       `(IF (NOT (EQUAL ,remove ,ref))
        (VALUEH ,ref
            ,(remove-pushh-1 remove h))
        ,x))
      (&
       x))
      x)))

(local
(defthm remove-pushh-1-meta-thm
(IMPLIES
     (NOT (EQUAL (EVL remove
                           A)
                      (EVL X3 A)))
     (EQUAL (VALUEH (EVL X3 A) (EVL X5 A))
            (VALUEH (EVL X3 A)
                    (EVL (REMOVE-PUSHH-1 remove
                                         X5)
                         A))))
:hints (("Subgoal *1/2'5'" :cases ((equal (EVL X3 A) (EVL X8 A)))))
:rule-classes nil))

(defthm remove-pushh-good
      (equal (evl x a)
         (evl (remove-pushh x mfc state) a))
 :hints (("Goal" :in-theory (disable find-to-remove))
     ("Goal'5'" :use (:instance remove-pushh-1-meta-thm
                    (remove (FIND-TO-REMOVE (LIST 'VALUEH X3 X5)
                                                         MFC STATE)))))
 :rule-classes ((:meta :trigger-fns (valueh))))



#|

(defun definition-<_1 (v1 v2 v3)
       (< v1
          (valueh (refh v2 'array_length_marker)
                  v3)))

(defevaluator evl-1 evl-list-1
   ((pushh ref value heap)
    (valueh ref heap)
    (refh x y)
    (not x)
    (equal x y)
    (if x y z)
    (definition-<_1 x y z)))

(set-ignore-ok t)

(defun find-to-remove-definition-<_1 (x mfc state)
  (case-match x
    (('DEFINITION-<_1 v1 v2 h)
     (find-to-remove-1 `(REFH ,v2 'ARRAY_LENGTH_MARKER) h mfc state))
    (&
     x)))

(defun remove-pushh-definition-<_1 (x mfc state)
  (let ((remove (find-to-remove-definition-<_1 x mfc state)))
    (if remove
    (case-match x
      (('DEFINITION-<_1 v1 v2 h)
       `(IF (NOT (EQUAL ,remove (REFH ,v2 'ARRAY_LENGTH_MARKER)))
        (DEFINITION-<_1 ,v1 ,v2
            ,(remove-pushh-1 remove h))
        ,x))
      (&
       x))
      x)))

(defthm foo
  (IMPLIES
 (AND
  remove
  (NOT
   (EQUAL
        (EVL-1 remove
               A)
        (REFH (EVL-1 X5 A)
              'ARRAY_LENGTH_MARKER))))
 (EQUAL
  (< (EVL-1 X3 A)
     (VALUEH (REFH (EVL-1 X5 A) 'ARRAY_LENGTH_MARKER)
             (EVL-1 X7 A)))
  (<
   (EVL-1 X3 A)
   (VALUEH
     (REFH (EVL-1 X5 A) 'ARRAY_LENGTH_MARKER)
     (EVL-1
          (REMOVE-PUSHH-1
               remove
               X7)
          A)))))
  :hints (("Subgoal *1/2'5'" :cases ((equal (REFH (EVL-1 X5 A) 'ARRAY_LENGTH_MARKER)
                        (EVL-1 X10 A)))))
  :rule-classes nil)

(defthm remove-pushh-definition-<_1-good
      (equal (evl-1 x a)
         (evl-1 (remove-pushh-definition-<_1 x mfc state) a))
 :hints (("Goal" :in-theory (disable find-to-remove-definition-<_1))
     ("Goal'5'" :use (:instance foo
                    (remove (FIND-TO-REMOVE-DEFINITION-<_1 (LIST 'DEFINITION-<_1 X3 X5 X7)
                                              MFC STATE)))))
 :rule-classes ((:meta :trigger-fns (definition-<_1))))

|#


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; A bunch of JVM functions
;;;
;;; We want to know nothing about them
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstub runtimeexception (x y z) t)

(defstub buildabstractsym (x) t)

(defstub getvirtualruntimeexception (x y) t)

(defstub getcomponenttype (x) t)

(defstub stringappend (x y) t)

(defstub is_class_loadable (x) t)

(defstub strip_object (x) t)

(defstub isprimitiveclass (x) t)

; (defstub arraylength (x y) t)

(defstub makeclassptr (x) t)

(defstub arraytypeasstring (x y) t)

(defstub notprimitive (x) t)

(defstub arrayclassref (x y) t)

(defstub classname (x y z) t)

(defstub componenttype (x y z) t)

(defstub runtimeexceptionsynthetic (x y) t)

(defstub buildabstractsymsynthetic (x y) t)

(defstub arraytype (x y) t)

(defstub loadablearray (x y) t)

(defstub getvirtualruntimemethod (x y) t)

(defstub makestr (x) t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Guard violation and type violation
;;; dummy functions
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstub gv-0 () t)

(defstub gv-1 () t)

(defstub gv-2 () t)

(defstub gv-3 () t)

(defstub gv-4 () t)

(defstub gv-5 () t)

(defstub gv-6 () t)

(defstub gv-7 () t)

(defstub gv-8 () t)

(defstub gv-9 () t)

(defstub gv-10 () t)

(defstub gv-11 () t)

(defstub gv-12 () t)

(defstub gv-13 () t)

(defstub gv-14 () t)

(defstub gv-15 () t)

(defstub gv-16 () t)

(defstub gv-17 () t)

(defstub gv-18 () t)

(defstub gv-19 () t)

(defstub gv-20 () t)

(defstub gv-21 () t)

(defstub gv-22 () t)

(defstub gv-23 () t)

(defstub gv-24 () t)

(defstub gv-25 () t)

(defstub gv-26 () t)

(defstub gv-27 () t)

(defstub gv-28 () t)

(defstub gv-29 () t)

(defstub gv-30 () t)

(defstub gv-31 () t)

(defstub gv-32 () t)

(defstub gv-33 () t)

(defstub gv-34 () t)

(defstub gv-35 () t)

(defstub gv-36 () t)

(defstub gv-37 () t)

(defstub gv-38 () t)

(defstub gv-39 () t)

(defstub tv-0 () t)

(defstub tv-1 () t)

(defstub tv-2 () t)

(defstub tv-3 () t)

(defstub tv-4 () t)

(defstub tv-5 () t)

(defstub tv-6 () t)

(defstub tv-7 () t)

(defstub tv-8 () t)

(defstub tv-9 () t)

(defstub tv-10 () t)

(defstub tv-11 () t)

(defstub tv-12 () t)

(defstub tv-13 () t)

(defstub tv-14 () t)

(defstub tv-15 () t)

(defstub tv-16 () t)

(defstub tv-17 () t)

(defstub tv-18 () t)

(defstub tv-19 () t)

(defstub tv-20 () t)

(defstub tv-21 () t)

(defstub tv-22 () t)

(defstub tv-23 () t)

(defstub tv-24 () t)

(defstub tv-25 () t)

(defstub tv-26 () t)

(defstub tv-27 () t)

(defstub tv-28 () t)

(defstub tv-29 () t)

(defstub tv-30 () t)

(defstub tv-31 () t)

(defstub tv-32 () t)

(defstub tv-33 () t)

(defstub tv-34 () t)

(defstub tv-35 () t)

(defstub tv-36 () t)

(defstub tv-37 () t)

(defstub tv-38 () t)

(defstub tv-39 () t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Expand hint
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun package-witness ()
  t)

(defun intern-name (lst)
  (declare (xargs :mode :program))
  (acl2::intern-in-package-of-symbol (coerce (acl2::packn1 lst) 'string)
                                     'package-witness))

(defun all-vars-quoteps-or-heaps (args)
  (cond ((atom args)
     t)
    ((or (atom (car args))
         (quotep (car args))
         (equal (car (car args)) 'PUSHH)
         (equal (car (car args)) 'PUSHFRAME))
     (all-vars-quoteps-or-heaps (cdr args)))
    (t
     nil)))

(mutual-recursion

 (defun find-expand-term-list (term-list name)
   (if (atom term-list)
       nil
     (let ((ans (find-expand-term-term (car term-list) name)))
       (if ans
       ans
     (find-expand-term-list (cdr term-list) name)))))

 (defun find-expand-term-term (term name)
   (cond ((atom term)
      nil)
     ((and (equal (car term) name)
           (all-vars-quoteps-or-heaps (cdr term)))
      term)
     (t
      (find-expand-term-list (cdr term) name))))

)


(defun find-expand-term-clause (clause name)
  (find-expand-term-term (car (last clause)) name))

#|
(defun find-expand-term-clause (clause name)
  (if (endp clause)
      nil
    (let ((ans (find-expand-term-term (car clause) name)))
      (if ans
      ans
    (find-expand-term-clause (cdr clause) name)))))
|#

;;; (destiny-expand-hint <name>) will cause ACL2 to expand a call to
;;; the function <name> if:
;;; 1. We are inducting
;;; 2. We are stable-under-simplificationp
;;; 3. and all the arguments to <name> are variables, quoteps, or heaps.

;;; Another strategy that might be considered is to examine the measure
;;; associated with <name> and see if the instantiated measure under
;;; the call being considered can be rewritten to a constant.  This would
;;; require some work to put together, but is probably closer to what we
;;; really want.  For instance, if the measure for (foo x n i) is
;;; (nfix (- n i)), the calls (foo x 5 3) and (foo x (+ n 2) n) could both
;;; be expanded but (foo x n i) would not be.

(defmacro destiny-expand-hint (name)
  (let ((fn-name (intern-name (list (cadr name) "-expand-hint"))))
    `(PROGN
      (DEFUN ,fn-name (ID CLAUSE WORLD STABLE-UNDER-SIMPLIFICATIONP HIST PSPV CTX)
    (DECLARE (IGNORE HIST CTX))
    (DECLARE (XARGS :MODE :PROGRAM))
    (IF (AND (CDAR ID)
         STABLE-UNDER-SIMPLIFICATIONP
         (ENABLED-RUNEP `(:DEFINITION ,,name)
                   (ACCESS REWRITE-CONSTANT
                       (ACCESS PROVE-SPEC-VAR PSPV :REWRITE-CONSTANT)
                       :CURRENT-ENABLED-STRUCTURE)
                   WORLD))
        (LET ((EXPAND-TERM (FIND-EXPAND-TERM-CLAUSE CLAUSE ,name)))
          (IF EXPAND-TERM
          `(:COMPUTED-HINT-REPLACEMENT T
            :EXPAND (,EXPAND-TERM ))
        NIL))
      NIL))
      (ADD-DEFAULT-HINTS '((,fn-name ID CLAUSE WORLD STABLE-UNDER-SIMPLIFICATIONP HIST PSPV CTX))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Bind-free stuff
;;;
;;; This is used by the xxx-mv-nth-<n>-is-irrelevant-to-mv-nth-<m>
;;; theorems guessed by the parser.  The idea is to find a cononical
;;; representation for these (mv-nth n (xxx <args>)) in which the
;;; mth arg is standardized.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-state-ok t)

(defun destiny-rewriting-goal-literal (mfc state)
  (declare (ignore state))
  (null (access metafunction-context mfc :ancestors)))

(defun assemble-answer (irrelevant-poss to-bind-list arg-list)
  (if (endp to-bind-list)
      nil
    (cons (cons (car to-bind-list)
        (nth (car irrelevant-poss) arg-list))
      (assemble-answer (cdr irrelevant-poss)
               (cdr to-bind-list)
               arg-list))))

(defun vars-match (term-vars target-vars irrelevant-poss i)
  (cond ((endp term-vars)
     t)
    ((member-equal i irrelevant-poss)
     (vars-match (cdr term-vars) (cdr target-vars) irrelevant-poss (+ i 1)))
    ((equal (car term-vars) (car target-vars))
     (vars-match (cdr term-vars) (cdr target-vars) irrelevant-poss (+ i 1)))
    (t
     nil)))

(defun not-all-vars-match (term-vars target-vars)
  (cond ((endp term-vars)
     nil)
    ((equal (car term-vars) (car target-vars))
     (not-all-vars-match (cdr term-vars) (cdr target-vars)))
    (t
     t)))

;;; RBK: I would like this to be in logic mode, but term-order is in program mode.

(mutual-recursion

(defun var-from-matches-up-to-irrelevant-poss (term mv-nth-pos fn-name args irrelevant-poss)
  (declare (xargs :mode :program))
  ;; If target matches with a sub-expresion of term, we return the value
  ;; in the irrelevant-poss.
  (cond ((atom term)
     nil)
    ((and (equal (car term) 'NTH)
          (equal (cadr (cadr term)) mv-nth-pos)  ;; strip the quote off
          (equal (car (caddr term)) fn-name)
          (vars-match (cdr (caddr term)) args irrelevant-poss 0)
          (not-all-vars-match (cdr (caddr term)) args)
          (term-order (cdr (caddr term)) args))
     (cdr (caddr term)))
    (t
     (var-from-matches-up-to-irrelevant-poss-lst (cdr term) mv-nth-pos fn-name args irrelevant-poss))))

(defun var-from-matches-up-to-irrelevant-poss-lst (term-lst mv-nth-pos fn-name args irrelevant-poss)
  (declare (xargs :mode :program))
  (if (endp term-lst)
      nil
    (let ((ans (var-from-matches-up-to-irrelevant-poss (car term-lst) mv-nth-pos fn-name args irrelevant-poss)))
      (if ans
      ans
    (var-from-matches-up-to-irrelevant-poss-lst (cdr term-lst) mv-nth-pos fn-name args irrelevant-poss)))))

)

(defun destiny-bind-irrelevant-var-1 (clause fn-name irrelevant-poss mv-nth-pos args to-bind-list ans)
  (declare (xargs :mode :program))
  (if (endp clause)
      (if ans
      (assemble-answer irrelevant-poss to-bind-list ans)
    nil)
    (let ((binding (var-from-matches-up-to-irrelevant-poss (car clause) mv-nth-pos fn-name args irrelevant-poss)))
      (cond ((and binding
          (null ans)
          (term-order binding args))
         (destiny-bind-irrelevant-var-1 (cdr clause) fn-name irrelevant-poss mv-nth-pos args to-bind-list binding))
        ((and binding
          ans
          (term-order binding ans))  ;;(< (acl2-count binding) (acl2-count ans)))
         (destiny-bind-irrelevant-var-1 (cdr clause) fn-name irrelevant-poss mv-nth-pos args to-bind-list binding))
        (t
         (destiny-bind-irrelevant-var-1 (cdr clause) fn-name irrelevant-poss mv-nth-pos args to-bind-list ans))))))

(defun destiny-bind-irrelevant-vars (fn-name irrelevant-poss mv-nth-pos args to-bind-list mfc state)
  (declare (xargs :mode :program))
  (declare (ignore state))
  (let ((clause (mfc-clause mfc))
    (ans nil))
    (destiny-bind-irrelevant-var-1 clause fn-name irrelevant-poss mv-nth-pos args to-bind-list ans)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Include the arithmetic-3 books, and a couple of extra theorems:

(defthm integerp-is-rationalp
  (implies (integerp x)
       (rationalp x)))

(defthm rationalp-is-acl2-numberp
  (implies (rationalp x)
       (acl2-numberp x)))


;;; (include-book "Applications/ACL2/v3-1/acl2-sources/books/arithmetic-3/bind-free/top" :dir :system)

;;; (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system)

;;; (defthm truncate-to-floor
;;;   (implies (and (integerp x)
 ;;;        (integerp y))
 ;;;       (equal (truncate x y)
 ;;;          (cond ((or (and (<= 0 x) (<= 0 y))
 ;;;                 (and (<= x 0) (<= y 0)))
  ;;;            (floor x y))
  ;;;           ((integerp (/ x y))
 ;;;            (floor x y))
 ;;;            (t
 ;;;             (+ 1 (floor x y))))))
 ;;;  :hints (("Goal" :in-theory (e/d (floor) (nonnegative-integer-quotient))))
;;;  :otf-flg t)

;;; (defthm rem-to-mod
;;;   (implies (and (integerp x)
 ;;;        (integerp y))
 ;;;       (equal (rem x y)
 ;;;          (cond ((or (and (<= 0 x) (<= 0 y))
 ;;;                 (and (<= x 0) (<= y 0)))
 ;;;             (mod x y))
 ;;;            ((integerp (/ x y))
 ;;;             (mod x y))
 ;;;            (t
 ;;;             (- (mod x y) y)))))
 ;;;  :hints (("Goal" :in-theory (e/d (mod) (truncate))))
 ;;;  :otf-flg t)
;;;
;;; (in-theory (disable truncate rem))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; We conclude with a few axioms.  These should be made defthms some
;;; day.

;; frank commented these axioms out in order to certify and make a book

#|
(defaxiom makeclassptr-returns-a-heap-counter-p
  (heap-counter-p (makeclassptr x)))

(defaxiom booleanp-0
  (boolean-p 0))

(defaxiom booleanp-1
  (boolean-p 1))

(defaxiom array-p-null-type
  (array-p 'NULL x y))

(defstub in-the-past (x) t)

(defaxiom makeclassptr-is-not-in-the-past
  (not (in-the-past (MAKECLASSPTR x))))

(defstub in-the-present (x) t)

(defaxiom makeclassptr-is-not-in-the-present
  (not (in-the-present (MAKECLASSPTR x))))

(defstub primitive-instantiated-heap-pointer (x) t)

(defaxiom in-the-present-primitive-instantiated-heap-pointer
  (implies (primitive-instantiated-heap-pointer v-nh)
       (in-the-present v-nh)))

(defaxiom in-the-present-primitive-instantiated-heap-pointer-+-n
  (implies (and (primitive-instantiated-heap-pointer v-nh)
        (integerp n)
        (<= 0 n))
       (in-the-present (+ n v-nh))))

(defaxiom in-the-past-not-in-the-past-is-not-equal-1
  (implies (and (in-the-past x)
        (not (in-the-past y)))
       (not (equal x y))))

(defaxiom in-the-past-not-in-the-past-is-not-equal-2
  (implies (and (not (in-the-past x))
        (in-the-past y))
       (not (equal x y))))

(defaxiom in-the-present-not-in-the-present-is-not-equal-1
  (implies (and (in-the-present x)
        (not (in-the-present y)))
       (not (equal x y))))

(defaxiom in-the-present-not-in-the-present-is-not-equal-2
  (implies (and (not (in-the-present x))
        (in-the-present y))
       (not (equal x y))))

(defaxiom in-the-past-is-not-in-the-present
  (implies (in-the-past x)
       (not (in-the-present x))))

(defaxiom in-the-present-is-not-in-the-past
  (implies (in-the-present x)
       (not (in-the-past x))))

(defaxiom stringappend-def
  (equal (stringappend x y)
     (string-append x y)))

(defaxiom not-equal-implies-not-equal-makeclassptr
  (implies (not (equal x y))
       (not (equal (makeclassptr x) (makeclassptr y)))))

(defaxiom array-p-implies-heap-counter-p
  (implies (ARRAY-P x y z)
       (heap-counter-p x)))

|#



#|

ACL2 analysis for "itsAWrap".
This analysis is adapted from the original work of Robert Krug,
and is based upon a slightly modified version of his "destiny-model"
file.

The first step is to map the itsAWrap loop module hypotheses to ACL2.  Because
of certain syntax issues, changes are made to both Robert's destiny-model
and the Destiny rules.

Changes to destiny-model:

storecat1 -->     storeLocalVar1
pushcat1  -->     pushOpStack1
getframe  -->     topFrame


Changes to destiny output:

All the "@" symbols are suppressed.  Addtionally,

nH         <--- @#0
popFrame   <--- pop
pushFrame  <--  push
X          <--- (putOpStack  X stack)
(popop X)  <--- (popOpStack (getOpStack X))

|#


(set-ignore-ok t)
(set-match-free-default :all)

; Definitions expressing the hypotheses for the loop module of itsAWrap
(defun |'x' is defined| (x) (not (= x 'null)))

(defun |'op0' is less than 10| (op0) ( < op0 10 ))

(defun |'i' is greater than or equal to 0| (i) (not (< i 0)))

(defun | 'i' is less than length of the Array 'x'|
  (i x inputHeap)
  (< i
     (valueH
      (refH x 'array_length_marker)
      inputHeap)))

; The guard conditions are from the type information generated by Destiny.
; The loop condition is the conjunction of the set of itsAWrap loop module hypotheses.
; Aside from the measure, we also have to tell ACL2 that i==op0.
; (In Destiny this fact is hidden away in one of the invariants for the loop module.)
; The recursive call is taken from the case "function" rule within Destiny.
; In the event of multiple cases, the loop expression becomes a nested if.

;; NOTE: A stricter translation from Destiny of the clearLoop defintiion would
;; involve two stack parameters, a dummy parameter and the "real" stack. For
;; simplicity we work here just with the "real" stack.

(defun clearLoop (x i op0 inputHeap nH inputStack inputStaticArea)
  (declare (xargs :measure (nfix (- 10 i))))
  (if
    (and (integerp i)
         (integerp op0)
         (array-p x 'int 1)
         (static-area-p inputStaticArea)
         (stack-p inputStack)
         (heap-counter-p nh)
         (heap-p inputHeap)
         (= i op0))
    (if
      (and
       (|'x' is defined| x)
       (|'op0' is less than 10| op0)
       (|'i' is greater than or equal to 0| i)
       (| 'i' is less than length of the Array 'x'|
        i x inputHeap))
      (clearLoop x (+ 1 i) (+ i 1) (pushH (refH x i) 0 inputHeap) nH

                 (pushFrame
                  (storeLocalVar1
                   (+ i 1 )
                   1
                   (storeLocalVar1
                    x
                    0
                    (pushOpStack1
                     (+ i 1 )
                     (popop
                      (topFrame inputStack )))))
                  (popFrame  inputStack ))
                 inputStaticArea)
      (mv x i op0 inputHeap nH inputStack inputStaticArea))
    (mv
     (tv-6)
     (tv-5)
     (tv-4)
     (tv-3)
     (tv-2)
     (tv-1)
     (tv-0))))

(destiny-expand-hint 'clearLoop)

; Theorems giving the type information for the non-invariant parameters,
; namely, i, op0, inputHeap, and inputStack

(defthm clearLoop-1-return-type
  (implies   (and (integerp i)
                  (integerp op0)
                  (array-p x 'int 1)
                  (static-area-p inputStaticArea)
                  (stack-p inputStack)
                  (heap-counter-p nh)
                  (heap-p inputHeap)
                  (= i op0))
             (integerp (mv-nth 1 (clearLoop x i op0 inputHeap nH inputStack inputStaticArea))))
  )

(defthm clearLoop-2-return-type
  (implies   (and (integerp i)
                  (integerp op0)
                  (array-p x 'int 1)
                  (static-area-p inputStaticArea)
                  (stack-p inputStack)
                  (heap-counter-p nh)
                  (heap-p inputHeap)
                  (= i op0))
             (integerp (mv-nth 2 (clearLoop x i op0 inputHeap nH inputStack inputStaticArea))))
  )

(defthm clearLoop-3-return-type
  (implies   (and (integerp i)
                  (integerp op0)
                  (array-p x 'int 1)
                  (static-area-p inputStaticArea)
                  (stack-p inputStack)
                  (heap-counter-p nh)
                  (heap-p inputHeap)
                  (= i op0))
             (heap-p (mv-nth 3 (clearLoop x i op0 inputHeap nH inputStack inputStaticArea)))))

(defthm clearLoop-5-return-type
  (implies   (and (integerp i)
                  (integerp op0)
                  (array-p x 'int 1)
                  (static-area-p inputStaticArea)
                  (stack-p inputStack)
                  (heap-counter-p nh)
                  (heap-p inputHeap)
                  (= i op0))
             (stack-p (mv-nth 5 (clearLoop x i op0 inputHeap nH inputStack inputStaticArea)))))

; Theorems expression the invariance of x, nH, inputStaticArea

(defthm clearLoop-0-invariant
  (implies   (and (integerp i)
                  (integerp op0)
                  (array-p x 'int 1)
                  (static-area-p inputStaticArea)
                  (stack-p inputStack)
                  (heap-counter-p nh)
                  (heap-p inputHeap)
                  (= i op0))
             (= (car (clearLoop x i op0 inputHeap nH inputStack inputStaticArea))x)))


(defthm clearLoop-4-invariant
  (implies   (and (integerp i)
                  (integerp op0)
                  (array-p x 'int 1)
                  (static-area-p inputStaticArea)
                  (stack-p inputStack)
                  (heap-counter-p nh)
                  (heap-p inputHeap)
                  (= i op0))
             (= (mv-nth 4 (clearLoop x i op0 inputHeap nH inputStack inputStaticArea))nH)))

(defthm clearLoop-6-invariant
  (implies   (and (integerp i)
                  (integerp op0)
                  (array-p x 'int 1)
                  (static-area-p inputStaticArea)
                  (stack-p inputStack)
                  (heap-counter-p nh)
                  (heap-p inputHeap)
                  (= i op0))
             (= (mv-nth 6 (clearLoop x i op0 inputHeap nH inputStack inputStaticArea))inputStaticArea)))

; Now Robert adds defintions required to capture the notion that the stack and
; static area are irrelevant to the inductive reasoning.  These definition "double-up" their
; respective target variable to facilitate the comparison of different possible values in the
; corresponding theorem below.

; (It is of course not always the case that the stack and/or static area is irrelevant.)

(defun
  clearLoop-induction-fn-stack
  (x i op0 inputHeap nH stack-1 stack-2 inputStaticArea)
  (declare (xargs :measure (nfix (- 10 i))))
  (if
    (and  (integerp i)
          (integerp op0)
          (array-p x 'int 1)
          (static-area-p inputStaticArea)
          (stack-p stack-1)
          (stack-p stack-2)
          (heap-counter-p nh)
          (heap-p inputHeap)
          (= i op0))
    (if
      (and
       (|'x' is defined| x)
       (|'op0' is less than 10| op0)
       (|'i' is greater than or equal to 0| i)
       (| 'i' is less than length of the Array 'x'|
        i x inputHeap))
      ( clearLoop-induction-fn-stack x (+ 1 i) (+ i 1) (pushH (refH x i) 0 inputHeap) nH

                                     (pushFrame
                                      (storeLocalVar1
                                       (+ i 1 )
                                       1
                                       (storeLocalVar1
                                        x
                                        0
                                        (pushOpStack1
                                         (+ i 1 )
                                         (popop
                                          (topFrame stack-1 )))))
                                      (popFrame  stack-1 ))
                                     (pushFrame
                                      (storeLocalVar1
                                       (+ i 1 )
                                       1
                                       (storeLocalVar1
                                        x
                                        0
                                        (pushOpStack1
                                         (+ i 1 )
                                         (popop
                                          (topFrame stack-2)))))
                                      (popFrame  stack-2))
                                     inputStaticArea)
      t)
    t))


(defun clearLoop-induction-fnh-1stack-1x-8i-8 (x i op0 inputHeap nH-1 nH-2 stack inputStaticArea-1 inputStaticArea-2)
  (declare (xargs :measure (nfix (- 10 i))))
  (if
    (and (integerp i)
         (integerp op0)
         (array-p x 'int 1)
         (static-area-p inputStaticArea-1)
         (static-area-p inputStaticArea-2)
         (stack-p stack)
         (heap-counter-p nh-1)
         (heap-counter-p nh-2)
         (heap-p inputHeap)
         (= i op0))
    (if
      (and
       (|'x' is defined| x)
       (|'op0' is less than 10| op0)
       (|'i' is greater than or equal to 0| i)
       (| 'i' is less than length of the Array 'x'|
        i x inputHeap))
      (clearLoop-induction-fnh-1stack-1x-8i-8 x (+ 1 i) (+ i 1) (pushH (refH x i) 0 inputHeap) nH-1 nH-2
                                              stack inputStaticArea-1 inputStaticArea-2)
      (mv x i op0 inputHeap nH-1 nH-2 stack inputStaticArea-1 inputStaticArea-2))
    (mv
     (tv-8)
     (tv-7)
     (tv-6)
     (tv-5)
     (tv-4)
     (tv-3)
     (tv-2)
     (tv-1)
     (tv-0))))

(set-ignore-ok t)
(set-match-free-default :all)



; The next set of theorems characterize the fact that the inputStack is irrelevant to the
; determination of the other output values, namely x, i, inputHeap, nH, and inputStaticArea.
; In other words, the inputStack might just have well been the 'dummy-stack.

(encapsulate
 nil
 (local
  (defthm
    clearLoop-stack-is-irrelevant-to-mv-nth-0-helper
    (implies (and (stack-p stack-1)
                  (stack-p stack-2))
             (equal (mv-nth 0 (clearLoop x i op0 inputHeap nH stack-1 inputStaticArea))
                    (mv-nth 0 (clearLoop x i op0 inputHeap nH stack-2 inputStaticArea))))
    :hints
    (("GOAL"
          :induct
          (clearLoop-induction-fn-stack x i op0 inputHeap nH stack-1 stack-2 inputStaticArea)))))
 (local
   (in-theory (disable clearLoop-stack-is-irrelevant-to-mv-nth-0-helper)))
 (defthm
      clearLoop-stack-is-irrelevant-to-mv-nth-0
      (implies (and (stack-p stack)
                    (syntaxp (not (equal stack ''dummy-stack))))
               (equal  (mv-nth 0 (clearLoop x i op0 inputHeap nH stack inputStaticArea))
                      (mv-nth 0
                              (clearLoop x i op0 inputHeap nH 'dummy-stack inputStaticArea))))
      :hints
      (("GOAL" :use
               (:instance clearLoop-stack-is-irrelevant-to-mv-nth-0-helper
                          (stack-1 stack)
                          (stack-2 'dummy-stack))
               :in-theory
               (union-theories '(stack-p-dummy-stack)
                               (theory 'minimal-theory))))))

(encapsulate
 nil
 (local
  (defthm
    clearLoop-stack-is-irrelevant-to-mv-nth-1-helper
    (implies (and (stack-p stack-1)
                  (stack-p stack-2))
             (equal (mv-nth 1 (clearLoop x i op0 inputHeap nH stack-1 inputStaticArea))
                    (mv-nth 1 (clearLoop x i op0 inputHeap nH stack-2 inputStaticArea))))
    :hints
    (("GOAL"
          :induct
          (clearLoop-induction-fn-stack x i op0 inputHeap nH stack-1 stack-2 inputStaticArea)))))
 (local
   (in-theory (disable clearLoop-stack-is-irrelevant-to-mv-nth-1-helper)))
 (defthm
      clearLoop-stack-is-irrelevant-to-mv-nth-1
      (implies (and (stack-p stack)
                    (syntaxp (not (equal stack ''dummy-stack))))
               (equal  (mv-nth 1 (clearLoop x i op0 inputHeap nH stack inputStaticArea))
                      (mv-nth 1
                              (clearLoop x i op0 inputHeap nH 'dummy-stack inputStaticArea))))
      :hints
      (("GOAL" :use
               (:instance clearLoop-stack-is-irrelevant-to-mv-nth-1-helper
                          (stack-1 stack)
                          (stack-2 'dummy-stack))
               :in-theory
               (union-theories '(stack-p-dummy-stack)
                               (theory 'minimal-theory))))))

(encapsulate
 nil
 (local
  (defthm
    clearLoop-stack-is-irrelevant-to-mv-nth-2-helper
    (implies (and (stack-p stack-1)
                  (stack-p stack-2))
             (equal (mv-nth 2 (clearLoop x i op0 inputHeap nH stack-1 inputStaticArea))
                    (mv-nth 2 (clearLoop x i op0 inputHeap nH stack-2 inputStaticArea))))
    :hints
    (("GOAL"
          :induct
          (clearLoop-induction-fn-stack x i op0 inputHeap nH stack-1 stack-2 inputStaticArea)))))
 (local
   (in-theory (disable clearLoop-stack-is-irrelevant-to-mv-nth-2-helper)))
 (defthm
      clearLoop-stack-is-irrelevant-to-mv-nth-2
      (implies (and (stack-p stack)
                    (syntaxp (not (equal stack ''dummy-stack))))
               (equal  (mv-nth 2 (clearLoop x i op0 inputHeap nH stack inputStaticArea))
                      (mv-nth 2
                              (clearLoop x i op0 inputHeap nH 'dummy-stack inputStaticArea))))
      :hints
      (("GOAL" :use
               (:instance clearLoop-stack-is-irrelevant-to-mv-nth-2-helper
                          (stack-1 stack)
                          (stack-2 'dummy-stack))
               :in-theory
               (union-theories '(stack-p-dummy-stack)
                               (theory 'minimal-theory))))))

(encapsulate
 nil
 (local
  (defthm
    clearLoop-stack-is-irrelevant-to-mv-nth-3-helper
    (implies (and (stack-p stack-1)
                  (stack-p stack-2))
             (equal (mv-nth 3 (clearLoop x i op0 inputHeap nH stack-1 inputStaticArea))
                    (mv-nth 3 (clearLoop x i op0 inputHeap nH stack-2 inputStaticArea))))
    :hints
    (("GOAL"
          :induct
          (clearLoop-induction-fn-stack x i op0 inputHeap nH stack-1 stack-2 inputStaticArea)))))
 (local
   (in-theory (disable clearLoop-stack-is-irrelevant-to-mv-nth-3-helper)))
 (defthm
      clearLoop-stack-is-irrelevant-to-mv-nth-3
      (implies (and (stack-p stack)
                    (syntaxp (not (equal stack ''dummy-stack))))
               (equal  (mv-nth 3 (clearLoop x i op0 inputHeap nH stack inputStaticArea))
                      (mv-nth 3
                              (clearLoop x i op0 inputHeap nH 'dummy-stack inputStaticArea))))
      :hints
      (("GOAL" :use
               (:instance clearLoop-stack-is-irrelevant-to-mv-nth-3-helper
                          (stack-1 stack)
                          (stack-2 'dummy-stack))
               :in-theory
               (union-theories '(stack-p-dummy-stack)
                               (theory 'minimal-theory))))))

(encapsulate
 nil
 (local
  (defthm
    clearLoop-stack-is-irrelevant-to-mv-nth-4-helper
    (implies (and (stack-p stack-1)
                  (stack-p stack-2))
             (equal (mv-nth 4 (clearLoop x i op0 inputHeap nH stack-1 inputStaticArea))
                    (mv-nth 4 (clearLoop x i op0 inputHeap nH stack-2 inputStaticArea))))
    :hints
    (("GOAL"
          :induct
          (clearLoop-induction-fn-stack x i op0 inputHeap nH stack-1 stack-2 inputStaticArea)))))
 (local
   (in-theory (disable clearLoop-stack-is-irrelevant-to-mv-nth-4-helper)))
 (defthm
      clearLoop-stack-is-irrelevant-to-mv-nth-4
      (implies (and (stack-p stack)
                    (syntaxp (not (equal stack ''dummy-stack))))
               (equal  (mv-nth 4 (clearLoop x i op0 inputHeap nH stack inputStaticArea))
                      (mv-nth 4
                              (clearLoop x i op0 inputHeap nH 'dummy-stack inputStaticArea))))
      :hints
      (("GOAL" :use
               (:instance clearLoop-stack-is-irrelevant-to-mv-nth-4-helper
                          (stack-1 stack)
                          (stack-2 'dummy-stack))
               :in-theory
               (union-theories '(stack-p-dummy-stack)
                               (theory 'minimal-theory))))))


(encapsulate
 nil
 (local
  (defthm
    clearLoop-stack-is-irrelevant-to-mv-nth-6-helper
    (implies (and (stack-p stack-1)
                  (stack-p stack-2))
             (equal (mv-nth 6 (clearLoop x i op0 inputHeap nH stack-1 inputStaticArea))
                    (mv-nth 6 (clearLoop x i op0 inputHeap nH stack-2 inputStaticArea))))
    :hints
    (("GOAL"
          :induct
          (clearLoop-induction-fn-stack x i op0 inputHeap nH stack-1 stack-2 inputStaticArea)))))
 (local
   (in-theory (disable clearLoop-stack-is-irrelevant-to-mv-nth-6-helper)))
 (defthm
      clearLoop-stack-is-irrelevant-to-mv-nth-6
      (implies (and (stack-p stack)
                    (syntaxp (not (equal stack ''dummy-stack))))
               (equal  (mv-nth 6 (clearLoop x i op0 inputHeap nH stack inputStaticArea))
                      (mv-nth 6
                              (clearLoop x i op0 inputHeap nH 'dummy-stack inputStaticArea))))
      :hints
      (("GOAL" :use
               (:instance clearLoop-stack-is-irrelevant-to-mv-nth-6-helper
                          (stack-1 stack)
                          (stack-2 'dummy-stack))
               :in-theory
               (union-theories '(stack-p-dummy-stack)
                               (theory 'minimal-theory))))))

; A characterization of the partial invariance of the stack

(defthm
     clearLoop-all-but-top-of-stack-is-invariant
     (implies  (and (integerp i)
                  (integerp op0)
                  (array-p x 'int 1)
                  (static-area-p inputStaticArea)
                  (stack-p inputStack)
                  (heap-counter-p nh)
                  (heap-p inputHeap)
                  (= i op0))
              (equal (popframe (mv-nth 5 (clearLoop x i op0 inputHeap nH inputStack inputStaticArea)))
                     (popframe inputStack))))

; Invariance of length of the array x

(defthm clearLoop-array-length-invariant-0
        (implies (and (integerp i)
                  (integerp op0)
                  (array-p x 'int 1)
                  (static-area-p inputStaticArea)
                  (stack-p inputStack)
                  (heap-counter-p nh)
                  (heap-p inputHeap)
                  (= i op0))
                 (let ((new-heap (mv-nth 3 (clearLoop x i op0 inputHeap nH inputStack inputStaticArea))))
                      (equal (valueh (refh x 'array_length_marker)
                                     new-heap)
                             (valueh (refh x 'array_length_marker)
                                     inputHeap)))))

;  OK now we "bind the irrelevant variables".
; I suspect that this characterizes the invarians of i vis-a-vis nH and inputStat.

;  This is based on the defuns "destiny-rewriting-goal-literal" and
;  "destiny-bind-irrelevant-vars" within destiny-model.

;  (defun destiny-bind-irrelevant-vars (fn-name irrelevant-poss mv-nth-pos args to-bind-list mfc state)


; Matt K., after v4-2:
; Commenting out the following rule, which rewrites a term to itself!
#||
(defthm
 clearLoop-irrrelevance-thm-i-8
 (implies
  (and
     (syntaxp (destiny-rewriting-goal-literal mfc state))
     (bind-free
          (destiny-bind-irrelevant-vars 'clearLoop
                                        '(6 4)
                                        1  (list x i op0 inputHeap nh-1 inputStack stat-1)
                                        '(stat-2 nh-2)
                                        mfc state)
          (stat-2 nh-2))
(integerp i)
         (integerp op0)
         (array-p x 'int 1)
         (static-area-p stat-1)
         (static-area-p stat-2)
         (stack-p stack)
         (heap-counter-p nh-1)
         (heap-counter-p nh-2)
         (heap-p inputHeap)
         (= i op0))

                 (equal (mv-nth 1 (clearLoop x i op0 inputHeap nh-1 inputStack stat-1))
         (mv-nth 1 (clearLoop x i op0 inputHeap nh-1 inputStack stat-1))))
 :hints
 (("GOAL" :induct
          (clearLoop-induction-fnh-1stack-1x-8i-8 x i op0 inputHeap nh-1 nh-2 stack stat-1 stat-2))))
||#

; I suspect that this characterizes the invariance of inputHeap vis-a-vis nH and inputStat.

; Matt K., after v4-2:
; Commenting out the following rule, which rewrites a term to itself!
#||
(defthm
 clearLoop-irrrelevance-thm-h-1
 (implies
  (and
     (syntaxp (destiny-rewriting-goal-literal mfc state))
     (bind-free
          (destiny-bind-irrelevant-vars 'clearLoop
                                        '(6 4)
                                        3  (list x i op0 inputHeap nh-1 inputStack stat-1)
                                        '(stat-2 nh-2)
                                        mfc state)
          (stat-2 nh-2))
(integerp i)
         (integerp op0)
         (array-p x 'int 1)
         (static-area-p stat-1)
         (static-area-p stat-2)
         (stack-p stack)
         (heap-counter-p nh-1)
         (heap-counter-p nh-2)
         (heap-p inputHeap)
         (= i op0))

                 (equal (mv-nth 3 (clearLoop x i op0 inputHeap nh-1 inputStack stat-1))
         (mv-nth 3 (clearLoop x i op0 inputHeap nh-1 inputStack stat-1))))
 :hints
 (("GOAL" :induct
          (clearLoop-induction-fnh-1stack-1x-8i-8 x i op0 inputHeap nh-1 nh-2 stack stat-1 stat-2))))
||#


; This concludes the discussion of the translation of the loop module into acl2.  We now
; define the additional hypothesis for the clear routine and prove the conjecture.  (The definition
; of "arrayLength" is taken from the "Function Space" within Destiny.  This definition was stubbed out
; in the original destiny-model.)

(defun arrayLength (obj heap) (valueH (refH obj 'array_length_marker) heap))

(defun |length of the Array 'x' is greater than or equal to 10| (x inputHeap)
( not ( < ( arrayLength x inputHeap ) 10 ) ))

;; an induction helper

(defthm |'i in output stack of loop at #2:iload_i' is greater than or equal to 10-helper|
    (implies
   (and (integerp i)
         (integerp op0)
         (array-p x 'int 1)
         (static-area-p inputStaticArea)
         (stack-p inputStack)
         (heap-counter-p nh)
         (heap-p inputHeap)
         (= i op0)
                (|length of the Array 'x' is greater than or equal to 10| x inputHeap)
                (|'x' is defined| x)
                (<= 0 i))

                (not (< (mv-nth 1 (clearLoop x i op0 inputHeap nH inputStack inputStaticArea)) 10))))

;;  NOTE: This theorem literally translated from Destiny would express the output i as an
;; access into the local variable array of the output stack at offset 1.  However, Destiny
;; guarantees that this value is the same as the output of parameter i.  We take the liberty
;; of expressing the theorem in terms of this output i rather than the stack.  It is in this
;; sense that Destiny tries to "hide" the structure of the stack as much as possible.

(defthm
  |'i in output stack of loop at #2:iload_i' is greater than or equal to 10|
  (implies
   (and (integerp i)
        (integerp op0)
        (array-p x 'int 1)
        (static-area-p inputStaticArea)
        (stack-p inputStack)
        (heap-counter-p nh)
        (heap-p inputHeap)
        (= i op0)
        (|length of the Array 'x' is greater than or equal to 10| x inputHeap)
        (|'x' is defined| x)
        (<= 0 i))
   (not (<
         (mv-nth
          1
          (clearLoop x 0 0 inputHeap nH

                     (pushFrame
                      (storeLocalVar1
                       0
                       1
                       (storeLocalVar1
                        x
                        0
                        (pushOpStack1
                         0
                         (popop
                          (topFrame inputStack )))))
                      (popFrame  inputStack ))
                     inputStaticArea))

         10))))

;; This concludes the discussion of the termination conjecture.  We now proceed to the proof of the main
;; theorem, that x[5]==x[6].

(set-ignore-ok t)
(set-match-free-default :all)


;;; RBK: The next pair of lemmas are typical of proofs about doing
;;; things to an array

;;; Array entries below loop counter are unchanged

(defthm x5==x6-helper-1
  (implies
   (and (integerp i)
         (integerp op0)
         (array-p x 'int 1)
         (static-area-p inputStaticArea)
         (stack-p inputStack)
         (heap-counter-p nh)
         (heap-p inputHeap)
         (= i op0)
              (not (< (arraylength x inputHeap) 10))
                            (|'x' is defined| x)

        (integerp index)
        (< index i))
       (let ((heapmodel
          (mv-nth 3
           (clearLoop x i op0 inputHeap nH inputStack inputStaticArea))))
         (equal (valueh (refh x index) heapmodel)
            (valueh (refh x index) inputHeap)))))


;;; Array entries at or above the loop counter are zeroed

(defthm x5==x6-helper-2
  (implies
   (and (integerp i)
         (integerp op0)
         (array-p x 'int 1)
         (static-area-p inputStaticArea)
         (stack-p inputStack)
         (heap-counter-p nh)
         (heap-p inputHeap)
         (= i op0)
              (not (< (arraylength x inputHeap) 10))
                            (|'x' is defined| x)

        (integerp index)
            (<= 0 i)
        (<= i index)
        (< index 10))
       (let ((heapmodel
          (mv-nth 3
           (clearLoop x i op0 inputHeap nH inputStack inputStaticArea))))
         (equal (valueh (refh x index) heapmodel)
            0))))

;; the main theorem

(defthm |'x'[5] equals 'x'[6]|

  (implies
   (and
    (array-p x 'int 1)
    (static-area-p inputStaticArea)
    (stack-p inputStack)
    (heap-counter-p nh)
    (heap-p inputHeap)

    (not (< (arraylength x inputHeap) 10))
    (|'x' is defined| x)
    )
   (let (

         (outputHeap
          (mv-nth 3
                  (clearLoop x 0 0 inputHeap nH
                             (pushFrame
                              (storeLocalVar1
                               0
                               1
                               (storeLocalVar1
                                x
                                0
                                (pushOpStack1
                                 0
                                 (pushOpStack1
                                  '---
                                  (topFrame inputStack )))))
                              (pushFrame
                               (storeLocalVar1
                                x
                                0
                                (topFrame inputStack )
                                )
                               (popFrame inputStack )))
                             inputStaticArea))))

     (= (valueh (refh x 5) outputHeap) (valueH (refH x 6) outputHeap)))))#|ACL2s-ToDo-Line|#

