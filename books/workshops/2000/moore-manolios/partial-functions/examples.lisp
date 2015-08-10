; Copyright (C) 1999 J Strother Moore

; This book is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This book is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this book; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; This book proves the theorems about the ``Toy Java Virtual Machine''
; tjvm, discussed in the paper

; Proving Theorems about Java-like Byte Code
; by J Strother Moore


(in-package "TJVM")

(include-book "tjvm")

; Here we develop the general theory for proving things about tjvm.

; Simplest of Arithmetic

(defthm constant-fold-+
  (implies (syntaxp (and (quotep x) (quotep y)))
           (equal (+ x (+ y z)) (+ (+ x y) z))))

(defthm commutativity2-of-+
  (equal (+ x y z) (+ y x z))
  :hints (("Goal" :use ((:instance acl2::associativity-of-+
                                   (acl2::x y)
                                   (acl2::y x)
                                   (acl2::z z))
                        (:instance acl2::associativity-of-+
                                   (acl2::x x)
                                   (acl2::y y)
                                   (acl2::z z))
                        (:instance acl2::commutativity-of-+
                                   (acl2::x x)
                                   (acl2::y y)))
           :in-theory (disable acl2::associativity-of-+
                               acl2::commutativity-of-+))))

(defthm commutativity2-of-*
  (equal (* x y z) (* y x z))
  :hints (("Goal" :use ((:instance acl2::associativity-of-*
                                   (acl2::x y)
                                   (acl2::y x)
                                   (acl2::z z))
                        (:instance acl2::associativity-of-*
                                   (acl2::x x)
                                   (acl2::y y)
                                   (acl2::z z))
                        (:instance acl2::commutativity-of-*
                                   (acl2::x x)
                                   (acl2::y y)))
           :in-theory (disable acl2::associativity-of-*
                               acl2::commutativity-of-*))))

(defthm plus-right-id
  (equal (+ x 0) (fix x)))

(defthm *-0 (equal (* 0 x) 0))

(defthm +-cancellation1
  (equal (+ i j (* -1 i) k)
         (+ j k)))

; Abstract Data Type Stuff

(defthm stacks
  (and (equal (top (push x s)) x)
       (equal (pop (push x s)) s)))

(in-theory (disable push top pop))

(defthm states
  (and (equal (call-stack (make-state s h c)) s)
       (equal (heap (make-state s h c)) h)
       (equal (class-table (make-state s h c)) c)))

(in-theory (disable make-state call-stack heap class-table))

(defthm frames
  (and (equal (pc (make-frame pc l s prog)) pc)
       (equal (locals (make-frame pc l s prog)) l)
       (equal (stack (make-frame pc l s prog)) s)
       (equal (program (make-frame pc l s prog)) prog)))

(in-theory (disable make-frame pc locals stack program))

; Step Stuff

(defthm step-opener
  (implies (consp (next-inst s))
           (equal (step s) (do-inst (next-inst s) s))))

(in-theory (disable step))

; Clocks

(defun c+ (i j)
  (if (zp i)
      (nfix j)
    (+ 1 (c+ (- i 1) j))))

(defun c* (i j)
  (if (zp i) 0 (c+ j (c* (- i 1) j))))

(defmacro ++ (&rest args)
  (if (endp args)
      0
    (if (endp (cdr args))
        (car args)
      `(c+ ,(car args) (++ ,@(cdr args))))))

(defthm c+-revealed
  (implies (and (natp i) (natp j))
           (equal (c+ i j) (+ i j))))

(defthm c*-revealed
  (implies (and (natp i) (natp j))
           (equal (c* i j) (* i j))))

(in-theory (disable c+-revealed c*-revealed))

(defthm tjvm-c+
  (implies (and (natp i) (natp j))
	   (equal (tjvm s (c+ i j))
		  (tjvm (tjvm s i) j))))

; Sometimes we get tjvm expressions such as (tjvm s (+ 4 (c+ ...))).  The
; following lemma produces (tjvm (tjvm s 4) (c+ ...)).

(defthm tjvm-+
  (implies (and (natp i) (natp j))
	   (equal (tjvm s (+ i j))
		  (tjvm (tjvm s i) j)))
  :hints (("Goal" :use tjvm-c+
                  :in-theory (enable c+-revealed))))

; Then we finally hit the (tjvm s 4) repeatedly with the following lemma to
; step s 4 times.

(defthm tjvm-opener
  (and (equal (tjvm s 0) s)
       (implies (natp i)
                (equal (tjvm s (+ 1 i))
                       (tjvm (step s) i)))))

(in-theory (disable tjvm))

; Alist Stuff

(defthm assoc-equal-bind
  (equal (assoc-equal key1 (bind key2 val alist))
         (if (equal key1 key2)
             (cons key1 val)
           (assoc-equal key1 alist))))

(defthm bind-formals-cons
  (and (equal (bind-formals nil stack) nil)
       (equal (bind-formals (cons var formals) stack)
              (cons (cons var (top stack))
                    (bind-formals formals (pop stack))))))

; Stack Stuff

; We normalize all POPNs away.

(defthm popn-opener
  (and (equal (popn 0 stack) stack)
       (implies (and (integerp n)
                     (<= 0 n))
                (equal (popn (+ 1 n) stack)
                       (popn n (pop stack))))))

; Applications

(defun fact (n)
  (if (zp n)
      1
    (* n (fact (- n 1)))))

(defun \bf_fact ()
  '("fact" (n)
    (load n)
    (ifle 8)
    (load n)
    (load n)
    (push 1)
    (sub)
    (invokestatic "Math" "fact" 1)
    (mul)
    (xreturn)
    (push 1)
    (xreturn)))

(defun \bfMath-class ()
  (make-class-decl "Math"
                   '("Object")
                   nil
                   (list (\bf_fact))))

(defun fact-clock (n)
  (if (zp n)
      5
    (++ 7
        (fact-clock (- n 1))
        2)))

(defthm example1
  (equal (top
          (stack
           (top-frame
            (tjvm (make-state
                  (push (make-frame 0
                                    nil
                                    nil
                                    '((push 5)
                                      (invokestatic "Math" "fact" 1)
                                      (halt)))
                        nil)
                  nil
                  (list (\bfMath-class)))
                 (++ 1 (fact-clock 5) 1)))))
         120)
  :rule-classes nil)

(defthm fact-clock-revealed
  (implies (natp n) (equal (fact-clock n) (+ 5 (* 9 n))))
  :hints (("Goal" :in-theory (enable c+-revealed)))
  :rule-classes nil)

(defun example2-hint (s0 n)
  (if (zp n)
      s0
    (example2-hint
     (make-state
      (push (make-frame 6
                        (list (cons 'n (top (stack (top-frame s0)))))
                        (push (- (top (stack (top-frame s0))) 1)
                              (push (top (stack (top-frame s0)))
                                    nil))
                        (method-program (\bf_fact)))
            (push (make-frame (+ 1 (pc (top (call-stack s0))))
                              (locals (top (call-stack s0)))
                              (pop (stack (top (call-stack s0))))
                              (program (top (call-stack s0))))
                  (pop (call-stack s0))))
      (heap s0)
      (class-table s0))
     (- n 1))))

(defthm example2
  (implies (and (equal (next-inst s0) '(invokestatic "Math" "fact" 1))
                (equal (assoc-equal "Math" (class-table s0))
                       (\bfMath-class))
                (equal n (top (stack (top-frame s0))))
                (natp n))
           (equal
            (tjvm s0 (fact-clock n))
            (make-state
             (push (make-frame (+ 1 (pc (top-frame s0)))
                               (locals (top-frame s0))
                               (push (fact n)
                                     (pop (stack (top-frame s0))))
                               (program (top-frame s0)))
                   (pop (call-stack s0)))
             (heap s0)
             (class-table s0))))
  :hints (("Goal" :induct (example2-hint s0 n)))
  :rule-classes nil)

(defun \bf_xIncrement ()
  '("xIncrement" (dx)
    (load this)
    (load this)
    (getfield "Point" "x")
    (load dx)
    (add)
    (putfield "Point" "x")
    (return)))

(defun xIncrement-clock () 8)

(defun \bf_inBox ()
  '("inBox" (p1 p2)
    (load p1)
    (getfield "Point" "x")
    (load this)
    (getfield "Point" "x")
    (sub)
    (ifgt 21)
    (load this)
    (getfield "Point" "x")
    (load p2)
    (getfield "Point" "x")
    (sub)
    (ifgt 15)
    (load p1)
    (getfield "Point" "y")
    (load this)
    (getfield "Point" "y")
    (sub)
    (ifgt 9)
    (load this)
    (getfield "Point" "y")
    (load p2)
    (getfield "Point" "y")
    (sub)
    (ifgt 3)
    (push 1)
    (xreturn)
    (push 0)
    (xreturn)))

(defun \bfPoint-class ()
  (make-class-decl "Point"
                   '("Object")
                   '("x" "y")
                   (list (\bf_xIncrement)
                         (\bf_inBox))))

(defun \bf_setColor ()
  '("setColor" (c)
    (load this)
    (load c)
    (putfield "ColoredPoint" "color")
    (return)))

(defun setColor-clock () 5)

(defun \bf_setColorBox ()
  '("setColorBox" (p1 p2 color)
    (load this)
    (load p1)
    (load p2)
    (invokevirtual "ColoredPoint" "inBox" 2)
    (ifeq 4)
    (load this)
    (load color)
    (putfield "ColoredPoint" "color")
    (return)))

(defun \bfColoredPoint-class ()
  (make-class-decl "ColoredPoint"
                   '("Point" "Object")
                   '("color")
                   (list (\bf_setColor)
                         (\bf_setColorBox))))


(defthm example3
  (let ((s (tjvm (make-state
                 (push
                  (make-frame 0
                              '((p . nil))
                              nil
                              '((new "ColoredPoint")
                                (store p)
                                (load p)
                                (push -23)
                                (invokevirtual "ColoredPoint" "xIncrement" 1)
                                (load p)
                                (push "Green")
                                (invokevirtual "ColoredPoint" "setColor" 1)
                                (load p)
                                (halt)))
                  nil)
                 nil
                 (list (\bfPoint-class)
                       (\bfColoredPoint-class)))
                (++ 4
                    (xIncrement-clock)
                    2
                    (setColor-clock)
                    2))))
    (equal (deref (top (stack (top-frame s)))
                  (heap s))
           '(("ColoredPoint" ("color" . "Green"))
             ("Point" ("x" . -23) ("y" . 0))
             ("Object")))))

(defun instance-of (ref class-name s)
  (assoc-equal class-name
               (deref ref (heap s))))

(defun Point.x (ref s)
  (field-value "Point" "x" (deref ref (heap s))))

(defun Point.y (ref s)
  (field-value "Point" "y" (deref ref (heap s))))

(defun inBox-clock (this p1 p2 s)
  (cond ((> (Point.x p1 s)
            (Point.x this s))
         9)
        ((> (Point.x this s)
            (Point.x p2 s))
         15)
        ((> (Point.y p1 s)
            (Point.y this s))
         21)
        (t 27)))

(defun inBox (this p1 p2 s)
  (and (<= (Point.x p1 s)
           (Point.x this s))
       (<= (Point.x this s)
           (Point.x p2 s))
       (<= (Point.y p1 s)
           (Point.y this s))
       (<= (Point.y this s)
           (Point.y p2 s))))

(defun setColorBox-clock (this p1 p2 c s)
  (declare (ignore c))
  (++ 4
      (inBox-clock this p1 p2 s)
      (if (inBox this p1 p2 s)
          5
        2)))

(defun setColorBox-heap (this p1 p2 c s)

; This function returns the new heap.

  (if (inBox this p1 p2 s)
      (let ((instance (deref this (heap s)))
            (address (cadr this)))
        (bind
         address
         (set-instance-field "ColoredPoint" "color" c instance)
         (heap s)))
    (heap s)))

(defthm example4
  (implies (and (consp (next-inst s0))
                (equal (car (next-inst s0)) 'invokevirtual)
                (equal (caddr (next-inst s0)) "inBox")
                (equal (cadddr (next-inst s0)) 2)

                (equal this (top (pop (pop (stack (top-frame s0))))))
                (equal p1  (top (pop (stack (top-frame s0)))))
                (equal p2  (top (stack (top-frame s0))))

; This next hyp is necessary because even if I know that the THIS object
; is an instance-of class "Point" I do not know that the "inBox" method
; hasn't been overridden!

                (equal (lookup-method "inBox"
                                      (class-name-of-ref this (heap s0))
                                      (class-table s0))
                       (\bf_inBox)))
           (equal
            (tjvm s0 (inBox-clock this p1 p2 s0))
            (make-state
             (push (make-frame (+ 1 (pc (top-frame s0)))
                               (locals (top-frame s0))
                               (push (if (inBox this p1 p2 s0) 1 0)
                                     (popn 3 (stack (top-frame s0))))
                               (program (top-frame s0)))
                   (pop (call-stack s0)))
             (heap s0)
             (class-table s0))))

  :rule-classes
  ((:rewrite
    :corollary
    (implies (and (consp (next-inst s0))
                  (equal (car (next-inst s0)) 'invokevirtual)
                  (equal (caddr (next-inst s0)) "inBox")
                  (equal (cadddr (next-inst s0)) 2)

                  (equal this (top (pop (pop (stack (top-frame s0))))))
                  (equal p1  (top (pop (stack (top-frame s0)))))
                  (equal p2  (top (stack (top-frame s0))))

; This next hyp is necessary because even if I know that the THIS object
; is an instance-of class "Point" I do not know that the "inBox" method
; hasn't been overridden!

                  (equal (lookup-method "inBox"
                                        (class-name-of-ref this (heap s0))
                                        (class-table s0))
                         (\bf_inBox))
                  (equal (inBox-clock this p1 p2 s1)
                         (inBox-clock this p1 p2 s0)))
             (equal
              (tjvm s0 (inBox-clock this p1 p2 s1))
              (make-state
               (push (make-frame (+ 1 (pc (top-frame s0)))
                                 (locals (top-frame s0))
                                 (push (if (inBox this p1 p2 s0) 1 0)
                                       (popn 3 (stack (top-frame s0))))
                                 (program (top-frame s0)))
                     (pop (call-stack s0)))
               (heap s0)
               (class-table s0))))
    :hints (("Goal" :in-theory (disable tjvm-opener))))))


(in-theory (disable inBox-clock inBox))

(defthm hackish-lemma1
  (equal
   (inbox-clock
    (top (pop (pop (pop (stack (top (call-stack s0)))))))
    (top (pop (pop (stack (top (call-stack s0))))))
    (top (pop (stack (top (call-stack s0)))))
    (make-state
     (push
      (make-frame
       '3
       (cons (cons 'this
                   (top (pop (pop (pop (stack (top (call-stack s0))))))))
             (cons (cons 'p1
                         (top (pop (pop (stack (top (call-stack s0)))))))
                   (cons (cons 'p2
                               (top (pop (stack (top (call-stack s0))))))
                         (cons (cons 'color
                                     (top (stack (top (call-stack s0)))))
                               'nil))))
       (push (top (pop (stack (top (call-stack s0)))))
             (push (top (pop (pop (stack (top (call-stack s0))))))
                   (push (top (pop (pop (pop (stack (top (call-stack s0)))))))
                         'nil)))
       '((load this)
         (load p1)
         (load p2)
         (invokevirtual "ColoredPoint" "inBox" 2)
         (ifeq 4)
         (load this)
         (load color)
         (putfield "ColoredPoint" "color")
         (return)))
      (push (make-frame (+ 1 (pc (top (call-stack s0))))
                        (locals (top (call-stack s0)))
                        (pop (pop (pop (pop (stack (top (call-stack s0)))))))
                        (program (top (call-stack s0))))
            (pop (call-stack s0))))
     (heap s0)
     (class-table s0)))
   (inbox-clock (top (pop (pop (pop (stack (top (call-stack s0)))))))
                      (top (pop (pop (stack (top (call-stack s0))))))
                      (top (pop (stack (top (call-stack s0)))))
                      s0))
  :hints (("goal" :in-theory (enable inbox-clock))))

(defthm hackish-lemma2
  (equal
   (inbox
    (top (pop (pop (pop (stack (top (call-stack s0)))))))
    (top (pop (pop (stack (top (call-stack s0))))))
    (top (pop (stack (top (call-stack s0)))))
    (make-state
     (push
      (make-frame
       '3
       (cons (cons 'this
                   (top (pop (pop (pop (stack (top (call-stack s0))))))))
             (cons (cons 'p1
                         (top (pop (pop (stack (top (call-stack s0)))))))
                   (cons (cons 'p2
                               (top (pop (stack (top (call-stack s0))))))
                         (cons (cons 'color
                                     (top (stack (top (call-stack s0)))))
                               'nil))))
       (push (top (pop (stack (top (call-stack s0)))))
             (push (top (pop (pop (stack (top (call-stack s0))))))
                   (push (top (pop (pop (pop (stack (top (call-stack s0)))))))
                         'nil)))
       '((load this)
         (load p1)
         (load p2)
         (invokevirtual "ColoredPoint" "inBox" 2)
         (ifeq 4)
         (load this)
         (load color)
         (putfield "ColoredPoint" "color")
         (return)))
      (push (make-frame (+ 1 (pc (top (call-stack s0))))
                        (locals (top (call-stack s0)))
                        (pop (pop (pop (pop (stack (top (call-stack s0)))))))
                        (program (top (call-stack s0))))
            (pop (call-stack s0))))
     (heap s0)
     (class-table s0)))
   (inbox (top (pop (pop (pop (stack (top (call-stack s0)))))))
                (top (pop (pop (stack (top (call-stack s0))))))
                (top (pop (stack (top (call-stack s0)))))
                s0))
  :hints (("goal" :in-theory (enable inbox))))

; This lemma is not stated generally enough to allow it to be used.
; We need to introduce s1 in the lhs of the concl, as in example4.

(defthm example5
  (implies (and (consp (next-inst s0))
                (equal (car (next-inst s0)) 'invokevirtual)
                (equal (caddr (next-inst s0)) "setColorBox")
                (equal (cadddr (next-inst s0)) 3)

                (equal this (top (pop (pop (pop (stack (top-frame s0)))))))
                (equal p1  (top (pop (pop (stack (top-frame s0))))))
                (equal p2  (top (pop (stack (top-frame s0)))))
                (equal color (top (stack (top-frame s0))))

                (equal (lookup-method "inBox"
                                      (class-name-of-ref this (heap s0))
                                      (class-table s0))
                       (\bf_inBox))
                (equal (lookup-method "setColorBox"
                                      (class-name-of-ref this (heap s0))
                                      (class-table s0))
                       (\bf_setColorBox)))
           (equal
            (tjvm s0 (setColorBox-clock this p1 p2 color s0))
            (make-state
             (push (make-frame (+ 1 (pc (top-frame s0)))
                               (locals (top-frame s0))
                               (popn 4 (stack (top-frame s0)))
                               (program (top-frame s0)))
                   (pop (call-stack s0)))
             (setColorBox-heap this p1 p2 color s0)
             (class-table s0)))))

; The above lemma may not look very interesting.  But the following observation
; shows that it is:

(defthm setColorBox-heap-property
  (implies (and (refp ref)
                (refp this))
           (equal (deref ref
                         (setColorBox-heap this p1 p2 color s))
                  (if (and (equal ref this)
                           (inBox this p1 p2 s))
                      (set-instance-field "ColoredPoint" "color" color
                                          (deref this (heap s)))
                    (deref ref (heap s))))))

; Several problems have come to light.
; (1) The role of s1 in example4.
; (2) The more general difficulty of counting cycles in the presence of
;     of overriding.  I really need a predicate that says "this clock
;     is appropriate for this method body"
; (3) Lack of evidence that something meaningful can be done with the heap.
;     By this I mean to suggest work on extracting abstract objects from
;     the heap.  If the abstract object is an object in ACL2, this is
;     probably straightforward.  If it is some circular object, it must
;     be represented more or less as a heap object.  That being the case,
;     it seems that this problem is really one of just getting used to
;     a suitable bunch of primitives like deref and get-instance-field.
