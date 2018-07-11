; Copyright (C) 2013, ForrestHunt, Inc.
; Written by J Strother Moore (some years before that)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "consider-hint")
(add-consider-hint)
(make-event (pprogn (show-custom-keyword-hint-expansion t)
                    (value '(value-triple nil))))

(include-book "misc/eval" :dir :system)

(defstub h (x) t)

(defun map-h (x)
  (if (endp x)
      nil
    (cons (h (car x)) (map-h (cdr x)))))

(defthm map-h-append
  (equal (map-h (append y z))
         (append (map-h y) (map-h z)))
  :rule-classes nil)

(defstub hp (x) t)

(defun filter-map-h (x)
  (if (endp x)
      nil
    (if (hp (car x))
        (cons (h (car x)) (filter-map-h (cdr x)))
      (filter-map-h (cdr x)))))

(defthm filter-map-h-append
  (equal (filter-map-h (append y z))
         (append (filter-map-h y) (filter-map-h z)))
  :rule-classes nil)

(defun bumper1 (u v w)
  (if (endp u)
      nil
    (cons (+ (* w (car u)) v)
          (bumper1 (cdr u) v w))))

(defun bumper2 (u v w)
  (if (consp u)
      (cons (+ (* w (car u)) v)
            (bumper2 (cdr u) v w))
    nil))

(defun bumper3 (u v w)
  (if (consp u)
      (if (zp (car u))
          (cons 0 (bumper3 (cdr u) v w))
        (cons (+ (* w (car u)) v)
              (bumper3 (cdr u) v w)))
    nil))

(defun bumper4 (u v)
  (if (consp u)
      (if (zp (* (car u) v))
          (bumper4 (cdr u) v)
        (cons (+ v (car u)) (bumper4 (cdr u) v)))
    nil))

(defun generic-run (s n)
  (if (zp n)
      s
    (generic-run (h s) (- n 1))))

(defun m5-run (s n)
  (if (zp n)
      s
    (m5-run (cons 3 s) (- n 1))))

(defun generic-exists (x)
  (if (endp x)
      nil
    (or (h x)
        (generic-exists (cdr x)))))

(defstub g (x y) t)

(defun generic-list-iterator (x ans)
  (cond ((endp x) ans)
        (t (generic-list-iterator (cdr x) (g (car x) ans)))))

(defun get-integers (x a)
  (cond ((consp x)
         (cond ((integerp (car x))
                (get-integers (cdr x) (cons (car x) a)))
               (t (get-integers (cdr x) a))))
        (t a)))

(defun get-big-integers (x min a)
  (cond ((consp x)
         (cond ((and (integerp (car x))
                     (>= (car x) min))
                (get-big-integers (cdr x) min (cons (car x) a)))
               (t (get-big-integers (cdr x) min a))))
        (t a)))

(defthm generic-run-sum
  (implies (and (integerp i)
                (<= 0 i)
                (integerp j)
                (<= 0 j))
           (equal (generic-run s (+ i j))
                  (generic-run (generic-run s i) j))))

(defthm generic-list-iterator-append
  (equal (generic-list-iterator (append u v) a)
         (generic-list-iterator v (generic-list-iterator u a))))


(must-prove
 (equal (bumper1 (append a b) i j)
        (append (bumper1 a i j)
                (bumper1 b i j)))
 :hints
 (("Goal"
   :consider (map-h-append :target (bumper1 (append a b) i j) ))))

(must-prove
 (equal (bumper1 (append a b) i j)
        (append (bumper1 a i j)
                (bumper1 b i j)))
 :hints
 (("Goal"
   :consider map-h-append)))

(must-prove
 (equal (bumper2 (append a b) i j)
        (append (bumper2 a i j)
                (bumper2 b i j)))
 :hints
 (("Goal"
   :consider map-h-append)))

(must-prove
 (equal (bumper3 (append a b) i j)
        (append (bumper3 a i j)
                (bumper3 b i j)))
 :hints
 (("Goal"
   :consider map-h-append)))

(must-prove
 (equal (bumper1 (append a b) i j)
        (append (bumper1 a i j)
                (bumper1 b i j)))
 :hints
 (("Goal"
   :consider filter-map-h-append)))

(must-prove
 (equal (bumper2 (append a b) i j)
        (append (bumper2 a i j)
                (bumper2 b i j)))
 :hints
 (("Goal"
   :consider filter-map-h-append)))

(must-prove
 (equal (bumper3 (append a b) i j)
        (append (bumper3 a i j)
                (bumper3 b i j)))
 :hints
 (("Goal"
   :consider filter-map-h-append)))

(must-prove
 (equal (bumper4 (append a b) i)
        (append (bumper4 a i)
                (bumper4 b i)))
 :hints
 (("Goal"
   :consider filter-map-h-append)))

(must-prove
 (implies (and (integerp i)
               (<= 0 i)
               (integerp j)
               (<= 0 j))
          (equal (m5-run s (+ i j))
                 (m5-run (m5-run s i) j)))
 :hints (("Goal"
          :consider generic-run-sum)))

(must-prove
 (equal (get-integers (append x y) z)
        (get-integers y (get-integers x z)))
 :hints (("Goal"
          :consider generic-list-iterator-append)))

(must-prove
 (equal (get-big-integers (append x y) u z)
        (get-big-integers y u (get-big-integers x u z)))
 :hints (("Goal"
          :consider generic-list-iterator-append)))

(skip-proofs
 (defthm g-thm (g x y) :rule-classes nil))


(must-prove
 (equal a b)

                  ;;; ************************************************
                  ;;; THIS GENERATES TWO SUBSTS AND THE FIRST SUCCEEDS
                  ;;; ************************************************

 :hints (("Goal"
          :consider g-thm)))

(must-not-prove
 (equal a b)
                  ;;; ***************************
                  ;;; THIS IS SUPPOSED TO FAIL!!!
                  ;;; ***************************

 :hints (("Goal"
          :consider (g-thm :instance ((X c))))))

(must-prove
 (equal a b)

                  ;;; ***************************
                  ;;; By seeding subst we get just 1
                  ;;; ***************************


 :hints
 (("Goal"
   :consider
   (g-thm :functional-instance ((G (LAMBDA (X Y) (EQUAL X B))))))))

(defthm assoc-append
  (equal (append (append a b) c)
         (append a (append b c)))
  :rule-classes nil)

; This is a test of first-order matching of the lhs of assoc-append, sweeping
; through the goal for the first match.

(must-prove
 (equal (append xxx (append a (append a a)))
        (append xxx (append (append a a) a)))
 :hints (("Goal" :consider assoc-append)))

; This next block illustrates a :consider hint with two items.

(defun app (x y)
  (if (consp x)
      (cons (car x) (app (cdr x) y))
    y))

(defun rev (x)
  (if (consp x)
      (app (rev (cdr x)) (list (car x)))
    nil))

(defthm assoc-of-app
  (equal (app (app a b) c)
         (app a (app b c)))
  :rule-classes nil)

(defthm rev-rev
  (implies (true-listp x) (equal (rev (rev x)) x)))

(defthm true-listp-rev (true-listp (rev x)))

(defthm triple-rev
  (equal (rev (rev (rev a))) (rev a))
  :rule-classes nil)

(in-theory (disable rev-rev true-listp-rev))

(must-prove
 (equal (app (app (rev (rev (rev a)))
                  b)
             c)
        (app (rev a)
             (app b
                  c)))
 :hints
 (("Goal"
   :do-not '(generalize)
   :consider (assoc-of-app triple-rev))))

(add-custom-keyword-hint :youse
                         (if (equal clause clause)
                             (value
                              (splice-keyword-alist
                               :youse
                               `(:use ,val)
                               keyword-alist))
                           (value nil)))

(add-custom-keyword-hint :ore
                         (if (equal clause clause)
                             (value
                              (splice-keyword-alist
                               :ore
                               `(:or ,val)
                               keyword-alist))
                           (value nil)))

(must-not-prove
 (equal (append a b) (append b a))
 :hints
 (("Subgoal *1/1"
   :in-theory (disable car-cons)
   :or ((:do-not '(generalize)
                 :ore ((:by nil)
                       (:youse (:instance car-cons (x case) (y 2)))))
        (:youse (:instance car-cons (x case) (y 3)))))))

; Here is a :consider hint that generates several substitutions and
; picks the wrong one.  The second of the top two is the right one.
; Make it work.

(encapsulate ((fff (x y) t))
             (local (defun fff (x y) (declare (ignore y)) x))
             (defthm fff-constraint
               (<= u (fff u v))))

(must-prove
 (<= a (+ a (nfix b)))
 :hints (("Goal" ;
          :consider fff-constraint)))

; By specifying a seed substitution we can select the correct one.

(must-prove
 (<= a (+ a (nfix b)))
 :hints (("Goal"
          :consider (fff-constraint :instance ((v b)) ))))

; Here is a vanilla flavored example of a realistic use of consider.

(encapsulate (((base) => *))
             (local (defun base () 45)))

(encapsulate (((op * *) => *))
             (local (defun op (i j) (declare (ignore i j)) 23))
             (defthm op-is-associative
               (equal (op (op i j) k) (op i (op j k))))
             (defthm op-is-commutative
               (equal (op i j) (op j i))))

(defthm op-is-commutative2
  (equal (op j (op i k)) (op i (op j k)))

  :hints
  (("Goal"
    :in-theory (disable op-is-commutative op-is-associative)
    :use ((:instance op-is-associative)
          (:instance op-is-commutative)
          (:instance op-is-associative (i j) (j i) (k k))))))

(defun map-op (x)
  (if (endp x)
      (base)
    (op (car x) (map-op (cdr x)))))

(in-theory (disable (:executable-counterpart map-op)))

(defthm map-op-rev
  (equal (map-op (rev x)) (map-op x)))

(defun sum-list (x)
  (if (consp x)
      (+ (car x) (sum-list (cdr x)))
    0))

(in-theory (disable associativity-of-+))

(defthm sum-list-rev
  (equal (sum-list (rev a)) (sum-list a))

  :hints (("Goal"
           :consider map-op-rev)))

; Now I need an example in which there are multiple substitutions,
; none succeeds outright, and I chose the best one.

; Never mind all this setup.  Just go to the thm below.

(defun propertyp (x) (equal x 23))

(encapsulate ((ff (x) t))
             (local (defun ff (x) (declare (ignore x)) 23))
             (defthm constraint-thm
               (propertyp (ff x))))

(in-theory (disable propertyp (propertyp)))

(defstub gg (x) t)
(defstub hh (x) t)

(skip-proofs
 (defthm derived-fact
   (propertyp (ff (gg (hh x))))
   :rule-classes nil))

(skip-proofs
 (defthm propertyp-true
   (equal (propertyp x)  t)))

(skip-proofs
 (defthm propertyp-false
   (equal (propertyp x)  nil)))

(in-theory (disable propertyp-true propertyp-false))

; This thm pushes one normal subgoal and then hits the :consider hint
; which generates 14 disjuncts.  By playing with the hints you can
; make them go away, one way or the other!  Then you can see what
; happens.

(must-not-prove
 (and (true-listp (app a b))
      (propertyp (app (rev (rev (rev (rev b)))) (rev (rev (rev a))))))
 :hints (("Subgoal 1"
;
          :consider derived-fact)
         ("Subgoal 1.D14'" :in-theory (enable propertyp-false))
         ("Subgoal 1.D13'" :in-theory (enable propertyp-false))
         ("Subgoal 1.D12'" :in-theory (enable propertyp-false))
         ("Subgoal 1.D11'" :in-theory (enable propertyp-false))
         ("Subgoal 1.D10'" :in-theory (enable propertyp-false))
         ("Subgoal 1.D9'" :in-theory (enable propertyp-false))
         ("Subgoal 1.D8'" :in-theory (enable propertyp-false))
         ("Subgoal 1.D7'" :in-theory (enable propertyp-false))
         ("Subgoal 1.D6'" :in-theory (enable propertyp-false))
         ("Subgoal 1.D5'" :in-theory (enable propertyp-false))
         ("Subgoal 1.D4'" :in-theory (enable propertyp-false))
         ("Subgoal 1.D3'" :in-theory (enable propertyp-false))
         ("Subgoal 1.D2'" :in-theory (enable propertyp-false))
         ("Subgoal 1.D1'" :in-theory (enable propertyp-false))
         )

 :otf-flg t)

(must-not-prove
 (and (true-listp (app a b))
      (propertyp (app (rev (rev (rev (rev b)))) (rev (rev (rev a))))))
 :hints (("Subgoal 1"
;
          :consider derived-fact)
         ("Subgoal 1.D14'" :in-theory (enable propertyp-false))
         ("Subgoal 1.D13'" :in-theory (enable propertyp-false))
;            ("Subgoal 1.D12'" :in-theory (enable propertyp-false))
         ("Subgoal 1.D11'" :in-theory (enable propertyp-false))
         ("Subgoal 1.D10'" :in-theory (enable propertyp-false))
         ("Subgoal 1.D9'" :in-theory (enable propertyp-false))
         ("Subgoal 1.D8'" :in-theory (enable propertyp-false))
         ("Subgoal 1.D7'" :in-theory (enable propertyp-false))
         ("Subgoal 1.D6'" :in-theory (enable propertyp-false))
         ("Subgoal 1.D5'" :consider derived-fact)
;            ("Subgoal 1.D4'" :in-theory (enable propertyp-false))
;            ("Subgoal 1.D3'" :in-theory (enable propertyp-false))
;            ("Subgoal 1.D2'" :in-theory (enable propertyp-false))
;            ("Subgoal 1.D1'" :in-theory (enable propertyp-false))
         )

 :otf-flg t)
