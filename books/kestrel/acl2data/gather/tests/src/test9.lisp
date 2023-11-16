; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Tests of :expansion-stack

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/util/defaggregate" :dir :system)
(include-book "std/util/def-bound-theorems" :dir :system)

(in-theory (theory 'ground-zero))
(in-theory (disable car-cons))

(defmacro my-defthm (&rest args)
  `(defthm ,@args))

(defthm thm1
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :in-theory (enable car-cons)))
  :rule-classes nil)

(local (defthm thm1-local
           (equal (append (append x y) z)
                  (append x y z))
         :hints (("Goal" :in-theory (enable car-cons)))
         :rule-classes nil))

(my-defthm thm2
           (equal (append (append x y) z)
                  (append x y z))
           :hints (("Goal" :in-theory (enable car-cons)))
           :rule-classes nil)

(make-event
 '(defthm thm3
   (equal (append (append x y) z)
    (append x y z))
   :hints (("Goal" :in-theory (enable car-cons)))
   :rule-classes nil))

(defsection section1
    (encapsulate
        ()
        (my-defthm thm4
         (equal (append (append x y) z)
                (append x y z))
         :hints (("Goal" :in-theory (enable car-cons)))
         :rule-classes nil))
  (progn
    (defrule thm5
        (equal (append (append x y) z)
               (append x y z))
      :hints (("Goal" :in-theory (enable car-cons)))
      :rule-classes nil)))

(std::defaggregate employee  ;; structure name
    (name salary position)   ;; fields
  :tag :employee             ;; options
  )

(encapsulate
    ()
    (set-enforce-redundancy t)
  (defthm consp-when-employee-p
      (implies (employee-p x) (consp x))
    :rule-classes :compound-recognizer))

(local
 (with-prover-step-limit 10000
   (std::defthm-natp thm6
       :hyp (and (natp x) (< x 10))
       :concl (len (make-list x)))))

(define foo (x)
  (cons x x)
  ///
  (defruled thm7
      (consp (foo x)))
  (defruled thm8
      (equal (foo x)
             (cons x x))))

(define bar (x)
  (cons x x)
  ///
  (std::deflist nat-free-listp (x)
    (natp x)
    :negatedp t))

; Redundant
(defthm nat-free-listp-of-cons
    (equal (nat-free-listp (cons a x))
           (and (not (natp a)) (nat-free-listp x)))
  :rule-classes ((:rewrite)))
