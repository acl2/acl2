; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; Test :in-theory

(in-theory (disable append car-cons))

(defthm app-assoc-rewrite
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :in-theory (enable append car-cons nth))))

(defthm app-assoc-backwards
  (equal (append x y z)
         (append (append x y) z))
  :hints (("Goal" :in-theory (enable append car-cons nth))))

(defthm app-assoc-1
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :in-theory (e/d (append car-cons nth)
                                  (app-assoc-backwards))))
  :rule-classes nil)

(defthm app-assoc-2
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :in-theory (e/d nil
                                  (app-assoc-backwards))))
  :rule-classes nil)

(defthm app-assoc-3
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :in-theory (e/d nil
                                  (nth app-assoc-backwards))))
  :rule-classes nil)

(in-theory (disable app-assoc-backwards app-assoc-rewrite))

(defthm app-assoc-4
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :in-theory (e/d (nth app-assoc-rewrite)
                                  nil)))
  :rule-classes nil)

; Test :use and :expand

(in-theory (enable (:i append) car-cons))

(defthm app-assoc-5
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :use (app-assoc-4)))
  :rule-classes nil)

(defthm app-assoc-5b
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :use app-assoc-4))
  :rule-classes nil)

(defthm app-assoc-6
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :use (app-assoc-4 nth)))
  :rule-classes nil)

(defthm app-assoc-7
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal"
           :expand ((:free (b) (append x b))
                    (:free (a b) (append (cons (car x) a) b)))))
  :rule-classes nil)

(defthm app-assoc-8
  (equal (append (append u v) w)
         (append u v w))
  :hints (("Goal" :by app-assoc-7))
  :rule-classes nil)

(defthm app-assoc-9
  (and (equal (append (append x y) z)
              (append x y z))
       (equal (append (append u v) w)
              (append u v w)))
  :hints (("Goal" :use (app-assoc-7 app-assoc-8 nth)))
  :rule-classes nil)

; Test do-not

(in-theory (enable append car-cons))

(defthm app-assoc-backwards-with-hyp ; hence not available for preprocess
  (implies (true-listp x)
           (equal (append x y z)
                  (append (append x y) z))))

(defthm app-assoc-rewrite-with-hyp ; hence not available for preprocess
  (implies (true-listp x)
           (equal (append (append x y) z)
                  (append x y z))))

(defthm app-assoc-10
  (implies (true-listp x)
           (equal (append (append x y) z)
                  (append x y z)))
  :hints (("Goal" :do-not '(simplify fertilize generalize))
          ("Subgoal *1/3" :do-not ())
          ("Subgoal *1/1" :do-not ()))
  :rule-classes nil)
