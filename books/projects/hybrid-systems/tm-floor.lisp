; Copyright (C) 2007 by Shant Harutunian
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "arith-nsa4")
(include-book "nsa")
(include-book "computed-hints")

(in-theory (disable i-large))
(in-theory (disable standard-part-<=))

(defthm tm-floor-thm-hint-1
  (implies
   (and
    (realp tm)
    (realp eps)
    (< 0 eps)
    (i-small eps))
   (equal (standard-part (* eps (floor1 (/ tm eps))))
          (standard-part tm)))
  :rule-classes nil
  :hints ((standard-part-hint stable-under-simplificationp clause)
          ("Goal" :in-theory (disable  <-CANCEL-DIVISORS)
           :use ((:instance pos-factor-<-thm (x (- (/ tm eps) 1))
                            (y (floor1 (/ tm eps))) (a eps))
                 (:instance pos-factor-<=-thm (x (floor1 (/ tm eps)))
                            (y (/ tm eps)) (a eps))))))

(defthm tm-floor-thm
  (implies
   (and
    (realp tm)
    (standard-numberp tm))
   (equal (STANDARD-PART (* (/ (I-LARGE-INTEGER))
                            (FLOOR1 (* (I-LARGE-INTEGER) TM))))
          tm))
  :hints (("Goal" :use ((:instance tm-floor-thm-hint-1
                                   (eps (/ (i-large-integer))))))))

(defthm tm-floor-limited-thm
  (implies
   (and
    (realp tm)
    (standard-numberp tm))
   (i-limited (* (/ (I-LARGE-INTEGER))
                 (FLOOR1 (* (I-LARGE-INTEGER) TM)))))
  :hints (("Goal" :use ((:instance standard+small->i-limited
                                   (x (standard-part
                                       (* (/ (I-LARGE-INTEGER))
                                          (FLOOR1 (* (I-LARGE-INTEGER) TM)))))
                                   (eps (- (* (/ (I-LARGE-INTEGER))
                                              (FLOOR1 (* (I-LARGE-INTEGER) TM)))
                                           (standard-part
                                            (* (/ (I-LARGE-INTEGER))
                                               (FLOOR1 (* (I-LARGE-INTEGER) TM)))
                                            ))))))))

(defthm tm-floor-*a-hint-1
  (implies
   (and
    (realp tm)
    (realp a)
    (i-limited a)
    (standard-numberp tm))
   (equal (STANDARD-PART (* a (/ (I-LARGE-INTEGER))
                            (FLOOR1 (* (I-LARGE-INTEGER) TM))))
          (standard-part (* a tm))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable *-COMMUT-3WAY))))

(defthm tm-floor-*a-thm
  (implies
   (and
    (realp tm)
    (realp a)
    (i-limited a)
    (standard-numberp tm))
   (equal (STANDARD-PART (* (/ (I-LARGE-INTEGER)) a
                            (FLOOR1 (* (I-LARGE-INTEGER) TM))))
          (standard-part (* a tm))))
  :hints (("Goal" :in-theory (disable i-large)
           :use ((:instance tm-floor-*a-hint-1)))))

(defun tm-fun (tm)
  (* (/ (I-LARGE-INTEGER))
     (FLOOR1 (* (I-LARGE-INTEGER) TM))))

(defthm tm-fun-limited-thm
  (implies
   (and
    (realp a)
    (realp tm)
    (standard-numberp tm))
   (i-limited (tm-fun tm))))

(defthm tm-fun-standard-part-thm
  (implies
   (and
    (realp a)
    (realp tm)
    (standard-numberp tm))
   (equal (standard-part (tm-fun tm))
          tm)))

(defthm tm-fun-rw-1-thm
  (implies
   (and
    (realp tm)
    (standard-numberp tm))
   (equal (* (/ (I-LARGE-INTEGER))
             (FLOOR1 (* (I-LARGE-INTEGER) TM)))
          (tm-fun tm))))

(defthm tm-fun-rw-2-thm
  (implies
   (and
    (realp a)
    (realp tm)
    (standard-numberp tm))
   (equal (* (/ (I-LARGE-INTEGER)) a
             (FLOOR1 (* (I-LARGE-INTEGER) TM)))
          (* (tm-fun tm) a)))
  :hints (("Goal" :in-theory (disable tm-fun-rw-1-thm))))

(defthm tm-fun-rw-3-thm
  (implies
   (and
    (realp a)
    (realp tm)
    (standard-numberp tm))
   (equal (* (/ (I-LARGE-INTEGER))
             (FLOOR1 (* (I-LARGE-INTEGER) TM))
             a)
          (* (tm-fun tm) a)))
  :hints (("Goal" :in-theory (disable tm-fun-rw-1-thm tm-fun-rw-2-thm))))

(defthm tm-fun-rw-4-thm
  (implies
   (and
    (realp a)
    (realp b)
    (realp tm)
    (standard-numberp tm))
   (equal (* (/ (I-LARGE-INTEGER))
             a
             (FLOOR1 (* (I-LARGE-INTEGER) TM))
             b)
          (* (tm-fun tm) a b)))
  :hints (("Goal" :in-theory (disable tm-fun-rw-1-thm
                                      tm-fun-rw-2-thm
                                      tm-fun-rw-3-thm))))

;; tm-fun should be disabled. Enabling it may result in rewrite loops.

(in-theory (disable tm-fun))

(defun eps-n-fun (eps n)
  (* eps n))

(defthm eps-n-fun-type-thm
  (implies
   (and
    (realp eps)
    (realp n))
   (realp (eps-n-fun eps n)))
  :rule-classes :type-prescription)

(defthm eps-n-fun-0-thm
  (equal (eps-n-fun eps 0) 0))

(defthm eps-n-fun-limited-thm
  (implies
   (and
    (realp eps)
    (integerp n)
    (i-limited (* eps n)))
   (i-limited (eps-n-fun eps n))))

(defthm eps-n-fun-rw-1-thm
  (implies
   (and
    (integerp n)
    (realp eps)
    (syntaxp (eq eps 'eps))
    (i-limited (* eps n)))
   (equal (* eps n)
          (eps-n-fun eps n))))

(defthm eps-n-fun-rw-2-thm
  (implies
   (and
    (realp a)
    (syntaxp (eq eps 'eps))
    (integerp n)
    (realp eps)
    (i-limited (* eps n)))
   (equal (* eps a n)
          (* (eps-n-fun eps n) a)))
  :hints (("Goal" :in-theory (disable eps-n-fun-rw-1-thm))))

(defthm eps-n-fun-rw-3-thm
  (implies
   (and
    (realp a)
    (syntaxp (eq eps 'eps))
    (integerp n)
    (realp eps)
    (i-limited (* eps n)))
   (equal (* eps n a)
          (* (eps-n-fun eps n) a)))
  :hints (("Goal" :in-theory (disable eps-n-fun-rw-1-thm
                                      eps-n-fun-rw-2-thm))))

(defthm eps-n-fun-rw-4-thm
  (implies
   (and
    (realp a)
    (realp b)
    (syntaxp (eq eps 'eps))
    (integerp n)
    (realp eps)
    (i-limited (* eps n)))
   (equal (* eps a n b)
          (* (eps-n-fun eps n) a b)))
  :hints (("Goal" :in-theory (disable eps-n-fun-rw-1-thm
                                      eps-n-fun-rw-2-thm
                                      eps-n-fun-rw-3-thm))))

;; eps-n-fun should be disabled. Enabling it may result in rewrite loops.

(in-theory (disable eps-n-fun))

(defun tm-eps-fun (tm eps)
  (* eps
     (FLOOR1 (/ TM eps))))

(defthm tm-eps-type
  (implies
   (realp eps)
   (realp (tm-eps-fun tm eps)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable tm-eps-fun))))

(defthm tm-eps-pos-thm
  (implies
   (and
    (realp tm)
    (realp eps)
    (<= 0 tm)
    (< 0 eps))
   (<= 0 (tm-eps-fun tm eps)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable tm-eps-fun))))

(defthm tm-eps-fun-standard-part-thm
  (implies
   (and
    (realp eps)
    (< 0 eps)
    (i-small eps)
    (realp tm)
    (standard-numberp tm))
   (equal (standard-part (tm-eps-fun tm eps))
          tm))
  :hints (("Goal" :use ((:instance tm-floor-thm-hint-1)))))

(defthm tm-eps-fun-limited-thm
  (implies
   (and
    (realp eps)
    (< 0 eps)
    (i-small eps)
    (realp tm)
    (standard-numberp tm))
   (i-limited (tm-eps-fun tm eps)))
  :hints (("Goal" :in-theory (disable tm-eps-fun)
           :use ((:instance standard+small->i-limited
                            (x (standard-part (tm-eps-fun tm eps)))
                            (eps (- (tm-eps-fun tm eps)
                                    (standard-part
                                     (tm-eps-fun tm eps)))))))))

(defthm tm-eps-fun-rw-1-thm
  (implies
   (and
    (realp eps)
    (< 0 eps)
    (i-small eps)
    (realp tm)
    (standard-numberp tm))
   (equal (* eps
             (FLOOR1 (* (/ EPS) TM)))
          (tm-eps-fun tm eps))))

(defthm tm-eps-fun-rw-2-thm
  (implies
   (and
    (realp eps)
    (< 0 eps)
    (i-small eps)
    (realp a)
    (realp tm)
    (standard-numberp tm))
   (equal (* eps a
             (FLOOR1 (* (/ EPS) TM)))
          (* (tm-eps-fun tm eps) a)))
  :hints (("Goal" :in-theory (disable tm-eps-fun-rw-1-thm))))

(defthm tm-eps-fun-rw-3-thm
  (implies
   (and
    (realp eps)
    (< 0 eps)
    (i-small eps)
    (realp a)
    (realp tm)
    (standard-numberp tm))
   (equal (* eps
             (FLOOR1 (* (/ EPS) TM))
             a)
          (* (tm-eps-fun tm eps) a)))
  :hints (("Goal" :in-theory (disable tm-eps-fun-rw-1-thm
                                      tm-eps-fun-rw-2-thm))))

(defthm tm-eps-fun-rw-4-thm
  (implies
   (and
    (realp eps)
    (< 0 eps)
    (i-small eps)
    (realp a)
    (realp b)
    (realp tm)
    (standard-numberp tm))
   (equal (* eps
             a
             (FLOOR1 (* (/ EPS) TM))
             b)
          (* (tm-eps-fun tm eps) a b)))
  :hints (("Goal" :in-theory (disable tm-eps-fun-rw-1-thm
                                      tm-eps-fun-rw-2-thm
                                      tm-eps-fun-rw-3-thm))))

;; tm-eps-fun should be disabled. Enabling it may result in rewrite loops.

(in-theory (disable tm-eps-fun))
