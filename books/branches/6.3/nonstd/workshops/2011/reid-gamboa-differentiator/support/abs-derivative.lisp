(in-package "ACL2")

(include-book "differentiator")

(defthm x-y/y-x
  (implies (and (realp x)
                (realp y)
                (not (equal x 0)))
           (equal (/ x (- x))
                  -1)))

; Discuss what happens without these hints

(defthm abs-derivative
  (implies (and (realp x) (not (equal x 0))
                (realp y) (not (equal y 0))
                (standardp x)
                (i-close x y) (not (equal x y)))
           (equal (/ (- (abs x) (abs y))
                     (- x y))
                  (signum x)))
  :hints (("Goal"
           :in-theory (enable i-close i-small abs)
           :use (:instance x-y/y-x (x (- y x))))))

(defthmd close-if-equal
  (implies (and (acl2-numberp a)
                (acl2-numberp b)
                (equal a b))
           (i-close a b)))

(defthmd elem-abs-close
  (implies (and (realp x) (not (equal x 0))
                (realp y) (not (equal y 0))
                (standardp x)
                (i-close x y) (not (equal x y)))
           (i-close (/ (- (abs x) (abs y))
                       (- x y))
                    (signum x)))
  :hints (("Goal"
           :in-theory (disable distributivity)
           :use ((:instance abs-derivative)
                 (:instance close-if-equal
                           (a (/ (- (abs x) (abs y))
                                 (- x y)))
                           (b (signum x)))))))

(defthm elem-abs-number
  (implies (and (realp x) (not (equal x 0)))
           (acl2-numberp (abs x))))

(defthm-std elem-abs-standard
  (implies (and (realp x) (not (equal x 0))
                (standardp x))
           (standardp (abs x))))

(defthm elem-abs-continuous
  (implies (and (realp x) (not (equal x 0))
                (realp y) (not (equal y 0))
                (standardp x)
                (i-close x y))
           (i-close (abs x)
                    (abs y)))
  :hints (("Goal" :in-theory (enable i-close i-small abs))))

(defthm elem-abs-prime-number
  (implies (and (realp x) (not (equal x 0)))
           (acl2-numberp (signum x))))

(defthm elem-abs-prime-standard
  (implies (and (realp x) (not (equal x 0))
                (standardp x))
           (standardp (signum x))))

(defthm elem-abs-prime-continuous
  (implies (and (realp x) (not (equal x 0))
                (realp y) (not (equal y 0))
                (standardp x)
                (i-close x y))
           (i-close (signum x) (signum y)))
  :hints (("Goal" :in-theory (enable i-close i-small))))

(def-elem-derivative abs
  elem-abs
  (and (realp x) (not (equal x 0)))
  (signum x))
