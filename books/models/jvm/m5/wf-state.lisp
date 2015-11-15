(in-package "M5")
(include-book "std/util/defrule" :dir :system)
(include-book "m5")

(acl2::defrule |bound? nil|
  (not (bound? x nil)))

(acl2::defruled |bound? bind|
  (equal (bound? x1 (bind x2 y alist))
         (if (equal x1 x2) (cons x1 y) (bound? x1 alist)))
  :induct (bind x2 y alist))

(acl2::defruled |len bind|
  (>= (len (bind x y alist)) (len alist))
  :induct (len alist)
  :rule-classes :linear)

(acl2::defrule bound?-bind
  (equal (bound? x (bind x y alist)) (cons x y))
  :use (:instance |bound? bind|
         (x1 x)
         (x2 x)))

(acl2::defrule |binding is cdr bound?|
  (equal (binding x alist) (cdr (bound? x alist))))

(defund indexed-alist-tail-p (alist n)
  (or (null alist)
      (and (consp alist)
           (consp (car alist))
           (equal (caar alist) n)
           (indexed-alist-tail-p (cdr alist) (1+ n)))))

(acl2::defrule |indexed-alist-tail-p is alistp|
  (implies
    (indexed-alist-tail-p alist n)
    (alistp alist))
  :enable indexed-alist-tail-p
  :induct (indexed-alist-tail-p list n))

(acl2::defruled |bound? in indexed-alist-tail-p|
  (implies
    (and
      (indexed-alist-tail-p alist n)
      (natp n))
    (equal (bound? i alist)
           (and (integerp i) (>= i n) (< i (+ n (len alist))) (nth (- i n) alist))))
  :enable indexed-alist-tail-p
  :induct (indexed-alist-tail-p alist n))

(defund indexed-alistp (alist)
  (indexed-alist-tail-p alist 0))

(acl2::defrule |indexed-alistp is alistp|
  (implies
    (indexed-alistp alist)
    (alistp alist))
  :enable indexed-alistp)

(acl2::defruled |bound? in indexed-alistp|
  (implies
    (indexed-alistp alist)
    (equal (bound? i alist)
           (and (natp i) (< i (len alist)) (nth i alist))))
  :enable indexed-alistp
  :use (:instance |bound? in indexed-alist-tail-p|
         (n 0)))

(acl2::defruled |bind in indexed-alistp|
  (implies
    (indexed-alistp alist)
    (equal (bind x y alist)
           (if (and (natp x) (< x (len alist)))
               (update-nth x (cons x y) alist)
               (append alist (list (cons x y))))))
  :prep-lemmas (
    (acl2::defrule lemma
      (implies
        (and
          (indexed-alist-tail-p alist n)
          (natp n))
        (equal (bind x y alist)
               (if (and (integerp x)
                        (>= x n)
                        (< x (+ n (len alist))))
                   (update-nth (- x n) (cons x y) alist)
                   (append alist (list (cons x y))))))
      :enable indexed-alist-tail-p
      :induct (indexed-alist-tail-p alist n)))
  :enable indexed-alistp)

(acl2::defruled |indexed-alistp bind|
  (implies
    (indexed-alistp alist)
    (equal (indexed-alistp (bind x y alist))
           (and (natp x) (<= x (len alist)))))
  :prep-lemmas (
    (acl2::defrule lemma
      (implies
        (and
          (indexed-alist-tail-p alist n)
          (natp n))
        (equal (indexed-alist-tail-p (bind x y alist) n)
               (and (integerp x) (>= x n) (<= x (+ n (len alist))))))
      :enable indexed-alist-tail-p
      :induct (indexed-alist-tail-p alist n)))
  :enable indexed-alistp)

(acl2::defruled |indexed-alistp bind when bound?|
  (implies
    (and
      (indexed-alistp alist)
      (bound? x alist))
    (indexed-alistp (bind x y alist)))
  :enable |indexed-alistp bind|
  :use (:instance |bound? in indexed-alistp|
         (i x)))

(acl2::defruled |indexed-alistp bind when len|
  (implies
    (and
      (indexed-alistp alist)
      (equal x (len alist)))
    (indexed-alistp (bind x y alist)))
  :enable |indexed-alistp bind|)

(local (acl2::defruled |indexed-alistp bind rrefToThread|
  (implies
    (and
      (indexed-alistp tt)
      (rrefToThread rref tt)
      (bound? th tt))
    (indexed-alistp (bind (rreftothread rref tt)
                          y1
                          (bind th y2 tt))))
  :prep-lemmas (
    (acl2::defrule lemma
      (implies
        (and
          (indexed-alist-tail-p tt n)
          (natp n)
          (rrefToThread rref tt))
        (and (integerp (rrefToThread rref tt))
             (>= (rrefToThread rref tt) n)
             (< (rrefToThread rref tt) (+ n (len tt)))))
      :enable (indexed-alist-tail-p rrefToThread)
      :induct (indexed-alist-tail-p tt n)
      :rule-classes ()))
  :enable |indexed-alistp bind|
  :disable (bind bound?)
  :cases ((not (and (natp (rreftoThread rref tt))
                    (< (rrefToThread rref tt)
                       (len tt))))
          (not (<= (len tt) (len (bind th y2 tt)))))
  :hints (
    ("subgoal 3" :in-theory (enable |bound? in indexed-alistp|)
                 :use (:instance |indexed-alistp bind|
                        (x (rrefToThread rref tt))
                        (y y1)
                        (alist (bind th y2 tt))))
    ("subgoal 2" :in-theory (enable indexed-alistp)
                 :use (:instance lemma
                        (n 0)))
    ("subgoal 1" :in-theory (enable |len bind|)))))

(local (defthm states
  (and (equal (thread-table (make-state tt h c)) tt)
       (equal (heap (make-state tt h c)) h)
       (equal (class-table (make-state tt h c)) c))))

(local (in-theory (disable make-state thread-table heap class-table)))

(local (acl2::defrule |indexed-alistp thread-table|
  (implies
    (indexed-alistp (thread-table s))
    (indexed-alistp (thread-table (step th s))))
  :enable (|indexed-alistp bind when bound?|
           |indexed-alistp bind rrefToThread|)
  :disable (bound? binding make-thread field-long-or-double
            bits2fp fp2fp fp2int
            fpadd fpcmp fpdiv fpmul fpneg fpsqrt fprem fpsub
            shl shr iushr lushr
            truncate abs
            arg1 arg2 arg3
            next-inst bind-formals)
  :cases ((bound? th (thread-table s)))))

(defund wf-state (s)
  (and
    (indexed-alistp (thread-table s))))

(acl2::defrule |wf-state invariant|
  (implies
    (wf-state s)
    (wf-state (step th s)))
  :enable wf-state
  :disable step)
