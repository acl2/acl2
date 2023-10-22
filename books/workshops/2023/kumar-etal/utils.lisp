(in-package "ACL2S")
;; Some utility functions

(set-acl2s-property-table-proof-timeout 1000)
(set-defunc-timeout 1000)

(defdata lol (listof tl))
(defdata lor (listof rational))
(defdata lon (listof nat))

(definecd map-diff (m1 m2 :lol) :lol
  (match (list m1 m2)
    ((() &) '())
    ((& ()) '())
    ((((x . xs) . rst1) ((& . ys) . rst2))
     (cons `(,x . ,(set-difference-equal xs ys))
           (map-diff rst1 rst2)))
    (& nil)))

(definec <<= (x y :all) :bool
  (or (== x y)
      (<< x y)))

(definec insert (a :all x :tl) :tl
  (match x
    (() (list a))
    ((e . es) (if (<<= a e)
                  (cons a x)
                (cons e (insert a es))))))

(definec isort (x :tl) :tl
  (match x
    (() ())
    ((e . es) (insert e (isort es)))))

(definec natlist (n :nat) :nat-list
  (if (zp n)
      '()
    (cons n (natlist (1- n)))))

(definec natlist-from (i n :nat) :nat-list
  (if (zp n)
      '()
    (cons i (natlist-from (1+ i) (1- n)))))

(definec grab (n :nat x :tl) :tl
  (if (or (zp n) (endp x))
      nil
    (cons (car x) (grab (1- n) (cdr x)))))

(defthm mvnth2mymvnth
  (=> (^ (posp k) (natp s))
      (natp (mv-nth 0 (defdata::genrandom-seed k s))))
  :hints (("goal" :use (:instance defdata::mv-nth--to--my-mv-nth
                                  (defdata::x 0) (defdata::y (defdata::genrandom-seed k s))))))

(defthm mvnth2mymvnth1
  (=> (^ (posp k) (natp s))
      (natp (mv-nth 1 (defdata::genrandom-seed k s))))
  :hints (("goal" :use (:instance defdata::mv-nth--to--my-mv-nth
                                  (defdata::x 0) (defdata::y (defdata::genrandom-seed k s))))))

(definec shuffle (ls :tl s :nat) :tl
  (b* (((mv k s) (defdata::genrandom-seed
                   (1- (expt 2 31))
                   (mod s (expt 2 31))))
       (i (mod k 2)))
    (match (list ls i)
      ((() &) ())
      (((l . rst) 0) (cons l (shuffle rst s)))
      (((l . rst) 1) (app (shuffle rst s) (list l))))))

(definecd rem-vals (al :lol rl :tl) :alist
  (match al
    (() '())
    (((k . v) . rst)
     (cons `(,k . ,(set-difference-equal v rl))
           (rem-vals rst rl)))
    (& nil)))

(property isort-lor (ls :lor)
  (lorp (isort ls)))

(property isort-cons (ls :lor)
  (=> (consp ls)
      (consp (isort ls))))

(definecd median-help (xs ys :lor) :rational
  :ic (consp xs)
  (cond
   ((= (len xs) (1+ (len ys))) (car xs))
   ((= (len xs) (len ys)) (/ (+ (car xs) (car ys)) 2))
   ((< (len xs) (len ys)) 0)
   (t (median-help (cdr xs) `(,(car xs) . ,ys)))))

(definecd median (ls :lor) :rational
  :ic (consp ls)
  (median-help (isort ls) '()))
