#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")

(acl2::begin-book);$ACL2s-Preamble$|#


(in-package "DEFDATA")

(set-verify-guards-eagerness 2)
(set-state-ok t)

(include-book "num-list-fns")

(local (include-book "num-list-thms"))

(local (in-theory (disable rem floor)))
(local (include-book "rem-and-floor"))

(defun weighted-split-nat-step (weights x old-results)
  (declare (xargs :guard (and (2+-listp weights)
                              (natp x)
                              (nat-listp old-results)
                              (= (len weights) (len old-results)))))
  (if (mbe :logic (or (endp weights)
                      (endp old-results))
           :exec (endp weights))
      nil
    (let ((weight (car weights)))
      (cons (+ (* weight (car old-results))
               (rem x weight))
            (weighted-split-nat-step (cdr weights)
                                     (floor x weight)
                                     (cdr old-results))))))


(local (defthm weighted-split-nat-step--true-listp
         (true-listp (weighted-split-nat-step w x r))
         :rule-classes (:type-prescription :rewrite)))

(local (defthm weighted-split-nat-step--len
         (equal (len (weighted-split-nat-step w x r))
                (min (len w) (len r)))))

(local (defthm weighted-split-nat-step--nat-listp
         (implies (and (nat-listp w)
                       (integerp x)
                       (<= 0 x)
                       (nat-listp r))
                  (nat-listp (weighted-split-nat-step w x r)))
         :rule-classes (:type-prescription :rewrite)))

(local (defthm weighted-split-nat-step--consp
         (implies (and (consp w)
                       (consp r))
                  (consp (weighted-split-nat-step w x r)))
         :rule-classes (:type-prescription :rewrite)))


(local (defthm weighted-split-nat-step--bound-old
         (implies (and (2+-listp w)
                       (integerp x)
                       (<= 0 x)
                       (nat-listp r)
                       (equal (len w) (len r)))
                  (<=-lists (weighted-split-nat-step w x r)
                            (+-lists
                             (*-lists r
                                      w)
                             w)))
         :rule-classes (:rewrite)))


(local
 (encapsulate nil
   (local (include-book "arithmetic-5/top" :dir :system))
   
   (local (SET-DEFAULT-HINTS '((acl2::NONLINEARP-DEFAULT-HINT
                                acl2::STABLE-UNDER-SIMPLIFICATIONP
                                acl2::HIST
                                acl2::PSPV))))

  (defthm <=-lists--scale
           (implies (and (rationalp v)
                         (<= 0 v)
                         (rationalp w)
                         (<= v w)
                         (nat-listp l))
                    (<=-lists (scale l v)
                              (scale l w))))

  (defthm <=-lists--scale2
           (implies (and (<=-lists l1
                                   (scale l2 v))
                         (rationalp v)
                         (<= 0 v)
                         (rationalp w)
                         (<= v w)
                         (nat-listp l2))
                    (<=-lists l1
                              (scale l2 w))))

  (defthm <=-lists--scale3
           (implies (and (rationalp v)
                         (<= 0 v)
                         (nat-listp l1)
                         (nat-listp l2)
                         (<=-lists l1 l2))
                    (<=-lists (scale l1 v)
                              (scale l2 v))))

  (defthm <=-lists--scale4
           (implies (and (rationalp v1)
                         (<= 0 v1)
                         (rationalp v2)
                         (<= 0 v2)
                         (nat-listp l1)
                         (nat-listp l2)
                         (<=-lists l1 l2)
                         (<= v1 v2))
                    (<=-lists (scale l1 v1)
                              (scale l2 v2))))

  
  (defthm <=-lists--shift
    (implies (and (rationalp v)
                  (rationalp w)
                  (<= v w)
                  (rational-listp l))
             (<=-lists (shift l v)
                       (shift l w))))

  (defthm <=-lists--shift2
    (implies (and (<=-lists l1
                            (shift l2 v))
                  (rationalp v)
                  (rationalp w)
                  (<= v w)
                  (rational-listp l2))
             (<=-lists l1
                       (shift l2 w))))

  (defthm <=-lists--shift3
           (implies (and (rationalp v)
                         (rational-listp l1)
                         (rational-listp l2)
                         (<=-lists l1 l2))
                    (<=-lists (shift l1 v)
                              (shift l2 v))))

  (defthm <=-lists--shift4
           (implies (and (rationalp v1)
                         (rationalp v2)
                         (rational-listp l1)
                         (rational-listp l2)
                         (<=-lists l1 l2)
                         (<= v1 v2))
                    (<=-lists (shift l1 v1)
                              (shift l2 v2))))
  ))

(local (defthm shift--<=
         (equal (<=-lists (shift l v1)
                          (shift l v2))
                (or (endp l)
                    (<= v1 v2)))))

(local (defthm weighted-split-nat-step--bound
         (implies (and (2+-listp w)
                       (integerp x)
                       (<= 0 x)
                       (nat-listp r)
                       (equal (len w) (len r)))
                  (<=-lists (weighted-split-nat-step w x r)
                            (shift
                             (*-lists r w)
                             x)))))

(local
 (encapsulate nil
   (local (include-book "arithmetic-5/top" :dir :system))
   
   (local (SET-DEFAULT-HINTS '((acl2::NONLINEARP-DEFAULT-HINT
                                acl2::STABLE-UNDER-SIMPLIFICATIONP
                                acl2::HIST
                                acl2::PSPV))))
   
   (defthm weighted-split-nat-step--bound2--lemma
     (implies (and (nat-listp r)
                   (2+-listp w)
                   (equal (len r) (len w)))
              (<=-lists (*-lists r w)
                        (scale r (product-list w)))))))


(local
 (encapsulate nil
   (local (defthm <=-lists--transitive--force
            (implies (and (<=-lists a b)
                          (force (<=-lists b c)))
                     (<=-lists a c))
            :rule-classes ((:rewrite :match-free :all))))

  (local (defthm <=-lists--scale4--force
           (implies (and (rationalp v1)
                         (<= 0 v1)
                         (rationalp v2)
                         (<= 0 v2)
                         (nat-listp l1)
                         (nat-listp l2)
                         (force (<=-lists l1 l2))
                         (force (<= v1 v2)))
                    (<=-lists (scale l1 v1)
                              (scale l2 v2)))))

  (local (defthm <=-lists--shift4--force
           (implies (and (rationalp v1)
                         (rationalp v2)
                         (rational-listp l1)
                         (rational-listp l2)
                         (force (<=-lists l1 l2))
                         (force (<= v1 v2)))
                    (<=-lists (shift l1 v1)
                              (shift l2 v2)))))
   
  (local (include-book "arithmetic-5/top" :dir :system))
  
  (local (SET-DEFAULT-HINTS '((acl2::NONLINEARP-DEFAULT-HINT
                               acl2::STABLE-UNDER-SIMPLIFICATIONP
                               acl2::HIST
                               acl2::PSPV))))

   (defthm weighted-split-nat-step--bound2
     (implies (and (2+-listp w)
                   (integerp x)
                   (<= 0 x)
                   (nat-listp r)
                   (equal (len w) (len r)))
              (<=-lists (weighted-split-nat-step w x r)
                        (shift
                         (scale r (product-list w))
                         x))))))


(local
 (defthm get-weights-factor-->=2
   (implies (and (2+-listp x)
                 (consp x))
            (<= 2 (product-list x)))
   :rule-classes (:linear :rewrite)))


(defun rot-list (x)
  (declare (xargs :guard (and (true-listp x)
                              (consp x))))
  (append (cdr x) (list (car x))))

(local
 (defthm rot-list--consp
   (implies (consp x)
            (consp (rot-list x)))
   :rule-classes (:type-prescription :rewrite)))

(local (defthm consp-cdr-append
         (implies (and (consp x)
                       (consp y))
                  (consp (cdr (append x y))))))

(local
 (defthm rot-list--consp-cdr
   (implies (and (consp x)
                 (consp (cdr x)))
            (consp (cdr (rot-list x))))
   :rule-classes (:type-prescription :rewrite)))

(local
 (defthm len-append-single
   (equal (len (append x (list y)))
          (+ 1 (len x)))))

(local
 (defthm rot-list--len
   (implies (consp x)
            (equal (len (rot-list x))
                   (len x)))))

(local (defthm rot-list--nat-listp
         (implies (and (nat-listp x)
                       (consp x))
                  (nat-listp (rot-list x)))))

(local (defthm rot-list--2+-listp
         (implies (and (2+-listp x)
                       (consp x))
                  (2+-listp (rot-list x)))))

(local (defthm rot-list--product-list
         (implies (consp x)
                  (equal (product-list (rot-list x))
                         (product-list x)))))

(local (defthm all-<=--rot-list
         (implies (consp l)
                  (equal (all-<= (rot-list l)
                                 x)
                         (all-<= l
                                 x)))))

(local (in-theory (disable rot-list)))

(defun weighted-split-nat1 (weights weights-factor x)
  (declare (xargs :measure (nfix x)
                  :verify-guards nil
                  :guard (and (2+-listp weights)
                              (equal weights-factor (product-list weights))
                              (consp weights)
                              (natp x))))
  (if (mbe :logic (or (zp x)
                      (endp weights)
                      (not (equal weights-factor (product-list weights)))
                      (not (2+-listp weights)))
           :exec (zp x))
    (make-list (len weights) :initial-element 0)
    (weighted-split-nat-step weights
                             (rem x weights-factor)
                             (rot-list
                              (weighted-split-nat1
                               (rot-list weights)
                               weights-factor
                               (floor x weights-factor))))))

(local
 (defthm weighted-split-nat1--consp
   (implies (consp weights)
            (consp (weighted-split-nat1 weights weights-factor x)))))

(local
 (defthm weighted-split-nat1--len
   (equal (len (weighted-split-nat1 weights weights-factor x))
          (len weights))))

(local
 (defthm weighted-split-nat1--nat-listp
   (implies (and (2+-listp weights)
                 (consp weights)
                 (equal weights-factor (product-list weights))
                 (integerp x)
                 (<= 0 x))
            (nat-listp (weighted-split-nat1 weights weights-factor x)))
   :rule-classes ((:rewrite)
                  (:rewrite :corollary
                   (implies (and (2+-listp weights)
                                 (consp weights)
                                 (equal weights-factor (product-list weights))
                                 (integerp x)
                                 (<= 0 x))
                            (true-listp (weighted-split-nat1 weights weights-factor x)))))))

(verify-guards weighted-split-nat1)

(local
 (defthm weighted-split-nat1--<=-induction-step1
   (implies (and (2+-listp weights)
                 (consp weights)
                 (integerp x)
                 (<= 0 x))
            (<=-lists (weighted-split-nat-step
                       weights
                       (rem x (product-list weights))
                       (rot-list (weighted-split-nat1 (rot-list weights)
                                                      (product-list weights)
                                                      (floor x (product-list weights)))))
                      (shift
                       (scale (rot-list (weighted-split-nat1 (rot-list weights)
                                                             (product-list weights)
                                                             (floor x (product-list weights))))
                              (product-list weights))
                       (rem x (product-list weights)))))
   :rule-classes nil))

(local
 (encapsulate nil
   (local (include-book "arithmetic-3/top" :dir :system))
   
   (local (SET-DEFAULT-HINTS '((acl2::NONLINEARP-DEFAULT-HINT
                                acl2::STABLE-UNDER-SIMPLIFICATIONP
                                acl2::HIST
                                acl2::PSPV))))
   
   (local (defthm all-<=--shift
            (equal (all-<= (shift l v)
                           x)
                   (all-<= l
                           (- x v)))))
   
   (local (defthm all-<=--scale
            (implies (and (rationalp v)
                          (< 0 v))
                     (equal (all-<= (scale l v)
                                    x)
                            (all-<= l
                                    (/ x v))))))

   (local (defthm blah
            (implies (and (equal n (len l)) 
                          (<=-lists l
                                    (make-list-logic x n))
                          (force (<= x y)))
                     (all-<= l
                             y))))

   (defthm weighted-split-nat1--<=-induction-step2
     (implies (and (2+-listp weights)
                   (consp weights)
                   (integerp x)
                   (<= 0 x)
                   (all-<= (weighted-split-nat1 (rot-list weights)
                                                (product-list weights)
                                                (floor x (product-list weights)))
                           (floor x (product-list weights))))
              (all-<= (shift
                       (scale (rot-list (weighted-split-nat1 (rot-list weights)
                                                             (product-list weights)
                                                             (floor x (product-list weights))))
                              (product-list weights))
                       (rem x (product-list weights)))
                      x))
     :rule-classes nil)))

(local
 (defthm weighted-split-nat1--<=--consp
   (implies (and (2+-listp weights)
                 (consp weights)
                 (equal weights-factor (product-list weights))
                 (integerp x)
                 (<= 0 x))
            (all-<= (weighted-split-nat1 weights weights-factor x) x))
   :hints (("Goal" :in-theory (disable len 2+-listp product-list)
                   :do-not '(eliminate-destructors)
                   :induct t)
           ("Subgoal *1/2.1"
            :use ((:instance weighted-split-nat1--<=-induction-step1)
                  (:instance weighted-split-nat1--<=-induction-step2))))))

(local
 (defthm weighted-split-nat1--<=--endp
   (implies (not (consp weights))
            (all-<= (weighted-split-nat1 weights weights-factor x) x))))
 
(local
 (defthm weighted-split-nat1--<=
   (implies (and (2+-listp weights)
                 (equal weights-factor (product-list weights))
                 (integerp x)
                 (<= 0 x))
            (all-<= (weighted-split-nat1 weights weights-factor x) x))
   :hints (("Goal" :cases ((consp weights))))))

#|
(defun pos-list-fix (x)
  (if (atom x)
    nil
    (cons
     (if (posp (car x))
       (car x)
       1)
     (pos-list-fix (cdr x)))))
|#

(defthm pos-listp--pos-list-fix
  (pos-listp (pos-list-fix x))
  :rule-classes (:rewrite :type-prescription))

(defthm len--pos-list-fix
  (equal (len (pos-list-fix x))
         (len x)))

(defthm pos-list-fix--shortcut
  (implies (pos-listp x)
           (equal (pos-list-fix x)
                  x)))

(defun non-empty-pos-list-fix (x)
  (if (atom x)
    (list 1)
    (pos-list-fix x)))

(defthm len--non-empty-pos-list-fix
  (equal (len (non-empty-pos-list-fix x))
         (max 1 (len x))))

(defthm consp--non-empty-pos-list-fix
  (consp (non-empty-pos-list-fix x))
  :rule-classes (:rewrite :type-prescription))

(defthm pos-listp--non-empty-pos-list-fix
  (pos-listp (non-empty-pos-list-fix x))
  :rule-classes (:rewrite :type-prescription))

(defthm non-empty-pos-list-fix--shortcut
  (implies (and (pos-listp x)
                (consp x))
           (equal (non-empty-pos-list-fix x)
                  x)))

(in-theory (disable non-empty-pos-list-fix))

(defun weighted-split-nat (weights x)
  (declare (xargs :guard (and (pos-listp weights)
                              (consp weights)
                              (natp x))))
  (mbe :exec
       (let ((2+-weights (scale weights 2)))
         (weighted-split-nat1 2+-weights (product-list 2+-weights) x))
       :logic
       (let* ((weights (non-empty-pos-list-fix weights))
              (x (nfix x))
              (2+-weights (scale weights 2)))
         (weighted-split-nat1 2+-weights (product-list 2+-weights) x))))

; Pete 2019-08-20: not useless; needed in base.lisp
;(local ; weighted-split-nat will later be automatically rewritten, so these
;       ; become useless 
(defthm weighted-split-nat--len
  (equal (len (weighted-split-nat weights x))
         (max 1 (len weights)))) ;)

(local
 (defthm weighted-split-nat--consp
   (consp (weighted-split-nat weights x))))


 (defthm weighted-split-nat--nat-listp
   (nat-listp (weighted-split-nat weights x)))

(local (defthm scale--pos-listp--2+-listp
         (implies (pos-listp l)
                  (2+-listp (scale l 2)))
         :rule-classes (:forward-chaining :type-prescription)))

(local
 (defthm weighted-split-nat--bound
   (implies (and (integerp x)
                 (<= 0 x))
            (all-<= (weighted-split-nat weights x) x))))

(local
 (defthm car--nat-list--integer
   (implies (and (consp x)
                 (nat-listp x))
            (integerp (car x)))))

(local
 (defthm weighted-split-nat--car-integer
   (INTEGERP (CAR (WEIGHTED-SPLIT-NAT WEIGHTS X)))))

(local
 (defthm car--nat-list-->=0
   (implies (and (consp x)
                 (nat-listp x))
            (<= 0 (car x)))))

(local
 (defthm weighted-split-nat--car->=0
   (<= 0 (CAR (WEIGHTED-SPLIT-NAT WEIGHTS X)))))

(local
(defthm not-nat-implies-weighted-split-nat-is-zero
  (implies (and (not (natp x))
                (pos-listp ws)
                (>= (len ws) 1))
           (equal (weighted-split-nat ws x)
                  (make-list (len ws) :initial-element 0)))))


(in-theory (disable weighted-split-nat))




;(set-verify-guards-eagerness 0)
(defun nth-weighted-split-nat (i weights x)
  (declare (xargs :guard nil)) ; logic only
  ;(declare (xargs :verify-guards nil))
  (if (and (integerp i)
           (<= 0 i)
           (< i (len weights)))
    (nth i (weighted-split-nat weights x))
    (car (weighted-split-nat weights x))))

(defun nthcdr-weighted-split-nat (i weights x)
  (declare (xargs :guard nil)) ; logic only
  ;(declare (xargs :verify-guards nil))
  (nthcdr i (weighted-split-nat weights x)))



(defthm nth-weighted-split-nat--bound
  (implies (and (integerp x)
                (<= 0 x))
           (<= (nth-weighted-split-nat i weights x)
               x))
  ;:hints (("Goal" :cases ((all-<= (weighted-split-nat weights x) x))))
  :rule-classes (:rewrite :linear))

(defthm nat-listp--nth--integerp
         (implies (and (nat-listp l)
                       (integerp i)
                       (<= 0 i)
                       (< i (len l)))
                  (integerp (nth i l)))
         :rule-classes (:rewrite :type-prescription))

(defthm nth-weighted-split-nat--integerp
  (integerp (nth-weighted-split-nat i weights x))
  :rule-classes (:rewrite :type-prescription))

(defthm nat-listp--nth-->=0
         (implies (and (nat-listp l)
                       (integerp i)
                       (<= 0 i)
                       (< i (len l)))
                  (<= 0 (nth i l)))
         :rule-classes (:rewrite :linear))

(defthm nth-weighted-split-nat-->=0
  (<= 0 (nth-weighted-split-nat i weights x))
  :rule-classes (:rewrite :linear))


(local
 (defthm nth--nthcdr--decomp
   (implies (consp l)
            (equal (cons (nth 0 l)
                         (nthcdr 1 l))
                   l))))

(local
 (defthm len--nthcdr--toobig
   (implies (and (integerp i)
                 (<= (len l) i))
            (equal (len (nthcdr i l))
                   0))))

(local
 (defthm len--nthcdr
   (implies (and (integerp i)
                 (<= 0 i)
                 (<= i (len l)))
            (equal (len (nthcdr i l))
                   (- (len l) i)))))

(defthm nthcdr-weighted-split-nat--len
  (equal (len (nthcdr-weighted-split-nat i weights x))
         (if (zp i)
           (max 1 (len weights))
           (if (<= i (len weights))
             (- (len weights) i)
             0))))

(local
 (defthm consp--nthcdr
   (equal (consp (nthcdr i l))
          (and (consp l)
               (implies (integerp i)
                        (< i (len l)))))))

(defthm nthcdr-weighted-split-nat--consp
           (equal (consp (nthcdr-weighted-split-nat i weights x))
                  (implies (integerp i)
                           (< i (max 1 (len weights))))))

(local
 (defthm nat-listp--nthcdr
   (implies (nat-listp l)
            (nat-listp (nthcdr i l)))
   :hints ; Added by Matt K. to defeat new rule post-Version 6.5, as indicated:
   (("Goal"
     :in-theory (disable (:t acl2::true-listp-nthcdr-type-prescription))))
   :rule-classes (:rewrite :type-prescription)))

(defthm nthcdr-weighted-split-nat--nat-listp
  (nat-listp (nthcdr-weighted-split-nat i weights x)))


(defthm weighted-split-nat--to--nthcdr-weighted-split-nat
  (implies (and (pos-listp weights)
                (consp weights)
                (integerp x)
                (<= 0 x))
           (equal (weighted-split-nat weights x)
                  (nthcdr-weighted-split-nat 0 weights x))))



(local
 (encapsulate nil
   (local (include-book "arithmetic-5/top" :dir :system))

   (local
    (defthm nthcdr--cdr
      (implies (and (integerp i)
                    (<= 0 i))
               (equal (nthcdr i (cdr l))
                      (nthcdr (+ 1 i) l)))
      :hints (("Goal" :expand (nthcdr (+ 1 i) l)))))

   (defthm nth--nthcdr--decomp2
     (implies (and (integerp i)
                   (<= 0 i)
                   (< i (len l)))
              (equal (cons (nth i l)
                           (nthcdr (+ 1 i) l))
                     (nthcdr i l))))))

(defthm nthcdr-weighted-split-nat--deflike
  (implies (and (integerp i)
                (<= 0 i)
                (< i (len weights)))
           (equal (nthcdr-weighted-split-nat i weights x)
                  (cons (nth-weighted-split-nat i weights x)
                        (nthcdr-weighted-split-nat (+ 1 i) weights x))))
  :hints (("Goal" :in-theory (disable nth nthcdr)))
  :rule-classes ((:definition :controller-alist ((nthcdr-weighted-split-nat t nil nil)))))

(in-theory (disable nth-weighted-split-nat nthcdr-weighted-split-nat)) 

(defthm nthcdr-weighted-split-nat--car
  (implies (and (integerp i)
                (<= 0 i)
                (< i (len weights)))
           (equal (car (nthcdr-weighted-split-nat i weights x))
                  (nth-weighted-split-nat i weights x)))
  :hints (("Goal" :expand (nthcdr-weighted-split-nat i weights x))))

(defthm nthcdr-weighted-split-nat--cdr
  (implies (and (integerp i)
                (<= 0 i)
                (< i (len weights)))
           (equal (cdr (nthcdr-weighted-split-nat i weights x))
                  (nthcdr-weighted-split-nat (+ 1 i) weights x)))
  :hints (("Goal" :expand (nthcdr-weighted-split-nat i weights x))))

(local
 (defthm len-exceeding-return-nil
   (implies (and (natp i)
                 (<= (len l) i))
            (equal (nth i l) nil))))
(local 
 (defthm make-list-logic-len
   (implies (natp i)
            (equal (len (make-list-logic a i))
                   i))))

(defun nth-returns-elem-of-make-list-ind-scheme (i x)
  (declare (xargs :guard (and (natp i) (natp x))))
  (if (or (zp i) (zp x))
    0
    (nth-returns-elem-of-make-list-ind-scheme (- i 1) (- x 1))))

(local
 (defthm nth-returns-elem-of-make-list
   (implies (and (natp i)
                 (natp x)
                 (< i x))
            (equal (nth i (make-list-logic a x)) a))
 :hints (("Goal" :induct 
                 (nth-returns-elem-of-make-list-ind-scheme i x)))))
#|
;Above lemmas should help prove this
(defthm nth-i-split-nat-<=
  (implies (and (pos-listp ws)
                (>= (len ws) 1))
       (<= (nth i (weighted-split-nat ws x)) (nfix x)))
  :hints (("Goal" :cases ((< i (len ws)))))
 :rule-classes (:rewrite :linear))
|#

;ADDED some hack defthms to help termination of recursive records with
;more than 3 fields.
(defthm nth-i-split-nat-3-<=
 ;(implies (and (integerp x)
 ;              (<= 0 x))
          (<= (nth i (weighted-split-nat '(1 1 1) (nfix x))) (nfix x))
 :rule-classes (:rewrite :linear))

(defthm nth-i-split-nat-4-<=
 ;(implies (and (integerp x)
 ;              (<= 0 x))
          (<= (nth i (weighted-split-nat '(1 1 1 1) (nfix x))) (nfix x))
 :rule-classes (:rewrite :linear))

(defthm nth-i-split-nat-5-<=
 ;(implies (and (integerp x)
 ;              (<= 0 x))
          (<= (nth i (weighted-split-nat '(1 1 1 1 1) (nfix x))) (nfix x))
 :rule-classes (:rewrite :linear))

(defthm nth-i-split-nat-6-<=
 ;(implies (and (integerp x)
 ;              (<= 0 x))
          (<= (nth i (weighted-split-nat '(1 1 1 1 1 1) (nfix x))) (nfix x))
 :rule-classes (:rewrite :linear))

; testing theorems

#|
(thm
 (implies (natp x)
          (natp (cadr (weighted-split-nat '(3 2 4) x)))))
(thm
 (implies (and (natp n) (natp x))
          (<= (nth i (weighted-split-nat '(1 1 1) x)) x)))
;|#

; testing

#|
(defun weighted-split-nat-downfrom (weights n)
  (declare (xargs :guard (and (pos-listp weights)
                              (consp weights)
                              (natp n))))
  (if (zp n)
    (list (list 0 '-> (weighted-split-nat weights 0)))
    (cons (list n '-> (weighted-split-nat weights n))
          (weighted-split-nat-downfrom weights (- n 1)))))

(defun weighted-split-nat-upto (weights n)
  (declare (xargs :guard (and (pos-listp weights)
                              (consp weights)
                              (natp n))))
  (reverse (weighted-split-nat-downfrom weights n)))

;(trace$ weighted-split-nat-step-tail)
(weighted-split-nat-upto '(1 1) 33)

;|#


; alternative interface

(defthm pos-listp--list-expt--2
  (implies (nat-listp l)
           (pos-listp (list-expt 2 l)))
  :rule-classes (:rewrite :type-prescription))

(defun pow-weighted-split-nat (pow-weights x)
  (declare (xargs :guard (and (pos-listp pow-weights)
                              (consp pow-weights)
                              (natp x))))
  (let ((2**weights (list-expt 2 pow-weights)))
    (weighted-split-nat1 2**weights (product-list 2**weights) x)))

(defun split-nat (nways x)
  (declare (xargs :guard (and (posp nways)
                              (natp x))))
  (weighted-split-nat (make-list nways :initial-element 1) x))

(defthm split-nat--nat-listp
  (nat-listp (split-nat nways x))
   :rule-classes :type-prescription)


(defthm nat-listp--true-listp
  (implies (nat-listp x)
           (true-listp x))
   :rule-classes (:rewrite :forward-chaining))#|ACL2s-ToDo-Line|#



