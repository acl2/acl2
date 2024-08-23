;; Copyright (C) 2024 Carl Kwan
;;
;; Defining matrix multiplication via the outer product
;; Summary:
;;      The events in this file defines matrix multiplication via the outer
;;      product and proves its equivalence to matrix multiplication defined
;;      via row multiplication. The main definitions in this file are:
;;
;;      - row-out-*, which defines the outer product between vectors row-wise
;;      - col-out-*, which defines the outer product between vectors column-wise
;;      - out-*, which defines the outer product via col-out-*
;;      - m*-by-out-*, which defines matrix multiplication via out-*
;;
;;      The main theorems in this file are:
;;
;;      - col-out-*-row-out-*, which states the equivalence between row- /
;;        column-wise outer products
;;      - m*-m*-by-out-*, which states m*-by-out-* is equivalent to m* under m*-guard
;;
;; Requires:
(in-package "ACL2")
(include-book "std/util/define" :dir :system)
(include-book "workshops/2003/hendrix/support/mtrans" :dir :system)

;; Define the outer product row-wise:
;; u x v = [ u_1 v ]
;;         [ u_2 v ]
;;         [ ...   ]
;;         [ u_n v ]
;; and prove basic properties:
;;   cu x v = c (u x v)
;;   u x cv = c (u x v)
;;   ( u + v ) x w = u x w + v x w
;;   u x ( v + w ) = u x v + u x w
(define row-out-* (u v)
 :verify-guards nil
 :returns out
 :guard (and (mvectorp u) (mvectorp v))
 (if (or (endp u) (endp v))
     (m-empty)
     (row-cons (sv* (car u) v)
               (row-out-* (cdr u) v)))
 ///
 (more-returns
  (out (= (row-count out) (if (consp v) (len u) 0))
       :name row-count-of-row-out-*)
  (out (= (col-count out) (if (consp u) (len v) 0))
       :name col-count-of-row-out-*)
  (out (implies (or (endp u) (endp v)) (m-emptyp out))
       :name m-emptyp-row-out-*)
  (out (matrixp out)
       :rule-classes (:rewrite :type-prescription)
       :hints (("Subgoal *1/2" :use ((:instance matrixp-row-cons
                                                (l (sv* (car u) v))
                                                (m (row-out-* (cdr u) v))))))))
 (verify-guards row-out-*)

 (defthm linearity-sv*-row-out-*
  (equal (row-out-* (sv* c u) v)
         (sm* c (row-out-* u v))))

 (defthm linearity-row-out-*-sv*
  (equal (row-out-* u (sv* c v))
         (sm* c (row-out-* u v))))

 (local
  (defthm lemma-1
   (implies (matrixp m) (equal (m+ m nil) m))))

 (local
  (defthm lemma-2
   (implies (and (mvectorp u) (not (consp v))) (equal (v+ u v) u))))

 (defthm distributivity-v+-row-out-*
  (implies (mvectorp u)
           (equal (row-out-* (v+ u v) w)
                  (m+ (row-out-* u w) (row-out-* v w)))))

 (defthm distributivity-row-out-*-v+
  (implies (mvectorp v)
           (equal (row-out-* u (v+ v w))
                  (m+ (row-out-* u v) (row-out-* u w))))))

;; Define the outer product column-wise:
;; u x v = [ u v_1 | u v_2 | ... | u v_n ]
(define col-out-* (u v)
 :verify-guards nil
 :returns out
 :guard (and (mvectorp u) (mvectorp v))
 (if (or (endp u) (endp v))
     (m-empty)
     (col-cons (sv* (car v) u)
               (col-out-* u (cdr v))))
 ///
 (more-returns
  (out (= (row-count out) (if (consp v) (len u) 0))
       :name row-count-of-col-out-*)
  (out (= (col-count out) (if (consp u) (len v) 0))
       :hints (("Goal" :in-theory (enable col-count col-cons)))
       :name col-count-of-col-out-*)
  (out (implies (or (endp u) (endp v)) (m-emptyp out))
       :name m-emptyp-col-out-*)
  (out (matrixp out)
       :rule-classes (:rewrite :type-prescription)
       :hints (("Subgoal *1/2" :use ((:instance matrixp-col-cons
                                                (l (sv* (car v) u))
                                                (m (col-out-* u (cdr v)))))))))
 (verify-guards col-out-*)

 (defthm mtrans-row-out-*-col-out-*
  (equal (mtrans (row-out-* u v)) (col-out-* v u))
  :hints (("Goal" :in-theory (enable mtrans row-out-*)))))

;; Show that
;; u x v = [ u_1 v ] = [ u v_1 | u v_2 | ... | u v_n ]
;;         [ u_2 v ]
;;         [ ...   ]
;;         [ u_n v ]

(defthmd col-out-*-row-out-*
 (equal (col-out-* u v) (row-out-* u v))
 :hints (("Goal" :in-theory (enable col-out-* row-out-* col-cons row-cons))))

(define out-* (u v)
 :guard (and (mvectorp u) (mvectorp v))
 :returns out
 (col-out-* u v)
 ///
 (more-returns
  (out (= (row-count out) (if (consp v) (len u) 0))
       :name row-count-out-*)
  (out (= (col-count out) (if (consp u) (len v) 0))
       :name col-count-out-*)
  (out (implies (or (endp u) (endp v)) (m-emptyp out))
       :name m-emptyp-out-*)
  (out (matrixp out)
       :rule-classes (:rewrite :type-prescription)))

 (defthm out-*-col-def
  (equal (out-* u v)
         (if (or (endp u) (endp v))
             (m-empty)
             (col-cons (sv* (car v) u)
                       (col-out-* u (cdr v)))))
  :hints (("Goal" :in-theory (enable col-out-*)))
  :rule-classes ((:definition)))

 ;; "Entry" theorems shouldn't be necessary but mentioned here for completeness
 ;(defthmd nth-col-of-out-*
 ; (implies (and (mvectorp u) (mvectorp v))
 ;          (equal (col n (out-* u v))
 ;                 (sv* (nth n v) u))))

 (local (in-theory (enable col-out-*-row-out-*)))

 (defthm mtrans-out-*
  (equal (mtrans (out-* u v)) (out-* v u)))

 (defthmd linearity-sv*-out-*
  (equal (out-* (sv* c u) v)
         (sm* c (out-* u v))))

 (defthmd linearity-out-*-sv*
  (equal (out-* u (sv* c v))
         (sm* c (out-* u v))))

 (defthmd distributivity-v+-out-*
  (implies (mvectorp u)
           (equal (out-* (v+ u v) w)
                  (m+ (out-* u w) (out-* v w)))))

 (defthmd distributivity-out-*-v+
  (implies (mvectorp v)
           (equal (out-* u (v+ v w))
                  (m+ (out-* u v) (out-* u w)))))

;; Row definition of out-* (can change to col definition if necessary)
(defthm out-*-row-def
  (equal (out-* u v)
         (if (or (endp u) (endp v))
             (m-empty)
             (row-cons (sv* (car u) v)
                       (out-* (cdr u) v))))
  :hints (("Goal" :in-theory (enable col-out-* row-out-*)))
  :rule-classes ((:definition))))

;; Disable many theorems to avoid rewriting in the wrong direction
;; In principle, we only need m*-m*-by-out-* at the end
(in-theory (disable out-*-col-def

                    row-out-*
                    col-out-*

                    row-count-of-row-out-*
                    col-count-of-row-out-*
                    m-emptyp-row-out-*
                    matrixp-of-row-out-*

                    linearity-sv*-row-out-*
                    linearity-row-out-*-sv*
                    distributivity-v+-row-out-*
                    distributivity-row-out-*-v+

                    row-count-of-col-out-*
                    col-count-of-col-out-*
                    m-emptyp-col-out-*
                    matrixp-of-col-out-*

                    mtrans-row-out-*-col-out-* ))

(define m*-by-out-* (m n)
 :guard (m*-guard m n)
 :returns prod
 :verify-guards nil
 (if (or (m-emptyp m) (m-emptyp n))
     (m-empty)
     ;; 1 x 1 case required to verify guards for m+
     (if (or (m-emptyp (col-cdr m)) (m-emptyp (row-cdr n)))
         (out-* (col-car m) (row-car n))
         (m+ (out-* (col-car m) (row-car n))
             (m*-by-out-* (col-cdr m) (row-cdr n)))))
 ///
 ;; Lemma for proving dimension properties of matrix multiplication via outer products
 (local
  (defthm lemma-1
   (and (equal (row-count (m*-by-out-* m n))
               (row-count (out-* (col-car m) (row-car n))))
        (equal (col-count (m*-by-out-* m n))
               (col-count (out-* (col-car m) (row-car n)))))
   :hints (("Goal" :in-theory (e/d (m-emptyp row-car col-car) ())))))

 ;; Basic "type" theorems
 (more-returns
  (prod (implies (matrixp m)
                 (equal (row-count prod)
                        (if (consp (row-car n)) (row-count m) 0)))
        :hints (("Goal" :use ((:instance row-count-out-*
                                         (u (col-car m))
                                         (v (row-car n))))))
        :name row-count-m*-by-out-*)

  (prod (implies (and (matrixp m) (matrixp n))
                 (equal (row-count prod)
                        (if (m-emptyp n) 0 (row-count m))))
        :name row-count-m*-by-out-*-when-matrixp)

  (prod (implies (matrixp n)
                 (equal (col-count prod)
                        (if (consp (col-car m)) (col-count n) 0)))
        :name col-count-m*-by-out-*)

  (prod (implies (and (matrixp m) (matrixp n))
                 (equal (col-count prod)
                        (if (m-emptyp m) 0 (col-count n))))
        :name col-count-m*-by-out-*-when-matrixp)

  (prod (matrixp prod)
        :hints (("Goal" :in-theory (disable m+ out-*-row-def) ))
        :rule-classes (:rewrite :type-prescription))

  (prod (implies (or (not (consp (row-car n)))
                     (not (consp (col-car m))))
                 (equal prod (m-empty)))
        :name m-empty-m*-by-out-*))

 (verify-guards m*-by-out-*)

; (defthmd row-car-m*-by-out-*
;  (implies (and (m*-guard m n)
;                (not (m-emptyp (row-cdr m))))
;           (equal (row-car (m*-by-out-* m n))
;                  (col* (row-car m) n)))
;  :hints (("Goal" :in-theory (disable m+-comm))))
;
; (defthmd row-cdr-m*-by-out-*
;  (implies (and (m*-guard m n)
;                (not (m-emptyp (row-cdr m))))
;           (equal (row-cdr (m*-by-out-* m n))
;                  (m*-by-out-* (row-cdr m) n))))

 (defthmd m*-by-out-*-row-def
   (implies (and (matrixp m)
       	         (matrixp n)
       	         (or (equal (col-count m) (row-count n))
       	             (m-emptyp m)
       	             (m-emptyp n)))
            (equal (m*-by-out-* m n)
       	           (if (or (m-emptyp m) (m-emptyp n))
       	               (m-empty)
       	       	       (if (m-emptyp (row-cdr m))
       	       	           (row-cons (col* (row-car m) n) nil)
       	       	           (row-cons (col* (row-car m) n)
       	       	                     (m*-by-out-* (row-cdr m) n))))))
   :rule-classes :definition)

  (defthmd m*-m*-by-out-*
    (implies (m*-guard m n)
             (equal (m* m n)
                    (m*-by-out-* m n)))
    :hints (("Goal" :in-theory (enable m*-by-out-*-row-def)))))
