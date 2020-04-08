; Copyright (C) 2020, Rob Sumners
; Written by Rob Sumners
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

;; include std libraries and fty libraries:
(include-book "std/top" :dir :system)
(include-book "centaur/fty/top" :dir :system)
;; include gl shape specs:
(include-book "centaur/gl/shape-spec" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; bakery specification defintion
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro make-signed-byte-type (name size)
  (declare (xargs :guard (and (symbolp name) (posp size))))
  (b* ((pred (intern-in-package-of-symbol
              (str::cat (symbol-name name) "-P")
              name))
       (fix  (intern-in-package-of-symbol
              (str::cat (symbol-name name) "-FIX")
              name))
       (equiv (intern-in-package-of-symbol
              (str::cat (symbol-name name) "-EQUIV")
              name))
       (nfix  (intern-in-package-of-symbol
               (str::cat (symbol-name name) "-OF-NFIX")
               name))
       (pos-fix (intern-in-package-of-symbol
                 (str::cat (symbol-name name) "-OF-POS-FIX")
                 name))
       (eqlp  (intern-in-package-of-symbol
               (str::cat (symbol-name name) "-IS-EQLABLEP")
               name))
       (ratp  (intern-in-package-of-symbol
               (str::cat (symbol-name name) "-IS-RATIONALP")
               name))
       (intp  (intern-in-package-of-symbol
               (str::cat (symbol-name name) "-IS-INTEGERP")
               name)))
    `(progn (define ,pred (x)
              (signed-byte-p ,size x))
            (define ,fix (x)
              :enabled t
              (if (,pred x) x 0))
            (fty::deffixtype ,name
              :pred   ,pred
              :fix    ,fix
              :equiv  ,equiv
              :define t)
            (defthm ,nfix
              (implies (,pred n) (,pred (nfix n)))
              :hints (("Goal" :in-theory (enable ,pred))))
            (defthm ,pos-fix
              (implies (,pred n) (,pred (pos-fix n)))
              :hints (("Goal" :in-theory (enable ,pred pos-fix))))
            (defthm ,eqlp
              (implies (,pred n) (eqlablep n))
              :hints (("Goal" :in-theory (enable ,pred))))
            (defthm ,ratp
              (implies (,pred n) (rationalp n))
              :hints (("Goal" :in-theory (enable ,pred))))
            (defthm ,intp
              (implies (,pred n) (integerp n))
              :hints (("Goal" :in-theory (enable ,pred)))))))

(make-signed-byte-type bake-loc 6)
(make-signed-byte-type bake-ndx 4)
(make-signed-byte-type bake-ctr 6)
(make-signed-byte-type bake-runs 10)
  
(fty::defprod bake-tr
  ((loc        bake-loc-p)
   (ndx        bake-ndx-p)
   (loop       bake-ndx-p)
   (pos        bake-ctr-p)
   (old-pos    bake-ctr-p)
   (temp       bake-ctr-p)
   (runs       bake-runs-p)
   (done       booleanp)
   (choosing   booleanp)
   (pos-valid  booleanp)))

(fty::defprod bake-sh
  ((max        bake-ctr-p)))

(fty::deflist bake-tr-lst
  :elt-type bake-tr
  :true-listp t)

(fty::defprod bake-st
  ((sh  bake-sh-p)
   (trs bake-tr-lst-p)))

;;;; bakery model definition:

;; some constants:

(define max-ctr ()
  :returns (r bake-ctr-p)
  16)

(define max-ndx ()
  :returns (r bake-ndx-p)
  6)

(define loop-start ()
  :returns (r bake-ndx-p)
  (1- (max-ndx)))

;; init states:

(define bake-tr-init ((n bake-ndx-p) (r bake-runs-p))
  :returns (x bake-tr-p :hyp :guard)
  (make-bake-tr
   :loc 0
   :ndx (nfix n)
   :loop 0
   :pos 1
   :old-pos 0
   :temp 0
   :runs (pos-fix r)
   :done nil
   :choosing nil
   :pos-valid nil))

(define bake-sh-init ()
  :returns (r bake-sh-p)
  (make-bake-sh
   :max 1))

(define bake-tr-done ((a bake-tr-p))
  (bake-tr->done a))

;; next states:

; some supporting definitions:
(define ctr-1+ ((a bake-ctr-p))
  :returns (r bake-ctr-p :hyp :guard
              :hints (("Goal" :in-theory (enable bake-ctr-p))))
  (if (< a (max-ctr)) (1+ a) 0))

(define ctr-> ((a bake-ctr-p) (b bake-ctr-p))
  (or (> a b) (and (= a 0) (= b (max-ctr)))))

(define ndx=0 ((a bake-ndx-p))
  (<= a 0))

(define ndx-1 ((a bake-ndx-p))
  :returns (r bake-ndx-p :hyp :guard
              :hints (("Goal" :in-theory (enable bake-ndx-p))))
  (if (> a 0) (1- a) a))

(define runs=0 ((a bake-runs-p))
  (<= a 0))

(define runs-1 ((a bake-runs-p))
  :returns (r bake-runs-p :hyp :guard
              :hints (("Goal" :in-theory (enable bake-runs-p))))
  (if (> a 0) (1- a) a))

(defmacro tr+ (&rest x) `(change-bake-tr ,@x))
(defmacro sh+ (&rest x) `(change-bake-sh ,@x))

; next state functions for bake-tr and bake-sh
(define bake-tr-next ((a bake-tr-p) (sh bake-sh-p))
  :returns (r bake-tr-p :hyp :guard)
  (b* (((bake-tr a) a) ((bake-sh sh) sh))
    (case a.loc
      (0  (tr+ a :loc 1 :choosing t))
      (1  (tr+ a :loc 2 :temp sh.max))
      (2  (tr+ a :loc 3 :pos (ctr-1+ a.temp)
                        :loop (loop-start)))
      (3  (tr+ a :loc 4)) ;; possibly blocked here
      (4  (tr+ a :loc 5 :loop (ndx-1 a.loop)))
      (5  (tr+ a :loc (if (ndx=0 a.loop) 6 3)
                 :pos-valid (ndx=0 a.loop)))
      (6  (tr+ a :loc 7))
      (7  (tr+ a :loc 8 :choosing nil
                        :loop (loop-start)))
      (8  (tr+ a :loc 9))  ;; possibly blocked here
      (9  (tr+ a :loc 10)) ;; possibly blocked here
      (10 (tr+ a :loc 11)) ;; possibly blocked here
      (11 (tr+ a :loc 12 :loop (ndx-1 a.loop)))
      (12 (tr+ a :loc (if (ndx=0 a.loop) 13 8)))
      (13 (tr+ a :loc 14 :pos-valid nil))
      (14 (tr+ a :loc 15 :runs (runs-1 a.runs)))
      (15 (tr+ a :loc (if (runs=0 a.runs) 16 0)))
      (t  (tr+ a :loc 17 :done t)))))

(define bake-sh-next ((sh bake-sh-p) (a bake-tr-p))
  :returns (r bake-sh-p :hyp :guard)
  (b* (((bake-tr a) a) ((bake-sh sh) sh))
    (case a.loc
      (6 (if (not (ctr-> sh.max a.temp))
             (sh+ sh :max a.pos)
           sh))
      (t sh))))

;; blocking relation:

(define bake-tr-blok ((a bake-tr-p) (b bake-tr-p))
  (b* (((bake-tr a) a) ((bake-tr b) b))
    (and (eql a.loop b.ndx)
         (case a.loc
           (3  (and (eql a.pos 0) b.pos-valid))
           (8  (and (not (eql b.pos 0)) b.choosing))
           (9  (and b.pos-valid (< b.pos a.pos)))
           (10 (and b.pos-valid (eql b.pos a.pos)
                    (< b.ndx a.ndx)))))))

;; bake-type shapes and constants:

; NOTE -- this is a bit of a hack, we use the the FTY types to embed values
;         which are then turned into appropriate symbolic types at the locations
;         that matter.. it would be better to do this in a more principled manner..
;         or extend FTY with support for it.. but alas.. this is the hack we have
;         here and now..

(define bake-tr-shp-descr ()
  :returns (r bake-tr-p)
  (make-bake-tr
   :loc 6
   :ndx 4
   :loop 4
   :pos 6
   :old-pos 6
   :temp 6
   :runs 10
   :done t
   :choosing t
   :pos-valid t))

(define bake-sh-shp-descr ()
  :returns (r bake-sh-p)
  (make-bake-sh
   :max 6))

(define bake-ndx-shp-descr ()
  :returns (r posp)
  4)

(define bake-runs-shp-descr ()
  :returns (r posp)
  10)

(define mk-nats ((n natp) (s natp))
  (if (zp s) () (cons n (mk-nats (1+ n) (1- s))))) 

(define mk-bake-shp (p (n natp))
  :verify-guards nil
  :returns (mv (x natp :hyp (natp n)) r)
  (cond
   ((posp p)
    (mv (+ n p)
        (cons :g-integer (mk-nats n p))))
   ((eq p t)
    (mv (1+ n)
        (cons :g-boolean n)))
   ((atom p) (mv n p))
   (t (mv-let (n1 x) (mk-bake-shp (car p) n)
        (mv-let (n2 y) (mk-bake-shp (cdr p) n1)
          (mv n2 (cons x y)))))))

(verify-guards mk-bake-shp)

(define make-all-tr-sh-shapes ()
  (b* ((n 2)
       ((mv n a-shp)   (mk-bake-shp (bake-tr-shp-descr)   n))
       ((mv n b-shp)   (mk-bake-shp (bake-tr-shp-descr)   n))
       ((mv n sh-shp)  (mk-bake-shp (bake-sh-shp-descr)   n))
       ((mv n n-shp)   (mk-bake-shp (bake-ndx-shp-descr)  n))
       ((mv n m-shp)   (mk-bake-shp (bake-ndx-shp-descr)  n))
       ((mv n r-shp)   (mk-bake-shp (bake-runs-shp-descr) n))
       ((mv - c-shp)   (mk-bake-shp (bake-tr-shp-descr)   n)))
    (mv a-shp b-shp sh-shp n-shp m-shp r-shp c-shp)))

(std::defconsts (*a-shp* *b-shp* *sh-shp* *n-shp* *m-shp* *r-shp* *c-shp*)
                (make-all-tr-sh-shapes))

(define a-shp ()  :returns (r gl::shape-specp) *a-shp*)
(define b-shp ()  :returns (r gl::shape-specp) *b-shp*)
(define c-shp ()  :returns (r gl::shape-specp) *c-shp*)
(define n-shp ()  :returns (r gl::shape-specp) *n-shp*)
(define m-shp ()  :returns (r gl::shape-specp) *m-shp*)
(define r-shp ()  :returns (r gl::shape-specp) *r-shp*)
(define sh-shp () :returns (r gl::shape-specp) *sh-shp*)

;; correlation betweeen types and shapes..
;;   these are actually provable both ways, but we only need this direction:

(defthm bake-tr-implies-shape-spec-obj-in-range-a
  (implies (bake-tr-p a)
           (gl::shape-spec-obj-in-range (a-shp) a))
  :hints (("Goal" :in-theory (enable a-shp bake-tr-p gl::shape-spec-obj-in-range
                                     bake-loc-p bake-ndx-p bake-ctr-p bake-runs-p))))

(defthm bake-tr-implies-shape-spec-obj-in-range-b
  (implies (bake-tr-p b)
           (gl::shape-spec-obj-in-range (b-shp) b))
  :hints (("Goal" :in-theory (enable b-shp bake-tr-p gl::shape-spec-obj-in-range
                                     bake-loc-p bake-ndx-p bake-ctr-p bake-runs-p))))

(defthm bake-tr-implies-shape-spec-obj-in-range-c
  (implies (bake-tr-p c)
           (gl::shape-spec-obj-in-range (c-shp) c))
  :hints (("Goal" :in-theory (enable c-shp bake-tr-p gl::shape-spec-obj-in-range
                                     bake-loc-p bake-ndx-p bake-ctr-p bake-runs-p))))

(defthm bake-sh-implies-shape-spec-obj-in-range-sh
  (implies (bake-sh-p sh)
           (gl::shape-spec-obj-in-range (sh-shp) sh))
  :hints (("Goal" :in-theory (enable sh-shp bake-sh-p gl::shape-spec-obj-in-range
                                     bake-loc-p bake-ndx-p bake-ctr-p bake-runs-p))))

