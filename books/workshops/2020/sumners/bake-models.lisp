; Copyright (C) 2020, Rob Sumners
; Written by Rob Sumners
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "bakery")
(include-book "gen-models")
(local (include-book "gl-setup"))

;; now we setup memory and satlink settings for GL through a macro

(local (gl::init-gl-params))

;; attach our gl var->shape function:

(define bake-get-var-shp (v)
  :returns (r gl::shape-specp)
  (cond ((eq v 'a)   (a-shp))
        ((eq v 'b)   (b-shp))
        ((eq v 'c)   (c-shp))
        ((eq v 'sh)  (sh-shp))
        ((eq v 'n)   (n-shp))
        ((eq v 'm)   (m-shp))
        ((eq v 'r)   (r-shp))
        (t (prog2$ (raise "did not find shape for variable:~x0" v)
                   (a-shp)))))

(defattach get-var-shp bake-get-var-shp)

(define nat->ord-tag ((src natp) (dst natp))
  :returns (r natp)
  (cond ((> src dst) 1)
        ((= src dst) 2)
        (t 3)))

(define make-ordr-trms (ords fn a b)
  (if (atom ords) ()
    (b* ((ord (first ords))
         (qord `(quote ,ord)))
      (cons (cons ord
                  `(nat->ord-tag (,fn ,a ,qord) 
                                 (,fn ,b ,qord)))
            (make-ordr-trms (rest ords) fn a b)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; First map and ord are for proving the rank terminates..
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bake-rank-map ((a bake-tr-p))
  (b* (((bake-tr a) a))
    `((:loc    ,a.loc)
      (:done   ,a.done)
      (:loop=0 ,(equal a.loop 0))
      (:runs=0 ,(equal a.runs 0))
      (:inv    ,(and (>= a.loop 0)
                     (>= a.runs 0))))))

(defconst *bake-rank-ords* '(loop runs))

(define bake-rank-ord ((a bake-tr-p) (o ord-p))
  :returns (r natp)
  (b* (((bake-tr a) a))
    (cond ((eq o 'runs) (nfix a.runs))
          ((eq o 'loop) (nfix a.loop))
          (t 0))))

;;;;

(defconsts (*bake-rank-reach* state)
  (comp-map-reach :init-hyp `t
                  :init-trm `(bake-rank-map (bake-tr-init n r))
                  :step-hyp `(and (equal (bake-rank-map a) ,*src-var*)
                                  (not (bake-tr-done a)))
                  :step-trm `(bake-rank-map (bake-tr-next a sh))))

(defconsts (*bake-rank-ord-graph* state)
  (comp-map-order :reach    *bake-rank-reach*
                  :ordr-hyp `(and (equal (bake-rank-map a) ,*src-var*)
                                  (equal (bake-rank-map b) ,*dst-var*)
                                  (equal (bake-tr-next a sh) b))
                  :ordr-trms (make-ordr-trms *bake-rank-ords* 
                                             'bake-rank-ord 'a 'b)))

(define chk-bake-rank-ord-arc ((src node-p) (dst node-p) (ord ord-p))
  :returns (r ord-tag-p)
  (check-arc-ord-tagging src dst ord *bake-rank-ord-graph*))

(defattach check-ord-arc chk-bake-rank-ord-arc)

(defconsts (*bake-rank-word*) 
  (mk-well-order *bake-rank-reach* *bake-rank-ords*))

(defthm bake-rakn-word-passed
  (w-ord-rslt->passed *bake-rank-word*)
  :rule-classes nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Second map and ord are for proving the nlock terminates..
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bake-nlock-map ((a bake-tr-p) (sh bake-sh-p))
  (b* (((bake-tr a) a)
       ((bake-sh sh) sh))     
    `((:loc       ,a.loc)
      (:pos-valid ,a.pos-valid)
      (:choosing  ,a.choosing)
      (:done      ,a.done)
      (:pos=0     ,(eql a.pos 0))
      (:inv       ,(and (>= a.temp 0)
                        (>= sh.max 0)
                        (>= a.pos 0)
                        (>= a.ndx 0))))))

(defconst *bake-nlock-ords* '(pos ndx))

(define bake-nlock-ord ((a bake-tr-p) (o ord-p))
  :returns (r natp)
  (b* (((bake-tr a) a))
    (cond ((eq o 'pos) (nfix a.pos))
          ((eq o 'ndx) (nfix a.ndx))
          (t 0))))

;;;;

(defconsts (*bake-nlock-reach* state)
  (comp-map-reach :init-hyp `t
                  :init-trm `(bake-nlock-map (bake-tr-init n r)
                                             (bake-sh-init))
                  :step-hyp `(and (equal (bake-nlock-map a sh) ,*src-var*)
                                  (not (bake-tr-done a)))
                  :step-trm `(bake-nlock-map (bake-tr-next a sh)
                                             (bake-sh-next sh a))))

(defconsts (*bake-nlock-blok* state)
  (comp-map-blok :reach *bake-nlock-reach*
                 :blok-hyp `(and (equal (bake-nlock-map a sh) ,*src-var*)
                                 (equal (bake-nlock-map b sh) ,*dst-var*)
                                 (bake-tr-blok a b))
                 :blok-trm `(bake-nlock-map b sh)))

(defconsts (*bake-nlock-ord-graph* state)
  (comp-map-order :reach    *bake-nlock-blok*
                  :ordr-hyp `(and (equal (bake-nlock-map a sh) ,*src-var*)
                                  (equal (bake-nlock-map b sh) ,*dst-var*)
                                  (bake-tr-blok a b))
                  :ordr-trms (make-ordr-trms *bake-nlock-ords* 
                                             'bake-nlock-ord 'a 'b)))

(define chk-bake-nlock-ord-arc ((src node-p) (dst node-p) (ord ord-p))
  :returns (r ord-tag-p)
  (check-arc-ord-tagging src dst ord *bake-nlock-ord-graph*))

(defattach check-ord-arc chk-bake-nlock-ord-arc)

(defconsts (*bake-nlock-word*) 
  (mk-well-order *bake-nlock-blok* *bake-nlock-ords*))

(defthm bake-nlock-word-passed
  (w-ord-rslt->passed *bake-nlock-word*)
  :rule-classes nil)
