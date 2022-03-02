; Copyright (C) 2020, Rob Sumners
; Written by Rob Sumners
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; wfo-thry.lisp

(in-package "ACL2")

(include-book "cycle-check")
(include-book "bounded-ords")

; Matt K. mod: Avoid ACL2(p) error from (define in-p ...), "Fast alist
; discipline violated in HONS-GET".  This happened repeatedly 2/28/2022 and
; 3/1/2022 using either "make regression" or cert.pl with ACL2_CUSTOMIZATION
; set to
; <ACL2_directory>/acl2-customization-files/parallel-resource-based.lisp.  It
; didn't happen when using certify-book directly after :ubt 1 and then
; (set-waterfall-parallelism t) followed by (ld "wfo-thry.port") and then
; (certify-book "wfo-thry" ? t :ttags :all :skip-proofs-okp t).  It's a
; mystery....
(set-waterfall-parallelism nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Theory connecting abstract graph to concrete relation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define snap ((x symbolp) (y symbolp))
  (intern-in-package-of-symbol (string-append (symbol-name x) (symbol-name y)) y))

(define in-p (e x)
  :enabled t
  (and (consp x)
       (or (equal e (first x))
           (in-p e (rest x)))))

(define subset-p (x y)
  :enabled t
  (or (atom x)
      (and (in-p (first x) y)
           (subset-p (rest x) y))))

(defthm in-p-subset-p-transfer
  (implies (and (in-p e x) (subset-p x y))
           (in-p e y))
  ;; darn free variable..
  :rule-classes nil)

(define w-ords (a (m omap-p))
  :returns (r w-ord-lst-p :hyp :guard)
  (cdr (nmap-get a m)))

(define max-omap-len ((m omap-p))
  :returns (r natp)
  :verify-guards nil
  (if (endp m) 0 (max (len (cdar m)) (max-omap-len (rest m)))))

(verify-guards max-omap-len)

(defthm max-omap-len-natp-tp
  (natp (max-omap-len m))
  :rule-classes :type-prescription)

(defthm len-w-ords-max-omap-len
  (<= (len (w-ords a m)) (max-omap-len m))
  :hints (("Goal" :in-theory (enable max-omap-len w-ords)))
  :rule-classes (:linear :rewrite))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro def-valid-wf-corr-assumption (name)
  (declare (xargs :guard (symbolp name)))
  (let ((rel-p (snap name '-rel-p)) ;; concrete domain relation we are showing is well-founded
        (map-e (snap name '-map-e)) ;; explicit value map (nodes in the graph)
        (map-o (snap name '-map-o)) ;; maps a state and ordering to a bpll measure..
        (o-bnd (snap name '-o-bnd))
        (a-dom (snap name '-a-dom))
        (nexts (snap name '-nexts))
        (chk-ord-arc (snap name '-chk-ord-arc)))
    (let (;; theorems/properties we define..
          (map-o-returns-o-bnd-bpl    (snap name '-map-o-returns-o-bnd-bpl))
          (a-dom-are-arcs             (snap name '-a-dom-are-arcs))
          (a-dom-non-empty            (snap name '-a-dom-non-empty))
          (nexts-are-arcs             (snap name '-nexts-are-arcs))
          (map-e-in-a-dom             (snap name '-map-e-in-a-dom))
          (natp-o-bnd                 (snap name '-natp-o-bnd))
          (map-e-member-nexts         (snap name '-map-e-member-nexts))
          (map-o-decrement-strict     (snap name '-map-o-decrement-strict))
          (map-o-decrement-non-strict (snap name '-map-o-decrement-non-strict)))
      `(progn
         ;;;; abstract explicit-state assumptions:
         (defthm ,a-dom-are-arcs          (arcs-p (,a-dom)))
         (defthm ,a-dom-non-empty         (consp (,a-dom)))
         (defthm ,map-e-in-a-dom          (in-p (,map-e x) (,a-dom)))
         (defthm ,nexts-are-arcs          (arcs-p (,nexts a)))
         (defthm ,map-e-member-nexts
           (implies (,rel-p x y)
                    (in-p (,map-e y) (,nexts (,map-e x)))))
         ;;;; ordering symbolic-state assumptions:
         (defthm ,natp-o-bnd              (natp (,o-bnd))
           :rule-classes (:rewrite :type-prescription))
         (defthm ,map-o-returns-o-bnd-bpl (bplp (,map-o x o) (,o-bnd)))
         (defthm ,map-o-decrement-strict
           (implies (and (,rel-p x y)
                         (equal (,chk-ord-arc (,map-e x) (,map-e y) o) :<<))
                    (bnl< (,map-o y o) (,map-o x o) (,o-bnd))))
         (defthm ,map-o-decrement-non-strict
           (implies (and (,rel-p x y)
                         (equal (,chk-ord-arc (,map-e x) (,map-e y) o) t))
                    (bnl<= (,map-o y o) (,map-o x o) (,o-bnd))))
         ))))

(defmacro def-valid-wf-corr-conclusion (name)
  (declare (xargs :guard (symbolp name)))
  (let (;; functions we assume...
        (rel-p       (snap name '-rel-p)) ;; concrete domain relation we are showing is well-founded
        (map-e       (snap name '-map-e)) ;; explicit value map (nodes in the graph)
        (map-o       (snap name '-map-o)) ;; maps a state and ordering to a bpll measure..
        (o-bnd       (snap name '-o-bnd))
        (a-dom       (snap name '-a-dom))
        (nexts       (snap name '-nexts))
        (chk-ord-arc (snap name '-chk-ord-arc))
        ;; functions we define...
        (w-ord<        (snap name '-w-ord<))
        (w-ord<=       (snap name '-w-ord<=))
        (w-ords<       (snap name '-w-ords<))
        (build-bpll    (snap name '-build-bpll))
        (chk-omap-arc  (snap name '-chk-omap-arc))
        (chk-omap-node (snap name '-chk-omap-node))
        (chk-omap      (snap name '-chk-omap))
        (mk-bpll       (snap name '-mk-bpll))
        (msr           (snap name '-msr))
        (valid-omap    (snap name '-valid-omap))
        (mk-bpl        (snap name '-mk-bpl))
        (bpl-bnd       (snap name '-bpl-bnd)))
    (let (;; theorems we prove... (given assumptions above)
          (w-ords<-impl-bnll<           (snap name '-w-ords<-impl-bnll<))
          (len-build-bpll               (snap name '-len-build-bpll))
          (max-omap-len-mk-bpll         (snap name '-max-omap-len-mk-bpll))
          (chk-omap-node-implies-w-ords (snap name '-chk-omap-node-implies-w-ords))
          (chk-omap-implies-w-ords<-1   (snap name '-chk-omap-implies-w-ords<-1))
          (chk-omap-implies-w-ords<     (snap name '-chk-omap-implies-w-ords<))
          (msr-is-ord-on-domp           (snap name '-msr-is-ord-on-domp))
          (relp-well-founded            (snap name '-relp-well-founded))
          (mk-bpll-becomes-bplp         (snap name '-mk-bpll-becomes-bplp))
          (mk-bpll-transfers-rel-p-bnl< (snap name '-mk-bpll-transfers-rel-p-bnl<)))
      `(progn
         (in-theory (enable ord=))

         ;; the following is a yucky lemma, that I don't want to use
         ;; outside of this book, but it is useful for proving one of
         ;; the conclusion lemmas:
         (local
          (defthm bnl<=-bnl<-helper
            (implies (and (natp b)
                          (bnlp x b)
                          (bnlp y b)
                          (not (bnl< x y b))
                          (bnl<= x y b))
                     (iff (equal x y) t))))

         (define ,w-ord< ((dst-w w-ord-p) (src-w w-ord-p)
                          (dst node-p) (src node-p))
           :enabled t
           (cond ((and (natp dst-w) (natp src-w))
                  (< dst-w src-w))
                 ((and (ord-p dst-w) (ord= src-w dst-w))
                  (eq (,chk-ord-arc src dst src-w) :<<))
                 ;; really shouldn't get here.. probably should throw an error..
                 ;; but leaving this as just nil for incomparable ordering descriptors..
                 (t nil)))

         (define ,w-ord<= ((dst-w w-ord-p) (src-w w-ord-p)
                           (dst node-p) (src node-p))
           :enabled t
           (cond ((and (natp dst-w) (natp src-w))
                  (<= dst-w src-w))
                 ((and (ord-p dst-w) (ord= src-w dst-w))
                  (b* ((x (,chk-ord-arc src dst src-w)))
                    (or (eq x t) (eq x :<<))))
                 ;; really shouldn't get here.. probably should throw an error..
                 ;; but leaving this as just nil for incomparable ordering descriptors..
                 (t nil)))

         (define ,w-ords< ((dst-w w-ord-lst-p) (src-w w-ord-lst-p)
                           (dst node-p) (src node-p))
           :enabled t
           (and (not (endp src-w))
                (or (endp dst-w)
                    (,w-ord< (first dst-w) (first src-w) dst src)
                    (and (,w-ord<= (first dst-w) (first src-w) dst src)
                         (,w-ords< (rest dst-w) (rest src-w) dst src)))))

         (define ,build-bpll ((w w-ord-lst-p) x)
           :returns (r (bpllp r (,o-bnd)))
           :enabled t
           (cond ((endp w) ())
                 ((natp (first w))
                  (cons (nat->bpl (first w) (,o-bnd))
                        (,build-bpll (rest w) x)))
                 (t
                  (cons (,map-o x (first w))
                        (,build-bpll (rest w) x)))))

         ;; prove first result that relates w-ords< to bnll< of the built bplls:

         (defthm ,w-ords<-impl-bnll<
           (implies (and (,rel-p src dst)
                         (w-ord-lst-p dst-w)
                         (w-ord-lst-p src-w)
                         (,w-ords< dst-w src-w
                                   (,map-e dst)
                                   (,map-e src)))
                    (bnll< (,build-bpll dst-w dst)
                           (,build-bpll src-w src)
                           (,o-bnd)))
           :rule-classes nil)

         ;; now define our omap checker which crawls over the omap ensuring that
         ;; w-ords in neighboring nodes satisfy w-ords<:

         (define ,chk-omap-arc ((src node-p) (dst node-p) (m omap-p))
           :enabled t
           (,w-ords< (w-ords dst m) (w-ords src m) dst src))

         (define ,chk-omap-node ((nxts arcs-p) (src node-p) (m omap-p))
           (or (endp nxts)
               (and (,chk-omap-arc src (first nxts) m)
                    (,chk-omap-node (rest nxts) src m))))

         (define ,chk-omap ((nodes arcs-p) (m omap-p))
           (or (endp nodes)
               (and (,chk-omap-node (,nexts (first nodes)) (first nodes) m)
                    (,chk-omap (rest nodes) m))))

         ;; pull together some results that chk-omap (along with assumptions)
         ;; ensures we can build a measure for all objects showing rel-p is
         ;; well-founded..

         (define ,mk-bpll (x (m omap-p))
           :enabled t
           :returns (r (bpllp r (,o-bnd)))
           (,build-bpll (w-ords (,map-e x) m) x))

         (defthm ,len-build-bpll
           (equal (len (,build-bpll w x)) (len w)))

         (defthm ,max-omap-len-mk-bpll
           (<= (len (,mk-bpll x m)) (max-omap-len m))
           :hints (("Goal" :in-theory (enable ,mk-bpll)))
           :rule-classes (:linear :rewrite))

         (define ,msr (x (m omap-p))
           :enabled t
           (bnll->o (max-omap-len m) (,mk-bpll x m) (,o-bnd)))

         (defthm ,chk-omap-node-implies-w-ords
           (implies (and (omap-p m)
                         (in-p b n-a)
                         (,chk-omap-node n-a a m))
                    (,w-ords< (w-ords b m) (w-ords a m) b a))
           :hints (("Goal" :in-theory (enable ,chk-omap-node ,chk-omap-arc)))
           :rule-classes nil)

         (defthm ,chk-omap-implies-w-ords<-1
           (implies (and (omap-p m)
                         (,chk-omap d m)
                         (in-p a d))
                    (,chk-omap-node (,nexts a) a m))
           :hints (("Goal" :in-theory (enable ,chk-omap)))
           :rule-classes nil)

         (defthm ,chk-omap-implies-w-ords<
           (implies (and (omap-p m)
                         (,chk-omap (,a-dom) m)
                         (in-p a (,a-dom))
                         (in-p b (,nexts a)))
                    (,w-ords< (w-ords b m) (w-ords a m) b a))
           :hints (("Goal" :use ((:instance ,chk-omap-implies-w-ords<-1
                                            (d (,a-dom)))
                                 (:instance ,chk-omap-node-implies-w-ords
                                            (n-a (,nexts a)))))))

         ;; finally tidy up the omap validity check and export the two theorems
         ;; required to ensure termination:

         (define ,valid-omap (m)
           (and (omap-p m)
                (,chk-omap (,a-dom) m)))

         ;; these final two properties demonstrate that the relation is well-founded on
         ;; the concrete domain:

         (defthm ,msr-is-ord-on-domp
           (o-p (,msr x m)))

         (defthm ,relp-well-founded
           (implies (and (,valid-omap m)
                         (,rel-p x y))
                    (o< (,msr y m) (,msr x m)))
           :hints (("Goal"
                    :in-theory (e/d (,valid-omap) (bnll<-implies-o<-bnll->o))
                    :use ((:instance bnll<-implies-o<-bnll->o
                                     (x (,build-bpll (w-ords (,map-e y) m) y))
                                     (y (,build-bpll (w-ords (,map-e x) m) x))
                                     (n (max-omap-len m))
                                     (b (,o-bnd)))
                          (:instance ,w-ords<-impl-bnll<
                                     (src x)
                                     (dst y)
                                     (src-w (w-ords (,map-e x) m))
                                     (dst-w (w-ords (,map-e y) m)))))))

         ;; BUT, in addition to proving that we have met the requirements of showing that
         ;; there exists an e0-ordinal (in terms of ACL2 ordinals) which is strictly
         ;; decreasing, we also want to prove that we can transform the bpll ordinal that
         ;; is defined by the given omap, but we can also turn that into a bpl ordinal which
         ;; could then be used as an ordering on higher-level omaps..

         (define ,mk-bpl (x (m omap-p))
           (bpll->bpl (,mk-bpll x m) (max-omap-len m) (,o-bnd)))

         (define ,bpl-bnd ((m omap-p))
           :returns (r natp)
           (* (max-omap-len m) (1+ (,o-bnd))))

         (defthm ,mk-bpll-becomes-bplp
           (implies (,valid-omap m)
                    (bplp (,mk-bpl x m) (,bpl-bnd m)))
           :hints (("Goal"
                    :in-theory (e/d (,valid-omap ,mk-bpl ,bpl-bnd) ())
                    :use ((:instance bpll->bpl-is-bplp
                                     (n (max-omap-len m))
                                     (b (,o-bnd))
                                     (x (,mk-bpll x m)))))))

         (defthm ,mk-bpll-transfers-rel-p-bnl<
           (implies (and (,valid-omap m)
                         (,rel-p x y))
                    (bnl< (,mk-bpl y m) (,mk-bpl x m) (,bpl-bnd m)))
           :hints (("Goal"
                    :in-theory (e/d (,valid-omap ,mk-bpl ,bpl-bnd) ())
                    :use ((:instance bpll->bpl-is-bplp
                                     (n (max-omap-len m))
                                     (b (,o-bnd))
                                     (x (,mk-bpll x m)))
                          (:instance bpll->bpl-is-bplp
                                     (n (max-omap-len m))
                                     (b (,o-bnd))
                                     (x (,mk-bpll y m)))
                          (:instance bpll->bpl-bnll<-transfer
                                     (n (max-omap-len m))
                                     (b (,o-bnd))
                                     (x (,mk-bpll y m))
                                     (y (,mk-bpll x m)))
                          (:instance ,w-ords<-impl-bnll<
                                     (src x)
                                     (dst y)
                                     (src-w (w-ords (,map-e x) m))
                                     (dst-w (w-ords (,map-e y) m)))))))
         ))))

;; Now, we show that the assumptions are sufficient to prove the conclusions..

(encapsulate
  (((test-rel-p * *)         => *)
   ((test-map-e *)           => *)
   ((test-map-o * *)         => *)
   ((test-o-bnd)             => *)
   ((test-a-dom)             => *)
   ((test-nexts *)           => *)
   ((test-chk-ord-arc * * *) => *))

  (local
   (progn
     (defun test-rel-p (x y) (declare (ignore x y)) nil)
     (defun test-map-e (x)   (declare (ignore x))   t)
     (defun test-map-o (x o) (declare (ignore x o)) 1)
     (defun test-o-bnd ()                           0)
     (defun test-a-dom ()                           (list t))
     (defun test-nexts (a)   (declare (ignore a))   nil)
     (defun test-chk-ord-arc (src dst ord)
       (declare (ignore src dst ord))
       nil)))

  (def-valid-wf-corr-assumption test)
)
(def-valid-wf-corr-conclusion test)
