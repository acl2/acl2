; Copyright (C) 2020 Centaur Technology
; AIGNET - And-Inverter Graph Networks
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>


(in-package "AIGNET")


(include-book "transform-utils")
(include-book "levels")
(include-book "supergate")
(include-book "cube-contradictionp")
(include-book "eval-toggle")
(include-book "centaur/fty/baselists" :dir :system)

(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
;; (local (include-book "data-structures/list-defthms" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))
(local (in-theory (disable nth
                           update-nth
                           resize-list
                           make-list-ac
                           true-listp-update-nth
                           acl2::nfix-when-not-natp
                           ;; acl2::resize-list-when-empty
                           ;; acl2::make-list-ac-redef
                           ;; set::double-containment
                           ;; set::sets-are-true-lists
                           acl2::nth-when-zp
                           ;; acl2::nth-with-large-index
                           )))
(local (std::add-default-post-define-hook :fix))



(define gate-node-supergate ((n natp) refcounts aignet)
  :guard (and (id-existsp n aignet)
              (eql (id->type n aignet) (gate-type))
              (< (nfix n) (u32-length refcounts)))
  :returns (super lit-listp)
  ;; BOZO hardcoded limit=1000 and use-muxes=nil
  (if (eql (id->regp n aignet) 1)
      ;; xor
      (b* (((mv children ?limit)
            (lit-collect-superxor (make-lit n 0) t 1000 nil refcounts aignet)))
        children)
    (b* (((mv children ?limit)
          (lit-collect-supergate (make-lit n 0) t nil 1000 nil refcounts aignet)))
      children))
  ///
  (defret aignet-lit-listp-of-<fn>
    (implies (aignet-idp n aignet)
             (aignet-lit-listp super aignet)))

  (defret <fn>-correct
    (and (implies (equal (stype (car (lookup-id n aignet))) :and)
                  (equal (aignet-eval-conjunction super invals regvals aignet)
                         (id-eval n invals regvals aignet)))
         (implies (equal (stype (car (lookup-id n aignet))) :xor)
                  (equal (aignet-eval-parity super invals regvals aignet)
                         (id-eval n invals regvals aignet))))
    :hints(("Goal" :in-theory (enable aignet-eval-parity aignet-eval-conjunction lit-eval))))

  (defret lits-max-id-val-of-<fn>
    (implies (equal (ctype (stype (car (lookup-id n aignet)))) :gate)
             (< (lits-max-id-val super) (nfix n)))
    :rule-classes :linear)

  (defret lits-max-id-val-of-<fn>-weak
    (<= (lits-max-id-val super) (nfix n))
    :hints (("Goal" :use ((:instance lits-max-id-val-of-lit-collect-superxor
                           (lit (make-lit n 0)) (top t) (limit 1000)
                           (superxor nil) (aignet-refcounts refcounts))
                          (:instance lits-max-id-val-of-supergate
                           (lit (make-lit n 0)) (top t) (use-muxes nil) (limit 1000)
                           (supergate nil) (aignet-refcounts refcounts)))))
    :rule-classes :linear)

  (defret true-listp-of-<fn>
    (true-listp super)
    :rule-classes :type-prescription))


(defthm lit->var-of-nth-lte-lits-max-id-val
  (<= (lit->var (nth n lits)) (lits-max-id-val lits))
  :hints(("Goal" :in-theory (enable lits-max-id-val nth)))
  :rule-classes :linear)

(local
 #!satlink
 (fty::deflist lit-list :pred lit-listp :elt-type litp :true-listp t
   :parents (litp)
   :short "List of literals"))


(define spath-existsp ((sink natp) (path nat-listp) refcounts aignet)
  :guard (and (id-existsp sink aignet)
              (< sink (u32-length refcounts)))
  :measure (len path)
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  (if (atom path)
      t
    (and (eql (id->type sink aignet) (gate-type))
         (let ((children (gate-node-supergate sink refcounts aignet)))
           (and (< (lnfix (car path)) (len children))
                (spath-existsp (lit->var (nth (car path) children)) (cdr path) refcounts aignet)))))
  ///
  (defthm spath-existsp-when-consp
    (implies (and (spath-existsp sink path refcounts aignet)
                  (consp path))
             (and (equal (ctype (stype (car (lookup-id sink aignet)))) :gate)
                  ;; (spath-existsp (lit->var (fanin (car path) (lookup-id sink aignet)))
                  ;;                        (cdr path) aignet)
                  (let ((supergate (gate-node-supergate sink refcounts aignet)))
                    (and (< (nfix (car path)) (len supergate))
                         (spath-existsp (lit->var (nth (car path) supergate))
                                        (cdr path) refcounts aignet))))))

  (defthm spath-existsp-of-cons
    (equal (spath-existsp sink (cons child path) refcounts aignet)
           (and (equal (ctype (stype (car (lookup-id sink aignet)))) :gate)
                (let ((supergate (gate-node-supergate sink refcounts aignet)))
                  (and (< (nfix child) (len supergate))
                       (spath-existsp (lit->var (nth child supergate))
                                      path refcounts aignet))))))

  (defthm spath-existsp-of-atom
    (implies (not (consp path))
             (equal (spath-existsp sink path refcounts aignet) t)))
  
  (defthm spath-existsp-of-nil
    (equal (spath-existsp sink nil refcounts aignet) t))

  (local (in-theory (disable (:d spath-existsp)))))

;; The endpoint of a path from a sink node is the source node it ends up at.
(define spath-endpoint ((sink natp) (path nat-listp) refcounts aignet)
  :guard (and (id-existsp sink aignet)
              (< sink (u32-length refcounts))
              (spath-existsp sink path refcounts aignet))
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  :measure (len path)
  (if (atom path)
      (lnfix sink)
    (spath-endpoint (lit->var
                     (nth (car path)
                          (gate-node-supergate sink refcounts aignet)))
                   (cdr path) refcounts aignet))
  ///
  (defthm spath-endpoint-of-cons
    (equal (spath-endpoint sink (cons dir rest) refcounts aignet)
           (spath-endpoint (lit->var
                            (nth dir (gate-node-supergate sink refcounts aignet))) rest refcounts aignet)))

  (defthm spath-endpoint-of-atom
    (implies (not (consp path))
             (equal (spath-endpoint sink path refcounts aignet)
                    (nfix sink))))
  
  (defthm spath-endpoint-of-nil
    (equal (spath-endpoint sink nil refcounts aignet)
           (nfix sink)))

  (local (in-theory (disable (:d spath-endpoint)))))



(define spath-and-literals ((sink natp) (path nat-listp) refcounts aignet)
  :guard (and (id-existsp sink aignet)
              (< sink (u32-length refcounts))
              (spath-existsp sink path refcounts aignet))
  :measure (len path)
  :guard-hints (("Goal" :expand ((spath-existsp sink path refcounts aignet))
                 :in-theory (enable aignet-idp)))
  :prepwork ((local (in-theory (disable satlink::equal-of-lit-fix-backchain
                                        lookup-id-out-of-bounds
                                        lookup-id-in-bounds-when-positive))))
  :returns (and-lits lit-listp)
  (b* (((when (atom path)) nil)
       (supergate (gate-node-supergate sink refcounts aignet))
       (next (nth (car path) supergate))
       ((unless (mbe :logic (non-exec (eq (stype (car (lookup-id sink aignet))) :and))
                     :exec (eql (id->regp sink aignet) 0)))
        (spath-and-literals (lit->var next) (cdr path) refcounts aignet)))
    (append supergate
            (spath-and-literals (lit->var next) (cdr path) refcounts aignet)))
  ///

  (defthm spath-and-literals-of-cons
    (equal (spath-and-literals sink (cons first rest) refcounts aignet)
           (let* ((supergate (gate-node-supergate sink refcounts aignet))
                  (rest (spath-and-literals (lit->var (nth first supergate))
                                            rest refcounts aignet)))
             (if (equal (stype (car (lookup-id sink aignet))) :and)
                 (append supergate rest)
               rest))))

  (defthm spath-and-literals-of-atom
    (implies (not (consp path))
             (equal (spath-and-literals sink path refcounts aignet) nil)))

  (defthm spath-and-literals-of-nil
    (equal (spath-and-literals sink nil refcounts aignet) nil))

  (local (defthm lits-max-id-val-of-append
           (equal (lits-max-id-val (append x y))
                  (max (lits-max-id-val x) (lits-max-id-val y)))
           :hints(("Goal" :in-theory (enable lits-max-id-val)))))
  
  (defthm lits-max-id-val-of-spath-and-literals
    (<= (lits-max-id-val (spath-and-literals sink path refcounts aignet)) (nfix sink))
    :rule-classes :linear)

  (defthm lits-max-id-val-of-spath-and-literals-strong
    (implies (posp sink)
             (< (lits-max-id-val (spath-and-literals sink path refcounts aignet)) (nfix sink)))
    :rule-classes :linear))



;; (define contradictory-literal-lists ((x lit-listp) (y lit-listp))
;;   (if (atom x)
;;       nil
;;     (or (and (member (lit-negate (car x)) (lit-list-fix y)) (lit-fix (car x)))
;;         (contradictory-literal-lists (cdr x) y)))
;;   ///
;;   (defthmd cube-contradictionp-of-append
;;     (iff (cube-contradictionp (append x y))
;;          (or (cube-contradictionp x)
;;              (contradictory-literal-lists x y)
;;              (cube-contradictionp y)))
;;     :hints(("Goal" :in-theory (enable cube-contradictionp)))))





(local (in-theory (disable member
                           lookup-id-in-bounds-when-positive
                           lookup-id-out-of-bounds
                           satlink::equal-of-lit-negate-backchain
                           satlink::lit-negate-not-equal-when-vars-mismatch)))


(define aignet-eval-conjunction-toggle ((lits lit-listp) (toggle natp)
                                        invals regvals aignet)
  :guard (and (aignet-lit-listp lits aignet)
              (id-existsp toggle aignet)
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  :returns (res bitp)
  (if (atom lits)
      1
    (acl2::b-and (lit-eval-toggle (car lits) toggle invals regvals aignet)
                 (aignet-eval-conjunction-toggle (cdr lits) toggle invals regvals aignet)))
  ///)

(defsection eval-conjunction-toggle-of-lit-collect-supergate
  (local
   (progn
     (defthm b-and-associative
       (equal (acl2::b-and (acl2::b-and a b) c)
              (acl2::b-and a (acl2::b-and b c)))
       :hints(("Goal" :in-theory (enable acl2::b-and))))

     (defthm b-and-commute-2
       (equal (acl2::b-and b (acl2::b-and a c))
              (acl2::b-and a (acl2::b-and b c)))
       :hints(("Goal" :in-theory (enable acl2::b-and))))
     (in-theory (disable acl2::nth-when-too-large-cheap))))

  (defret eval-conjunction-toggle-of-lit-collect-supergate
    (implies (and (< 1 (nfix (nth toggle aignet-refcounts)))
                  (or (not top)
                      (not (equal (lit->var lit) (nfix toggle)))))
             (equal (aignet-eval-conjunction-toggle res toggle invals regvals aignet)
                    (acl2::b-and (lit-eval-toggle lit toggle invals regvals aignet)
                                 (aignet-eval-conjunction-toggle supergate toggle invals regvals aignet))))
    :hints (("goal" :induct <call>
             :do-not-induct t
             :in-theory (e/d (eval-and-of-lits-toggle
                              (:i <fn>))
                             ((:definition lit-collect-supergate)))
             :expand ((:free (top use-muxes) <call>)))
            (and stable-under-simplificationp
                 '(:expand ((lit-eval-toggle lit toggle invals regvals aignet)
                            (id-eval-toggle (lit-id lit) toggle invals regvals aignet)
                            (:free (a b)
                             (aignet-eval-conjunction-toggle (cons a b) toggle invals regvals aignet))))))
    :fn lit-collect-supergate))

(define aignet-eval-parity-toggle ((lits lit-listp) (toggle natp) invals regvals aignet)
  :guard (and (aignet-lit-listp lits aignet)
              (id-existsp toggle aignet)
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  :returns (res bitp)
  (if (atom lits)
      0
    (b-xor (lit-eval-toggle (car lits) toggle invals regvals aignet)
           (aignet-eval-parity-toggle (cdr lits) toggle invals regvals aignet))))


(defsection eval-parity-toggle-of-lit-collect-superxor
  (local
   (progn
     (defthm b-xor-associative
       (equal (acl2::b-xor (acl2::b-xor a b) c)
              (acl2::b-xor a (acl2::b-xor b c)))
       :hints(("Goal" :in-theory (enable acl2::b-xor))))

     (defthm b-xor-commute-2
       (equal (acl2::b-xor b (acl2::b-xor a c))
              (acl2::b-xor a (acl2::b-xor b c)))
       :hints(("Goal" :in-theory (enable acl2::b-xor))))
     (in-theory (disable acl2::nth-when-too-large-cheap))))

  (defret eval-parity-toggle-of-lit-collect-superxor
    (implies (and (< 1 (nfix (nth toggle aignet-refcounts)))
                  (or (not top)
                      (not (equal (lit->var lit) (nfix toggle)))))
             (equal (aignet-eval-parity-toggle res toggle invals regvals aignet)
                    (acl2::b-xor (lit-eval-toggle lit toggle invals regvals aignet)
                                 (aignet-eval-parity-toggle superxor toggle invals regvals aignet))))
    :hints (("goal" :induct <call>
             :do-not-induct t
             :in-theory (e/d (eval-xor-of-lits-toggle
                              (:i <fn>))
                             ((:definition lit-collect-superxor)))
             :expand ((:free (top use-muxes) <call>)))
            (and stable-under-simplificationp
                 '(:expand ((lit-eval-toggle lit toggle invals regvals aignet)
                            (id-eval-toggle (lit-id lit) toggle invals regvals aignet)
                            (:free (a b)
                             (aignet-eval-parity-toggle (cons a b) toggle invals regvals aignet))))))
    :fn lit-collect-superxor))


(define lit-list-has-const0-under-toggle ((x lit-listp) (toggle natp)
                                          invals regvals aignet)
  :guard (and (aignet-lit-listp x aignet)
              (id-existsp toggle aignet)
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  (if (atom x)
      nil
    (or (and (eql (lit-eval (car x) invals regvals aignet) 0)
             (eql (lit-eval-toggle (car x) toggle invals regvals aignet) 0))
        (lit-list-has-const0-under-toggle (cdr x) toggle invals regvals aignet)))
  ///
  (defthm lit-list-has-const0-under-toggle-of-append
    (equal (lit-list-has-const0-under-toggle (append x y) toggle invals regvals aignet)
           (or (lit-list-has-const0-under-toggle x toggle invals regvals aignet)
               (lit-list-has-const0-under-toggle y toggle invals regvals aignet))))

  (defthm lit-list-has-const0-under-toggle-of-nil
    (not (lit-list-has-const0-under-toggle nil toggle invals regvals aignet)))

  (defthmd aignet-eval-conjunction-when-lit-list-has-const0-under-toggle
    (implies (lit-list-has-const0-under-toggle x toggle invals regvals aignet)
             (equal (aignet-eval-conjunction x invals regvals aignet) 0))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction))))

  (defthmd aignet-eval-conjunction-toggle-when-lit-list-has-const0-under-toggle
    (implies (lit-list-has-const0-under-toggle x toggle invals regvals aignet)
             (equal (aignet-eval-conjunction-toggle x toggle invals regvals aignet) 0))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction-toggle))))

  (defthm lit-list-has-const0-under-toggle-of-and-supergate
    (implies (and (equal (stype (car (lookup-id sink aignet))) :and)
                  (not (equal (id-eval sink invals regvals aignet)
                              (id-eval-toggle sink toggle invals regvals aignet)))
                  (< 1 (nfix (nth toggle refcounts)))
                  (not (equal (nfix toggle) (nfix sink))))
             (not (lit-list-has-const0-under-toggle
                   (gate-node-supergate sink refcounts aignet)
                   toggle invals regvals aignet)))
    :hints (("goal" :in-theory (enable gate-node-supergate)
             :use ((:instance aignet-eval-conjunction-toggle-when-lit-list-has-const0-under-toggle
                    (x (gate-node-supergate sink refcounts aignet)))
                   (:instance aignet-eval-conjunction-when-lit-list-has-const0-under-toggle
                    (x (gate-node-supergate sink refcounts aignet))))
            :expand ((aignet-eval-conjunction nil invals regvals aignet)
                     (aignet-eval-conjunction-toggle nil toggle invals regvals aignet)
                     (:free (var neg) (lit-eval (make-lit var neg) invals regvals aignet))
                     (:free (var neg) (lit-eval-toggle (make-lit var neg) toggle invals regvals aignet))))))

  (defthmd lit-list-has-const0-under-toggle-when-member
    (implies (and (member-equal lit (lit-list-fix x))
                  (equal (lit-eval lit invals regvals aignet) 0)
                  (equal (lit-eval-toggle lit toggle invals regvals aignet) 0))
             (lit-list-has-const0-under-toggle x toggle invals regvals aignet))
    :hints(("Goal" :in-theory (enable member-equal lit-list-fix)))))


(defsection cube-contradictionp
  (local (defthm aignet-eval-conjunction-when-member-0
           (implies (and (member-equal k (lit-list-fix x))
                         (equal (lit-eval-toggle k toggle invals regvals aignet) 0))
                    (equal (aignet-eval-conjunction-toggle x toggle invals regvals aignet) 0))
           :hints(("Goal" :in-theory (enable aignet-eval-conjunction-toggle member-equal)))))

  (local (defthm b-xor-b-not
           (equal (b-xor (b-not a) b)
                  (b-not (b-xor a b)))
           :hints(("Goal" :in-theory (enable b-not)))))
  
  (defthm lit-eval-toggle-of-lit-negate
    (equal (lit-eval-toggle (lit-negate x) toggle invals regvals aignet)
           (b-not (lit-eval-toggle x toggle invals regvals aignet)))
    :hints(("Goal" :expand ((:free (x) (lit-eval-toggle x toggle invals regvals aignet))))))
  
  (defthm aignet-eval-conjunction-toggle-when-cube-contradictionp
    (implies (cube-contradictionp x)
             (equal (aignet-eval-conjunction-toggle x toggle invals regvals aignet) 0))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction-toggle
                                      cube-contradictionp))))

  (defthm cube-contradictionp-of-gate-node-supergate-when-and
    (implies (and (equal (stype (car (lookup-id sink aignet))) :and)
                  (not (equal (id-eval sink invals regvals aignet)
                              (id-eval-toggle sink toggle invals regvals aignet)))
                  (< 1 (nfix (nth toggle refcounts)))
                  (not (equal (nfix toggle) (nfix sink))))
             (not (cube-contradictionp (gate-node-supergate sink refcounts aignet))))
    :hints (("goal" :in-theory (e/d (gate-node-supergate)
                                    (aignet-eval-conjunction-toggle-when-cube-contradictionp
                                     cube-contradictionp-correct))
             :use ((:instance aignet-eval-conjunction-toggle-when-cube-contradictionp
                    (x (gate-node-supergate sink refcounts aignet)))
                   (:instance cube-contradictionp-correct
                    (x (gate-node-supergate sink refcounts aignet))))
            :expand ((aignet-eval-conjunction nil invals regvals aignet)
                     (aignet-eval-conjunction-toggle nil toggle invals regvals aignet)
                     (:free (var neg) (lit-eval (make-lit var neg) invals regvals aignet))
                     (:free (var neg) (lit-eval-toggle (make-lit var neg) toggle invals regvals aignet)))))))
                  

(define has-toggling-lit ((x lit-listp) (toggle natp) invals regvals aignet)
  :guard (and (aignet-lit-listp x aignet)
              (id-existsp toggle aignet)
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  (if (atom x)
      nil
    (or (not (eql (lit-eval (car x) invals regvals aignet)
                  (lit-eval-toggle (car x) toggle invals regvals aignet)))
        (has-toggling-lit (cdr x) toggle invals regvals aignet)))

  ///
  (fty::deffixequiv has-toggling-lit)
  
  (local (Defthm b-xor-of-b-not-1
           (equal (b-xor (b-not a) b)
                  (b-not (b-xor a b)))
           :hints(("Goal" :in-theory (enable b-not)))))

  (local (Defthm b-xor-of-b-not-2
           (equal (b-xor a (b-not b))
                  (b-not (b-xor a b)))
           :hints(("Goal" :in-theory (enable b-not)))))

  (local (defthm id-eval-toggle-of-toggle
           (equal (id-eval-toggle toggle toggle invals regvals aignet)
                  (b-not (id-eval toggle invals regvals aignet)))
           :hints (("goal" :expand
                    ((id-eval-toggle toggle toggle invals regvals aignet)
                     (id-eval toggle invals regvals aignet))
                    :in-theory (enable eval-xor-of-lits-toggle
                                       eval-xor-of-lits
                                       eval-and-of-lits-toggle
                                       eval-and-of-lits
                                       lit-eval-toggle
                                       lit-eval)))))

  
  (local (defthmd lit-eval-toggle-when-lit->var-equal-toggle
           (implies (equal (lit->var lit) (nfix toggle))
                    (equal (lit-eval-toggle lit toggle invals regvals aignet)
                           (b-not (lit-eval lit invals regvals aignet))))
           :hints(("Goal" :in-theory (enable lit-eval-toggle lit-eval)
                   :expand ((lit-eval-toggle lit toggle invals regvals aignet)
                            (lit-eval lit invals regvals aignet))))))

  (local (defthm lit-eval-toggle-of-lit->var
           (equal (lit-eval-toggle lit (lit->var lit) invals regvals aignet)
                  (b-not (lit-eval lit invals regvals aignet)))
           :hints (("goal" :in-theory (enable lit-eval-toggle-when-lit->var-equal-toggle)))))

  
  (local (defthm has-toggling-lit-when-member
           (implies (and (member-equal lit (lit-list-fix supergate))
                         (not (equal (lit-eval lit invals regvals aignet)
                                     (lit-eval-toggle lit toggle invals regvals aignet))))
                    (has-toggling-lit supergate toggle invals regvals aignet))
           :hints(("Goal" :in-theory (enable has-toggling-lit lit-list-fix member-equal)))))

  (local (defthmd has-toggling-lit-when-eval-conjunction-differs
           (implies (not (equal (aignet-eval-conjunction x invals regvals aignet)
                                (aignet-eval-conjunction-toggle x toggle invals regvals aignet)))
                    (has-toggling-lit x toggle invals regvals aignet))
           :hints(("Goal" :in-theory (enable aignet-eval-conjunction
                                             aignet-eval-conjunction-toggle)))))

  (local (defthmd has-toggling-lit-when-eval-parity-differs
           (implies (not (equal (aignet-eval-parity x invals regvals aignet)
                                (aignet-eval-parity-toggle x toggle invals regvals aignet)))
                    (has-toggling-lit x toggle invals regvals aignet))
           :hints(("Goal" :in-theory (enable aignet-eval-parity
                                             aignet-eval-parity-toggle)))))

  ;; (local (defthm lit-collect-supergate-preserves-supergate-toggle
  ;;          (implies (has-toggling-lit supergate toggle invals regvals aignet)
  ;;                   (has-toggling-lit
  ;;                    (mv-nth 0 (lit-collect-supergate lit top use-muxes limit supergate refcounts aignet))
  ;;                    toggle invals regvals aignet))
  ;;          :hints (("goal" :induct (lit-collect-supergate lit top use-muxes limit supergate refcounts aignet)
  ;;                   :in-theory (enable (:i lit-collect-supergate))
  ;;                   :expand ((:free (top use-muxes limit)
  ;;                             (lit-collect-supergate lit top use-muxes limit supergate refcounts aignet))
  ;;                            (lit-eval-toggle 0 toggle invals regvals aignet)
  ;;                            (id-eval-toggle 0 toggle invals regvals aignet))))))
  
  ;; (local (defthm id-eval-toggle-in-terms-of-supergate
  ;;          (implies (and (not (equal (lit-eval lit invals regvals aignet)
  ;;                                    (lit-eval-toggle lit toggle invals regvals aignet)))
  ;;                        (< 1 (nfix (nth toggle refcounts)))
  ;;                        (or (not top)
  ;;                            (not (equal (lit->var lit) (nfix toggle)))))
  ;;                   (has-toggling-lit
  ;;                    (mv-nth 0 (lit-collect-supergate lit top use-muxes limit supergate refcounts aignet))
  ;;                                     toggle invals regvals aignet))
  ;;          :hints (("goal" :induct (lit-collect-supergate lit top use-muxes limit supergate refcounts aignet)
  ;;                   :in-theory (enable (:i lit-collect-supergate) b-and)
  ;;                   :expand ((:free (top use-muxes limit)
  ;;                             (lit-collect-supergate lit top use-muxes limit supergate refcounts aignet))
  ;;                            (lit-eval lit invals regvals aignet)
  ;;                            (lit-eval-toggle lit toggle invals regvals aignet)
  ;;                            (id-eval (lit->var lit) invals regvals aignet)
  ;;                            (:free (toggle) (id-eval-toggle (lit->var lit) toggle invals regvals aignet))
  ;;                            (:free (a b) (eval-and-of-lits a b invals regvals aignet))
  ;;                            (:free (a b) (eval-xor-of-lits a b invals regvals aignet))
  ;;                            (:free (a b) (eval-and-of-lits-toggle a b toggle invals regvals aignet))
  ;;                            (:free (a b) (eval-xor-of-lits-toggle a b toggle invals regvals aignet)))
  ;;                   :do-not-induct t)
  ;;                  (and stable-under-simplificationp
  ;;                       '(:in-theory (enable lit-eval-toggle-when-lit->var-equal-toggle))))))

  ;; (local (defthm lit-collect-superxor-preserves-supergate-toggle
  ;;          (implies (has-toggling-lit supergate toggle invals regvals aignet)
  ;;                   (has-toggling-lit
  ;;                    (mv-nth 0 (lit-collect-superxor lit top limit supergate refcounts aignet))
  ;;                    toggle invals regvals aignet))
  ;;          :hints (("goal" :induct (lit-collect-superxor lit top limit supergate refcounts aignet)
  ;;                   :in-theory (enable (:i lit-collect-superxor))
  ;;                   :expand ((:free (top limit)
  ;;                             (lit-collect-superxor lit top limit supergate refcounts aignet))
  ;;                            (lit-eval-toggle 0 toggle invals regvals aignet)
  ;;                            (id-eval-toggle 0 toggle invals regvals aignet))))))
  
  ;; (local (defthm id-eval-toggle-in-terms-of-superxor
  ;;          (implies (and (not (equal (lit-eval lit invals regvals aignet)
  ;;                                    (lit-eval-toggle lit toggle invals regvals aignet)))
  ;;                        (< 1 (nfix (nth toggle refcounts)))
  ;;                        (or (not top)
  ;;                            (not (equal (lit->var lit) (nfix toggle)))))
  ;;                   (has-toggling-lit
  ;;                    (mv-nth 0 (lit-collect-superxor lit top limit supergate refcounts aignet))
  ;;                                     toggle invals regvals aignet))
  ;;          :hints (("goal" :induct (lit-collect-superxor lit top limit supergate refcounts aignet)
  ;;                   :in-theory (enable (:i lit-collect-superxor) b-and)
  ;;                   :expand ((:free (top limit)
  ;;                             (lit-collect-superxor lit top limit supergate refcounts aignet))
  ;;                            (lit-eval lit invals regvals aignet)
  ;;                            (lit-eval-toggle lit toggle invals regvals aignet)
  ;;                            (id-eval (lit->var lit) invals regvals aignet)
  ;;                            (id-eval-toggle (lit->var lit) toggle invals regvals aignet)
  ;;                            (:free (a b) (eval-and-of-lits a b invals regvals aignet))
  ;;                            (:free (a b) (eval-xor-of-lits a b invals regvals aignet))
  ;;                            (:free (a b) (eval-and-of-lits-toggle a b toggle invals regvals aignet))
  ;;                            (:free (a b) (eval-xor-of-lits-toggle a b toggle invals regvals aignet)))
  ;;                   :do-not-induct t))))
  
  (defthm supergate-has-toggling-lit-when-toggles
    (implies (and (not (equal (id-eval sink invals regvals aignet)
                              (id-eval-toggle sink toggle invals regvals aignet)))
                  (< 1 (nfix (nth toggle refcounts)))
                  (not (equal (nfix toggle) (nfix sink))))
             (has-toggling-lit (gate-node-supergate sink refcounts aignet)
                               toggle invals regvals aignet))
    :hints(("Goal" :in-theory (e/d (gate-node-supergate)
                                   (has-toggling-lit-when-eval-parity-differs
                                    has-toggling-lit-when-eval-conjunction-differs
                                    has-toggling-lit))
            :use ((:instance has-toggling-lit-when-eval-parity-differs
                   (x (gate-node-supergate sink refcounts aignet)))
                  (:instance has-toggling-lit-when-eval-conjunction-differs
                   (x (gate-node-supergate sink refcounts aignet))))
            :expand ((aignet-eval-parity nil invals regvals aignet)
                     (aignet-eval-parity-toggle nil toggle invals regvals aignet)
                     (aignet-eval-conjunction nil invals regvals aignet)
                     (aignet-eval-conjunction-toggle nil toggle invals regvals aignet)
                     (:free (var neg) (lit-eval (make-lit var neg) invals regvals aignet))
                     (:free (var neg) (lit-eval-toggle (make-lit var neg) toggle invals regvals aignet)))))))



(define min-toggling-lit ((x lit-listp) (toggle natp) invals regvals aignet)
  :guard (and (aignet-lit-listp x aignet)
              (id-existsp toggle aignet)
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  :returns (min-index natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (b* ((toggles (not (eql (lit-eval (car x) invals regvals aignet)
                            (lit-eval-toggle (car x) toggle invals regvals aignet))))
         (rest (min-toggling-lit (cdr x) toggle invals regvals aignet))
         ((unless toggles) (+ 1 rest))
         ((unless (< rest (len (cdr x)))) 0)
         (other-min (nth rest (cdr x))))
      (if (<= (lit->var (car x)) (lit->var other-min))
          0
        (+ 1 rest))))
  ///
  (defret min-toggling-lit-bound
    (<= min-index (len x))
    :rule-classes :linear)

  (defret min-toggling-lit-bound-strong-rw
    (iff (< min-index (len x))
         (has-toggling-lit x toggle invals regvals aignet))
    :hints(("Goal" :in-theory (enable has-toggling-lit))))

  (defret min-toggling-lit-bound-strong-linear
    (implies (has-toggling-lit x toggle invals regvals aignet)
             (< min-index (len x)))
    :rule-classes :linear)

  (defret min-toggling-lit-bound-equal-rw
    (iff (equal min-index (len x))
         (not (has-toggling-lit x toggle invals regvals aignet)))
    :hints(("Goal" :in-theory (enable has-toggling-lit))))

  (local (defthm len-of-lit-list-fix
           (equal (len (lit-list-fix x)) (len x))))

  (local (defthm cdr-of-lit-list-fix
           (equal (cdr (lit-list-fix x)) (lit-list-fix (cdr x)))))

  (local (defthm nth-of-lit-list-fix
           (lit-equiv (nth n (lit-list-fix x))
                      (lit-fix (nth n x)))
           :hints(("Goal" :in-theory (enable nth)))))

  (defret min-toggling-lit-toggles
    (implies (has-toggling-lit x toggle invals regvals aignet)
             (not (equal (id-eval (lit->var (nth min-index x)) invals regvals aignet)
                         (id-eval-toggle (lit->var (nth min-index x)) toggle invals regvals aignet))))
    :hints(("Goal" :in-theory (e/d (lit-eval lit-eval-toggle)
                                   (min-toggling-lit-bound-strong-linear
                                    id-eval-toggle-when-less))
            :expand ((has-toggling-lit x toggle invals regvals aignet)))))

  (local (defthm has-toggling-lit-when-member
           (implies (and (member-equal lit (lit-list-fix supergate))
                         (not (equal (lit-eval lit invals regvals aignet)
                                     (lit-eval-toggle lit toggle invals regvals aignet))))
                    (has-toggling-lit supergate toggle invals regvals aignet))
           :hints(("Goal" :in-theory (enable has-toggling-lit lit-list-fix member-equal)))))
  
  (defret min-toggling-lit-is-minimum
    (implies (and (not (equal (lit-eval k invals regvals aignet)
                              (lit-eval-toggle k toggle invals regvals aignet)))
                  (member-equal k (lit-list-fix x)))
             (<= (lit->var (nth min-index x)) (lit->var k)))
    :hints(("Goal" :in-theory (enable nth lit-list-fix member-equal)))
    :rule-classes :linear))

(local (defthm aignet-litp-nth-of-aignet-lit-list
         (implies (and (aignet-lit-listp x aignet)
                       (< (nfix n) (len x)))
                  (aignet-litp (nth n x) aignet))
         :hints(("Goal" :in-theory (enable aignet-lit-listp nth)))))


(local
 (defsection not-two-cubes-contradictionp-lemma
   ;; A lemma for contradictionp-of-toggle-witness-path is that there
   ;; can't be contradictory literals between an AND supergate whose conjunction
   ;; toggles and the AND literals on the path starting from its minimum toggling lit.

   ;; Neither the supergate nor the path may have constant 0 literals, so all
   ;; literals are constant 1 or toggling.  Therefore, there may only be
   ;; contradictions between toggling literals.  But the path literals all have
   ;; variables less than the minimum toggling literal of the supergate, so none
   ;; of them may be contradictory either.  Whew.

   
   
   (local (defthm member-equal-when-lits-max-id-val-less
            (implies (< (lits-max-id-val y) (lit->var x))
                     (not (member-equal x (lit-list-fix y))))
            :hints(("Goal" :in-theory (enable lit-list-fix lits-max-id-val member-equal)))))


   
   (local (defthm not-two-cubes-contradictionp-when-no-toggling-lit
            (implies (and (two-cubes-contradictionp x y)
                          (not (lit-list-has-const0-under-toggle
                                x toggle invals regvals aignet))
                          (not (has-toggling-lit x toggle invals regvals aignet)))
                     (lit-list-has-const0-under-toggle
                      y toggle invals regvals aignet))
            :hints(("Goal" :in-theory (enable lit-list-has-const0-under-toggle
                                              has-toggling-lit
                                              two-cubes-contradictionp
                                              lit-list-has-const0-under-toggle-when-member)))))
   
   (defthmd not-two-cubes-contradictionp-lemma
     (implies (and (not (lit-list-has-const0-under-toggle
                         x toggle invals regvals aignet))
                   (not (lit-list-has-const0-under-toggle
                         y toggle invals regvals aignet))
                   (has-toggling-lit x toggle invals regvals aignet)
                   (< (lits-max-id-val y)
                      (lit->var (nth (min-toggling-lit x toggle invals regvals aignet)
                                     x))))
              (not (two-cubes-contradictionp x y)))
     :hints(("Goal" :in-theory (e/d (;; two-cubes-contradictionp
                                     ;; lit-list-has-const0-under-toggle
                                     ;; has-toggling-lit
                                     ;; min-toggling-lit
                                     lit-list-has-const0-under-toggle-when-member
                                     ;; nth
                                     )
                                    (min-toggling-lit-bound-strong-linear
                                     min-toggling-lit-bound
                                     acl2::nth-when-too-large-cheap))
             :induct (len x)
             :expand ((two-cubes-contradictionp x y)
                      (min-toggling-lit x toggle invals regvals aignet)
                      (:free (n) (nth n x))
                      (has-toggling-lit x toggle invals regvals aignet)
                      (lit-list-has-const0-under-toggle
                       x toggle invals regvals aignet))
             :do-not-induct t)))))

(define toggle-witness-spath ((sink natp) (source natp) invals regvals refcounts aignet)
  ;; Given that sink is toggled by source, find a path from sink to source
  ;; containing no contradictory AND siblings and no const0 siblings.
  :guard (and (id-existsp sink aignet)
              (id-existsp source aignet)
              (< sink (u32-length refcounts))
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals))
              (not (equal (id-eval sink invals regvals aignet)
                          (id-eval-toggle sink source invals regvals aignet)))
              (< 1 (get-u32 source refcounts)))
  :measure (nfix sink)
  :returns (path nat-listp)
  ;; :verify-guards nil
  (b* (((when (or (<= (lnfix sink) (lnfix source))
                  (not (eql (id->type sink aignet) (gate-type)))))
        nil)
       (supergate (gate-node-supergate sink refcounts aignet))
       (next-idx (min-toggling-lit supergate source invals regvals aignet)))
    (cons next-idx (toggle-witness-spath (lit->var (nth next-idx supergate))
                                        source invals regvals refcounts aignet)))
  ///
  (local (in-theory (disable (:d toggle-witness-spath))))
  
  (defret spath-existsp-of-<fn>
    (implies (and (not (equal (id-eval sink invals regvals aignet)
                              (id-eval-toggle sink source invals regvals aignet)))
                  (< 1 (nfix (nth source refcounts))))
             (spath-existsp sink path refcounts aignet))
    :hints (("Goal" :induct <call> :expand (<call>))))

  (defret id-eval-toggle-when-not-gate
    (implies (not (equal (ctype (stype (car (lookup-id x aignet)))) :gate))
             (equal (id-eval-toggle x toggle invals regvals aignet)
                    (b-xor (bool->bit (equal (nfix x) (nfix toggle)))
                           (id-eval x invals regvals aignet))))
    :hints(("Goal" :in-theory (enable id-eval-toggle
                                      id-eval))))
                        
  
  (defret spath-endpoint-of-<fn>
    (implies (and (not (equal (id-eval sink invals regvals aignet)
                              (id-eval-toggle sink source invals regvals aignet)))
                  (< 1 (nfix (nth source refcounts))))
             (equal (spath-endpoint sink path refcounts aignet)
                    (nfix source)))
    :hints (("Goal" :induct <call> :expand (<call>))))

  (defret has-const0-of-<fn>
    (implies (and (not (equal (id-eval sink invals regvals aignet)
                              (id-eval-toggle sink source invals regvals aignet)))
                  (< 1 (nfix (nth source refcounts))))
             (not (lit-list-has-const0-under-toggle
                   (spath-and-literals sink path refcounts aignet)
                   source invals regvals aignet)))
    :hints (("Goal" :induct <call> :expand (<call>))))


 (local (defthm not-two-cubes-contradictionp-lemma-rw
           (implies (and (bind-free '((toggle . source)
                                      (invals . invals)
                                      (regvals . regvals)
                                      (aignet . aignet))
                                    (toggle invals regvals aignet))
                         (not (lit-list-has-const0-under-toggle
                               x toggle invals regvals aignet))
                         (not (lit-list-has-const0-under-toggle
                               y toggle invals regvals aignet))
                         (has-toggling-lit x toggle invals regvals aignet)
                         (< (lits-max-id-val y)
                            (lit->var (nth (min-toggling-lit x toggle invals regvals aignet)
                                           x))))
                    (not (two-cubes-contradictionp x y)))
           :hints (("goal" :by not-two-cubes-contradictionp-lemma))))

  (local (defthm lit->var-of-nth-single-0
           (equal (lit->var (nth n '(0))) 0)
           :hints (("goal" :expand ((nth n '(0)))))))
  
  (local (defthm spath-and-literals-of-zero 
           (equal (spath-and-literals 0 path refcounts aignet) nil)
           :hints(("Goal" :in-theory (enable spath-and-literals
                                             gate-node-supergate)
                   :expand ((spath-and-literals 0 path refcounts aignet)
                            (LIT-COLLECT-SUPERGATE 0 T NIL 1000 NIL REFCOUNTS AIGNET))
                   :induct (len path)))))
  
  (defret contradictionp-of-<fn>
    (implies (and (not (equal (id-eval sink invals regvals aignet)
                              (id-eval-toggle sink source invals regvals aignet)))
                  (< 1 (nfix (nth source refcounts))))
             (not (cube-contradictionp
                   (spath-and-literals sink path refcounts aignet))))
    :hints (("Goal" :induct <call> :expand (<call>)
             :in-theory (enable cube-contradictionp-of-append))
            (and stable-under-simplificationp
                 '(:cases ((zp (lit->var
                                (nth (min-toggling-lit
                                      (gate-node-supergate sink refcounts aignet)
                                      source invals regvals aignet)
                                     (gate-node-supergate sink refcounts aignet))))))))))

