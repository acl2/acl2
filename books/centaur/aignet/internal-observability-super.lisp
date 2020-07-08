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
(include-book "std/osets/element-list" :dir :system)

(local (include-book "std/osets/under-set-equiv" :dir :system))
  
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
;; (local (include-book "data-structures/list-defthms" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
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
                           set::pick-a-point-subsetp-equal-strategy
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




;; Dominator info for each node is stored as either
;; (1) T, signifying that every path from an output to the node contains
;;     contradictory literals, or
;; (2) a list of literals, all of which must occur as AND-siblings in every
;;     path from an output to the node not containing contradictory literals,
;;     mergesorted.

(define obs-dom-info-p (x)
  (or (eq x t)
      (and (lit-listp x) (set::setp x)))
  ///
  (define obs-dom-info-fix ((x obs-dom-info-p))
    :returns (new-x obs-dom-info-p)
    :inline t
    (mbe :logic (if (eq x t) t (set::mergesort (lit-list-fix x)))
         :exec x)
    ///
    (defthm obs-dom-info-fix-when-obs-dom-info-p
      (implies (obs-dom-info-p x)
               (equal (obs-dom-info-fix x) x)))

    (fty::deffixtype obs-dom-info :pred obs-dom-info-p :fix obs-dom-info-fix
      :equiv obs-dom-info-equiv :define t :forward t)))

(define make-obs-dom-info-unreached ()
  :returns (info obs-dom-info-p)
  :inline t
  t)

(define make-obs-dom-info-reached ((doms lit-listp))
  :guard (set::setp doms)
  :returns (info obs-dom-info-p
                 :hints (("goal" :in-theory (Enable obs-dom-info-p))))
  :inline t
  (mbe :logic (set::mergesort (lit-list-fix doms))
       :exec doms))

(define obs-dom-info->reached ((x obs-dom-info-p))
  :inline t
  :hooks nil
  (not (eq x t))
  ///
  (defthm obs-dom-info->reached-of-make-obs-dom-info-reached
    (obs-dom-info->reached (make-obs-dom-info-reached doms)))

  (fty::deffixequiv obs-dom-info->reached
    :hints (("goal" :in-theory (enable obs-dom-info-fix)))))


(define obs-dom-info->doms ((x obs-dom-info-p))
  :inline t
  ;; :guard (obs-dom-info->reached x)
  :returns (doms lit-listp)
  :guard-hints (("goal" :in-theory (enable obs-dom-info-p obs-dom-info->reached)))
  :hooks nil
  (if (eq x t)
      nil
    (mbe :logic (set::mergesort (lit-list-fix x))
         :exec x))
  ///
  (defret setp-of-<fn>
    (set::setp doms))
  
  (defthm obs-dom-info->doms-of-make-obs-dom-info-reached
    (equal (obs-dom-info->doms (make-obs-dom-info-reached doms))
           (set::mergesort (lit-list-fix doms)))
    :hints (("goal" :in-theory (enable make-obs-dom-info-reached))))

  (fty::deffixequiv obs-dom-info->doms
    :hints (("goal" :in-theory (enable obs-dom-info-fix))))

  (defthm make-obs-dom-info-reached-of-doms
    (implies (obs-dom-info->reached x)
             (equal (make-obs-dom-info-reached (obs-dom-info->doms x))
                    (obs-dom-info-fix x)))
    :hints(("Goal" :in-theory (enable make-obs-dom-info-reached
                                      obs-dom-info-fix)))))


(acl2::def-b*-binder
  obs-dom-info
  :body (std::da-patbind-fn 'obs-dom-info
                            '((reached . obs-dom-info->reached)
                              (doms . obs-dom-info->doms))
                            args acl2::forms acl2::rest-expr))

(define obs-dom-info-well-formedp ((info obs-dom-info-p) aignet)
  :returns wfp
  (b* (((obs-dom-info info)))
    (or (not info.reached)
        (aignet-lit-listp info.doms aignet)))
  ///
  (defret aignet-lit-listp-of-doms-when-<fn>
    (b* (((obs-dom-info info)))
      (implies wfp
               (aignet-lit-listp info.doms aignet)))
    :hints (("goal" :in-theory (enable obs-dom-info->reached obs-dom-info->doms)))))





(fty::deflist obs-dom-info-list :elt-type obs-dom-info :true-listp t)

(make-event
 `(acl2::def-1d-arr obs-dom-array
    :slotname dominfo
    :pred obs-dom-info-p
    :fix obs-dom-info-fix
    :default-val ,(make-obs-dom-info-unreached)
    :rename ((resize-dominfos . resize-dominfo)
             (dominfos-length . dominfo-length))))

(defthm obs-dom-array$ap-is-obs-dom-info-list-p
  (equal (obs-dom-array$ap x)
         (obs-dom-info-list-p x)))


(local
 (defsection set-stuff-in-terms-of-list-stuff
   
   (defthm head-when-setp
     (implies (set::setp x)
              (equal (set::head x) (car x)))
     :hints(("Goal" :in-theory (enable set::head))))

   (defthm tail-when-setp
     (implies (set::setp x)
              (equal (set::tail x) (cdr x)))
     :hints(("Goal" :in-theory (enable set::tail))))

   (defthm empty-when-setp
     (implies (set::setp x)
              (equal (set::empty x) (atom x)))
     :hints(("Goal" :in-theory (enable set::empty))))

   (defthm setp-of-cdr
     (implies (set::setp x)
              (set::setp (cdr x)))
     :hints(("Goal" :in-theory (enable set::setp))))


   (defthm in-when-setp
     (implies (set::setp x)
              (iff (set::in k x)
                   (member-equal k x)))
     :hints(("Goal" :in-theory (enable set::in))))

   (defthm subset-when-setp
     (implies (and (set::setp x) (set::setp y))
              (equal (set::subset x y)
                     (subsetp-equal x y)))
     :hints(("Goal" :in-theory (enable set::subset))))))

(define obs-dom-info-subsetp ((x obs-dom-info-p)
                              (y obs-dom-info-p))
  :returns (subsetp)
  (b* (((obs-dom-info x))
       ((obs-dom-info y)))
    (or (not y.reached)
        (cube-contradictionp y.doms)
        (and x.reached
             (mbe :logic (subsetp-equal x.doms y.doms)
                  :exec (set::subset x.doms y.doms)))))
  ///
  (local (defthm aignet-eval-conjunction-when-member
           (implies (and (equal (lit-eval x invals regvals aignet) 0)
                         (member (lit-fix x) (lit-list-fix y)))
                    (equal (aignet-eval-conjunction y invals regvals aignet) 0))
           :hints(("Goal" :in-theory (enable aignet-eval-conjunction)))))
  (local (defthm aignet-eval-conjunction-when-subsetp
           (implies (and (equal (aignet-eval-conjunction x invals regvals aignet) 0)
                         (subsetp (lit-list-fix x) (lit-list-fix y)))
                    (equal (aignet-eval-conjunction y invals regvals aignet) 0))
           :hints(("Goal" :in-theory (enable aignet-eval-conjunction
                                             subsetp lit-list-fix)
                   :induct (lit-list-fix x)))))

  (defretd <fn>-implies-reached
    (implies (and subsetp
                  (obs-dom-info->reached y)
                  (not (cube-contradictionp (obs-dom-info->doms y)))
                  )
             (obs-dom-info->reached x)))

  (defretd <fn>-implies-member
    (implies (and subsetp
                  (obs-dom-info->reached y)
                  (not (cube-contradictionp (obs-dom-info->doms y)))
                  (not (member-equal lit (obs-dom-info->doms y))))
             (not (member lit (obs-dom-info->doms x))))))



(define obs-dom-info-add-lits ((lits lit-listp) (x obs-dom-info-p))
  :returns (new obs-dom-info-p)
  (b* (((obs-dom-info x)))
    (if x.reached
        (make-obs-dom-info-reached (set::union (set::mergesort (lit-list-fix lits)) x.doms))
      (make-obs-dom-info-unreached)))
  ///

  (defret <fn>-when-unreached
    (implies (not (obs-dom-info->reached x))
             (equal new (make-obs-dom-info-unreached))))

  (defret <fn>-when-reached
    (implies (obs-dom-info->reached x)
             (obs-dom-info->reached new)))

  (defret member-of-<fn>
    (implies (obs-dom-info->reached x)
             (iff (member-equal dom (obs-dom-info->doms new))
                  (or (member-equal dom (lit-list-fix lits))
                      (member-equal dom (obs-dom-info->doms x)))))))

(define obs-dom-info-for-child ((fanout-info obs-dom-info-p)
                                (fanout natp)
                                refcounts
                                aignet)
  :guard (and (id-existsp fanout aignet)
              (eql (id->type fanout aignet) (gate-type))
              (< fanout (u32-length refcounts)))
  :returns (child-fanout-info obs-dom-info-p)
  (b* (;; (fanin0 (gate-id->fanin0 fanout aignet))
       ;; (fanin1 (gate-id->fanin1 fanout aignet))
       (xor (eql 1 (id->regp fanout aignet))))
    (if xor
        ;; Won't complicate things with this optimization since hashing should prevent this anyhow.
        ;; (if (or (eql fanin0 fanin1)
        ;;         (eql fanin0 (lit-negate fanin1)))
        ;;     (make-obs-dom-info-unreached)
        (obs-dom-info-fix fanout-info)
      ;; (cond ((eql fanin0 fanin1) (obs-dom-info-fix fanout-info))
      ;;       ((eql fanin0 (lit-negate fanin1)) (make-obs-dom-info-unreached))
      ;;       (t
      (obs-dom-info-add-lits
       (gate-node-supergate fanout refcounts aignet)
       fanout-info)))
  ///

  (defret <fn>-when-xor
    (implies (equal (stype (car (lookup-id fanout aignet))) :xor)
             (equal child-fanout-info
                    (obs-dom-info-fix fanout-info))))
  
  (defret <fn>-when-and
    (implies (equal (stype (car (lookup-id fanout aignet))) :and)
             (equal child-fanout-info
                    (obs-dom-info-add-lits (gate-node-supergate fanout refcounts aignet)
                                           fanout-info)))))


(define obs-dom-fanins-ok ((super lit-listp)
                           (parent-info obs-dom-info-p)
                           obs-dom-array)
  :guard (< (lits-max-id-val super) (dominfo-length obs-dom-array))
  (if (atom super)
      t
    (and (obs-dom-info-subsetp (get-dominfo (lit->var (car super)) obs-dom-array)
                               parent-info)
         (obs-dom-fanins-ok (cdr super) parent-info obs-dom-array)))
  ///
  (defthm obs-dom-fanins-ok-implies-member-subset
    (implies (and (obs-dom-fanins-ok super parent-info obs-dom-array)
                  (member lit super))
             (obs-dom-info-subsetp (nth (lit->var lit) obs-dom-array) parent-info)))

  (defthm obs-dom-fanins-ok-when-unreached
    (implies (not (obs-dom-info->reached parent-info))
             (obs-dom-fanins-ok super parent-info obs-dom-array))
    :hints(("Goal" :in-theory (enable obs-dom-info-subsetp)))))

(define obs-dom-fanout-ok ((fanout natp) obs-dom-array refcounts aignet)
  :guard (and (id-existsp fanout aignet)
              (<= (num-fanins aignet) (dominfo-length obs-dom-array))
              (<= (num-fanins aignet) (u32-length refcounts)))
  (or (not (eql (id->type fanout aignet) (gate-type)))
      (let* ((super (gate-node-supergate fanout refcounts aignet))
             (dominfo (get-dominfo fanout obs-dom-array)))
        (if (eql (id->regp fanout aignet) 1)
            (obs-dom-fanins-ok super dominfo obs-dom-array)
          (obs-dom-fanins-ok
           super (obs-dom-info-add-lits super dominfo) obs-dom-array))))
  ///
  (defthm obs-dom-fanout-ok-implies-xor-child
    (implies (and (obs-dom-fanout-ok fanout obs-dom-array refcounts aignet)
                  (equal (stype (car (lookup-id fanout aignet))) :xor)
                  (member lit (gate-node-supergate fanout refcounts aignet)))
             (obs-dom-info-subsetp (nth (lit->var lit) obs-dom-array)
                                   (nth fanout obs-dom-array))))

  (defthm obs-dom-fanout-ok-implies-and-child
    (implies (and (obs-dom-fanout-ok fanout obs-dom-array refcounts aignet)
                  (equal (stype (car (lookup-id fanout aignet))) :and)
                  (member lit (gate-node-supergate fanout refcounts aignet)))
             (obs-dom-info-subsetp (nth (lit->var lit) obs-dom-array)
                                   (obs-dom-info-add-lits
                                    (gate-node-supergate fanout refcounts aignet)
                                    (nth fanout obs-dom-array)))))

  (defthmd obs-dom-fanout-ok-out-of-bounds
    (implies (< (fanin-count aignet) (nfix n))
             (obs-dom-fanout-ok n obs-dom-array refcounts aignet))
    :hints(("Goal" :in-theory (enable obs-dom-fanout-ok)))))



(define cube-contradictionp-sorted ((x lit-listp))
  :guard (set::setp x)
  :enabled t
  :guard-hints (("goal" :in-theory (enable cube-contradictionp
                                           cube-contradictionp-sorted)))
  (mbe :logic (cube-contradictionp x)
       :exec
       (if (set::empty x)
           nil
         (or (set::in (lit-negate (set::head x)) (set::tail x))
             (cube-contradictionp-sorted (set::tail x))))))

(define obs-dom-info-normalize ((x obs-dom-info-p))
  :returns (new-x obs-dom-info-p)
  (b* (((obs-dom-info x)))
    (if (and x.reached
             (cube-contradictionp-sorted x.doms))
        (make-obs-dom-info-unreached)
      (obs-dom-info-fix x)))
  ///

  ;; (local (defthm cube-contradictionp-by-member
  ;;          (implies (and (member x cube)
  ;;                        (member (lit-negate x) cube)
  ;;                        (lit-listp cube))
  ;;                   (cube-contradictionp cube))
  ;;          :hints(("Goal" :in-theory (enable cube-contradictionp)))))
  
  ;; (local (defthm cube-contradictionp-when-subsetp
  ;;          (implies (and (subsetp x y)
  ;;                        (cube-contradictionp x)
  ;;                        (lit-listp y) (lit-listp x))
  ;;                   (cube-contradictionp y))
  ;;          :hints(("Goal" :in-theory (enable cube-contradictionp
  ;;                                            subsetp)))))
  
  (defret subsetp-of-<fn>-1
    (iff (obs-dom-info-subsetp new-x y)
         (obs-dom-info-subsetp x y))
    :hints(("Goal" :in-theory (enable obs-dom-info-subsetp
                                      cube-contradictionp-when-subsetp))))

  (defret subsetp-of-<fn>-2
    (iff (obs-dom-info-subsetp y new-x)
         (obs-dom-info-subsetp y x))
    :hints(("Goal" :in-theory (enable obs-dom-info-subsetp)))))

(define obs-dom-info-intersect ((x obs-dom-info-p) (y obs-dom-info-p))
  :returns (int obs-dom-info-p)
  (b* (((obs-dom-info x))
       ((obs-dom-info y)))
    (if (and x.reached (not (cube-contradictionp-sorted x.doms)))
        (if (and y.reached (not (cube-contradictionp-sorted y.doms)))
            (make-obs-dom-info-reached (set::intersect x.doms y.doms))
          (obs-dom-info-fix x))
      (obs-dom-info-normalize y)))
  ///
  (local (in-theory (enable obs-dom-info-subsetp
                            obs-dom-info-normalize)))
  
  (local (defthm subsetp-of-intersect-1
           (subsetp (intersection$ x y) x)))
  (local (defthm subsetp-of-intersect-2
           (subsetp (intersection$ x y) y)))
  (local (defthm lit-negate-by-equal-lit-negate
           (implies (equal (lit-negate x) (lit-fix y))
                    (equal (lit-negate y) (lit-fix x)))))
  (local (defthm cube-contradictionp-implies-not-member
           (implies (and (not (cube-contradictionp y))
                         (member-equal (lit-negate x) (lit-list-fix y)))
                    (not (member-equal (lit-fix x) (lit-list-fix y))))
           :hints(("Goal" :in-theory (enable cube-contradictionp lit-list-fix)))))
  (local (defthm cube-contradiction-by-subsetp
           (implies (and (subsetp (lit-list-fix x) (lit-list-fix y))
                         (not (cube-contradictionp y)))
                    (not (cube-contradictionp x)))
           :hints(("Goal" :in-theory (enable cube-contradictionp lit-list-fix)
                   :induct (lit-list-fix x)))))

  (local (defthm cube-contradiction-by-subsetp-lits
           (implies (and (subsetp x y)
                         (lit-listp x) (lit-listp y)
                         (not (cube-contradictionp y)))
                    (not (cube-contradictionp x)))
           :hints (("goal" :use ((:instance cube-contradiction-by-subsetp))
                    :in-theory (disable cube-contradiction-by-subsetp)))))
  
  (defret obs-dom-info-subsetp-of-obs-dom-info-intersect-1
    (obs-dom-info-subsetp int x))

  (defret obs-dom-info-subsetp-of-obs-dom-info-intersect-2
    (obs-dom-info-subsetp int y))

  (defret obs-dom-info-intersect-preserves-obs-dom-info-subsetp-1
    (implies (obs-dom-info-subsetp x z)
             (obs-dom-info-subsetp int z)))
  
  (defret obs-dom-info-intersect-preserves-obs-dom-info-subsetp-2
    (implies (obs-dom-info-subsetp y z)
             (obs-dom-info-subsetp int z)))

  (local (defthm cube-contradictionp-of-intersect
           (implies (and (not (cube-contradictionp x))
                         (set::setp x))
                    (not (cube-contradictionp (set::intersect x y))))
           :hints(("Goal" :use ((:instance cube-contradictionp-when-subsetp
                                 (x (set::intersect x y))
                                 (y x)))))))
  
  (defret obs-dom-info-intersect-idempotent
    (equal (obs-dom-info-intersect (obs-dom-info-intersect x y) y)
           (obs-dom-info-intersect x y))))

(define lit-list-vars ((x lit-listp))
  :returns (vars nat-listp)
  (if (atom x)
      nil
    (cons (lit->var (car x))
          (lit-list-vars (cdr x)))))


(define obs-dom-info-store-intersections ((super lit-listp)
                                          (dominfo obs-dom-info-p)
                                          (obs-dom-array))
  :guard (< (lits-max-id-val super) (dominfo-length obs-dom-array))
  :returns (new-obs-dom-array)
  (b* (((when (atom super)) obs-dom-array)
       (var (lit->var (car super)))
       (obs-dom-array
        (set-dominfo var
                     (obs-dom-info-intersect
                      (get-dominfo var obs-dom-array)
                      dominfo)
                     obs-dom-array)))
    (obs-dom-info-store-intersections (cdr super) dominfo obs-dom-array))
  ///
  (defret <fn>-length
    (implies (< (lits-max-id-val super) (len obs-dom-array))
             (equal (len new-obs-dom-array)
                    (len obs-dom-array))))

  (defret <fn>-index
    (equal (nth i new-obs-dom-array)
           (if (member-equal (nfix i) (lit-list-vars super))
               (obs-dom-info-intersect (nth i obs-dom-array) dominfo)
             (nth i obs-dom-array)))
    :hints(("Goal" :in-theory (enable lit-list-vars))))

  (defret obs-dom-fanins-ok-of-obs-dom-info-store-intersections
    (implies (obs-dom-fanins-ok lits fanout-dominfo obs-dom-array)
             (obs-dom-fanins-ok lits fanout-dominfo new-obs-dom-array))
    :hints (("goal" :in-theory (enable obs-dom-fanins-ok)
             :induct (obs-dom-fanins-ok lits fanout-dominfo obs-dom-array))))

  (defret obs-dom-fanins-ok-of-obs-dom-info-store-intersections
    (implies (obs-dom-fanins-ok lits fanout-dominfo obs-dom-array)
             (obs-dom-fanins-ok lits fanout-dominfo new-obs-dom-array))
    :hints (("goal" :in-theory (enable obs-dom-fanins-ok)
             :induct (obs-dom-fanins-ok lits fanout-dominfo obs-dom-array))))

  (local (defthm member-lit->var-of-lit-list-vars
           (implies (member k x)
                    (member (lit->var k) (lit-list-vars x)))
           :hints(("Goal" :in-theory (enable member lit-list-vars)))))
  
  (defret obs-dom-fanins-ok-of-obs-dom-info-store-intersections-self
    (implies (subsetp-equal lits super)
             (obs-dom-fanins-ok lits dominfo new-obs-dom-array))
    :hints (("goal" :in-theory (enable obs-dom-fanins-ok subsetp-equal)
             :induct (subsetp-equal lits super)))))



(define obs-dom-info-sweep-node ((n natp) obs-dom-array refcounts aignet)
  :guard (and (id-existsp n aignet)
              (< n (dominfo-length obs-dom-array))
              (< n (u32-length refcounts)))
  :returns new-obs-dom-array
  (b* ((slot0 (id->slot n 0 aignet))
       (type (snode->type slot0)))
    (aignet-case
      type
      :gate (b* ((dominfo (get-dominfo n obs-dom-array))
                 ((unless (obs-dom-info->reached dominfo))
                  obs-dom-array)
                 (super (gate-node-supergate n refcounts aignet))
                 (xor (eql (id->regp n aignet) 1))
                 (child-dominfo (if xor dominfo (obs-dom-info-add-lits super dominfo))))
              (obs-dom-info-store-intersections
               super child-dominfo obs-dom-array))
      :otherwise obs-dom-array))
  ///
  (defret <fn>-length
    (implies (< (nfix n) (len obs-dom-array))
             (equal (len new-obs-dom-array)
                    (len obs-dom-array))))

  (local (defthm member-lit-list-vars-when-lits-max-id-val
           (implies (< (lits-max-id-val lits) i)
                    (not (member-equal i (lit-list-vars lits))))
           :hints(("Goal" :in-theory (enable lits-max-id-val lit-list-vars)))))
  
  (defret <fn>-preserves-correct
    (implies (and (< (nfix n) (nfix i))
                  (obs-dom-fanout-ok i obs-dom-array refcounts aignet))
             (obs-dom-fanout-ok i new-obs-dom-array refcounts aignet))
    :hints(("Goal" :in-theory (enable obs-dom-fanout-ok)
            :do-not-induct t))
    :otf-flg t)

  (defret <fn>-sets-correct
    (obs-dom-fanout-ok n new-obs-dom-array refcounts aignet)
    :hints(("Goal" :in-theory (enable obs-dom-fanout-ok)
            :do-not-induct t)))

  ;; (local (defthm intersection-with-nil
  ;;          (equal (intersection-equal x nil) nil)
  ;;          :hints(("Goal" :in-theory (enable intersection-equal)))))
  (local (defthm intersect-with-nil
           (equal (set::intersect nil x) nil)
           :hints(("Goal" :use ((:instance set::double-containment
                                 (x (set::intersect nil x)) (y nil)))))))
  
  (defret <fn>-preserves-empty-dominators
    (implies (equal (nth i obs-dom-array)
                    (make-obs-dom-info-reached nil))
             (equal (nth i new-obs-dom-array)
                    (make-obs-dom-info-reached nil)))
    :hints(("Goal" :in-theory (enable obs-dom-info-intersect)))))


(define obs-dom-info-sweep-nodes ((n natp) obs-dom-array refcounts aignet)
  :guard (and (<= n (num-fanins aignet))
              (<= n (dominfo-length obs-dom-array))
              (<= n (u32-length refcounts)))
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  :returns new-obs-dom-array
  (b* (((when (zp n))
        obs-dom-array)
       (obs-dom-array (obs-dom-info-sweep-node (1- n) obs-dom-array refcounts aignet)))
    (obs-dom-info-sweep-nodes (1- n) obs-dom-array refcounts aignet))
  ///
  (defret <fn>-length
    (implies (<= (nfix n) (len obs-dom-array))
             (equal (len new-obs-dom-array)
                    (len obs-dom-array))))

  (defret <fn>-preserves-correct
    (implies (and (<= (nfix n) (nfix i))
                  (obs-dom-fanout-ok i obs-dom-array refcounts aignet))
             (obs-dom-fanout-ok i new-obs-dom-array refcounts aignet)))

  (defret <fn>-sets-correct
    (implies (< (nfix i) (nfix n))
             (obs-dom-fanout-ok i new-obs-dom-array refcounts aignet)))
  
  (defret <fn>-preserves-empty-dominators
    (implies (equal (nth i obs-dom-array)
                    (make-obs-dom-info-reached nil))
             (equal (nth i new-obs-dom-array)
                    (make-obs-dom-info-reached nil)))
    :hints(("Goal" :in-theory (enable obs-dom-info-intersect)))))


(define obs-dom-info-set-pos ((n natp) obs-dom-array aignet)
  :guard (and (<= n (num-outs aignet))
              (<= (num-fanins aignet) (dominfo-length obs-dom-array)))
  :measure (nfix (- (num-outs aignet) (nfix n)))
  :returns new-obs-dom-array
  (b* (((when (mbe :logic (zp (- (num-outs aignet) (nfix n)))
                   :exec (eql n (num-outs aignet))))
        obs-dom-array)
       (fanin-node (lit->var (outnum->fanin n aignet)))
       (obs-dom-array (set-dominfo fanin-node (make-obs-dom-info-reached nil) obs-dom-array)))
    (obs-dom-info-set-pos (1+ (lnfix n)) obs-dom-array aignet))
  ///
  (defret <fn>-length
    (implies (< (fanin-count aignet) (len obs-dom-array))
             (equal (len new-obs-dom-array)
                    (len obs-dom-array))))

  (defret <fn>-preserves-empty-dominators
    (implies (equal (nth i obs-dom-array)
                    (make-obs-dom-info-reached nil))
             (equal (nth i new-obs-dom-array)
                    (make-obs-dom-info-reached nil))))

  (defret fanin-dominfo-of-<fn>
    (implies (and (<= (nfix n) (nfix k))
                  (< (nfix k) (num-outs aignet)))
             (equal (nth (lit->var (fanin 0 (lookup-stype k :po aignet))) new-obs-dom-array)
                    (make-obs-dom-info-reached nil)))))

(define obs-dom-info-set-nxsts ((n natp) obs-dom-array aignet)
  :guard (and (<= n (num-regs aignet))
              (<= (num-fanins aignet) (dominfo-length obs-dom-array)))
  :measure (nfix (- (num-regs aignet) (nfix n)))
  :returns new-obs-dom-array
  (b* (((when (mbe :logic (zp (- (num-regs aignet) (nfix n)))
                   :exec (eql n (num-regs aignet))))
        obs-dom-array)
       (fanin-node (lit->var (regnum->nxst n aignet)))
       (obs-dom-array (set-dominfo fanin-node (make-obs-dom-info-reached nil) obs-dom-array)))
    (obs-dom-info-set-nxsts (1+ (lnfix n)) obs-dom-array aignet))
  ///
  (defret <fn>-length
    (implies (< (fanin-count aignet) (len obs-dom-array))
             (equal (len new-obs-dom-array)
                    (len obs-dom-array))))

  (defret <fn>-preserves-empty-dominators
    (implies (equal (nth i obs-dom-array)
                    (make-obs-dom-info-reached nil))
             (equal (nth i new-obs-dom-array)
                    (make-obs-dom-info-reached nil))))

  (defret fanin-dominfo-of-<fn>
    (implies (and (<= (nfix n) (nfix k))
                  (< (nfix k) (num-regs aignet)))
             (equal (nth (lit->var (lookup-reg->nxst k aignet)) new-obs-dom-array)
                    (make-obs-dom-info-reached nil)))))


(define aignet-compute-obs-dom-info (obs-dom-array refcounts aignet)
  :returns new-obs-dom-array
  :guard (<= (num-fanins aignet) (u32-length refcounts))
  (b* ((obs-dom-array (resize-dominfo 0 obs-dom-array))
       (obs-dom-array (resize-dominfo (num-fanins aignet) obs-dom-array))
       (obs-dom-array (obs-dom-info-set-pos 0 obs-dom-array aignet))
       (obs-dom-array (obs-dom-info-set-nxsts 0 obs-dom-array aignet)))
    (obs-dom-info-sweep-nodes (num-fanins aignet) obs-dom-array refcounts aignet))
  ///
  (defret <fn>-length
    (equal (len new-obs-dom-array) (num-fanins aignet)))

  (defret po-dominfo-of-<fn>
    (implies (< (nfix k) (num-outs aignet))
             (equal (nth (lit->var (fanin 0 (lookup-stype k :po aignet))) new-obs-dom-array)
                    (make-obs-dom-info-reached nil))))

  (defret nxst-dominfo-of-<fn>
    (implies (< (nfix k) (num-regs aignet))
             (equal (nth (lit->var (lookup-reg->nxst k aignet)) new-obs-dom-array)
                    (make-obs-dom-info-reached nil))))

  (defret <fn>-fanouts-ok
    (obs-dom-fanout-ok i new-obs-dom-array refcounts aignet)
    :hints(("Goal" :in-theory (enable obs-dom-fanout-ok-out-of-bounds)
            :cases ((< (nfix i) (+ 1 (fanin-count aignet))))))))



(defsection obs-dom-array-correct
  
  (defun-sk obs-dom-array-correct (obs-dom-array refcounts aignet)
    (forall fanout
            (obs-dom-fanout-ok fanout obs-dom-array refcounts aignet))
    :rewrite :direct)

  (in-theory (disable obs-dom-array-correct))

  (defthm obs-dom-array-correct-of-obs-dom-info-sweep-nodes
    (obs-dom-array-correct
     (obs-dom-info-sweep-nodes (+ 1 (fanin-count aignet)) obs-dom-array refcounts aignet)
     refcounts
     aignet)
    :hints(("Goal" :in-theory (enable obs-dom-array-correct
                                      obs-dom-fanout-ok-out-of-bounds)
            :cases ((<= (nfix
                         (obs-dom-array-correct-witness
                          (obs-dom-info-sweep-nodes (+ 1 (fanin-count aignet)) 
                                                    obs-dom-array refcounts aignet)
                          refcounts
                          aignet))
                        (fanin-count aignet))))))

  (defthm obs-dom-array-correct-of-aignet-compute-obs-dom-info
    (obs-dom-array-correct (aignet-compute-obs-dom-info obs-dom-array refcounts aignet)
                           refcounts aignet)
    :hints(("Goal" :in-theory (enable obs-dom-array-correct)))))





(define spath-last ((x nat-listp))
  :guard (consp x)
  :returns (last natp :rule-classes :type-prescription)
  (lnfix (car (last x))))

(define spath-butlast ((x nat-listp))
  :guard (consp x)
  :returns (prefix nat-listp)
  (acl2::nat-list-fix (butlast x 1))
  ///
  (defret len-of-<fn>
    (implies (consp x)
             (equal (len prefix) (+ -1 (len x)))))
  
  (defret spath-exists-of-spath-butlast
    (implies (spath-existsp sink x refcounts aignet)
             (spath-existsp sink prefix refcounts aignet))
    :hints(("Goal" :in-theory (enable spath-existsp))))

  (local (defthm len-equal-0
           (equal (equal (len x) 0)
                  (not (consp x)))))

  (local (in-theory (disable satlink::equal-of-lit-fix-backchain)))

  (defthmd spath-endpoint-in-terms-of-butlast
    (equal (spath-endpoint sink path refcounts aignet)
           (if (atom path)
               (nfix sink)
             (b* ((prev (spath-endpoint sink (spath-butlast path) refcounts aignet))
                  (last (spath-last path)))
               (lit->var (nth last (gate-node-supergate prev refcounts aignet))))))
    :hints(("Goal" :in-theory (enable spath-last (:i spath-endpoint))
            :induct (spath-endpoint sink path refcounts aignet)
            :expand ((:free (path) (spath-endpoint sink path refcounts aignet)))))
    :rule-classes ((:definition :controller-alist ((spath-endpoint nil t nil nil)))))

    (defthmd spath-existsp-in-terms-of-butlast
      (equal (spath-existsp sink path refcounts aignet)
             (if (atom path)
                 t
               (and (spath-existsp sink (spath-butlast path) refcounts aignet)
                    (b* ((prev (spath-endpoint sink (spath-butlast path) refcounts aignet)))
                      (and (equal (ctype (stype (car (lookup-id prev aignet))))
                                  :gate)
                           (< (spath-last path) (len (gate-node-supergate prev refcounts aignet))))))))
      :hints(("Goal" :in-theory (enable spath-endpoint spath-existsp spath-last)
              :induct (spath-endpoint sink path refcounts aignet)
              :expand ((:with spath-endpoint (:free (path) (spath-endpoint sink path refcounts aignet)))
                       (:free (path) (spath-existsp sink path refcounts aignet)))))
      :rule-classes ((:definition :controller-alist ((spath-existsp nil t nil nil)))))

    (defthmd spath-and-literals-in-terms-of-butlast
      (equal (spath-and-literals sink path refcounts aignet)
             (if (atom path)
                 nil
               (append (spath-and-literals sink (spath-butlast path) refcounts aignet)
                       (b* ((prev (spath-endpoint sink (spath-butlast path) refcounts aignet)))
                         (and (equal (stype (car (lookup-id prev aignet))) :and)
                              (gate-node-supergate prev refcounts aignet))))))
    :hints(("Goal" :in-theory (enable spath-last (:i spath-endpoint))
            :induct (spath-endpoint sink path refcounts aignet)
            :expand ((:with spath-endpoint (:free (path) (spath-endpoint sink path refcounts aignet)))
                     (:free (path) (spath-and-literals sink path refcounts aignet)))))
    :rule-classes ((:definition :controller-alist ((spath-and-literals nil t nil nil))))))



(defsection obs-dom-array-implies-path-contains-dominators
  (local
   (progn
     (define spath-induct-reverse ((x nat-listp))
       :measure (len x)
       (if (atom x)
           (acl2::nat-list-fix x)
         (spath-induct-reverse (spath-butlast x))))

     ;; (defthm path-contains-and-siblings-implies-not-cube-contradictionp
     ;;   (implies (and (path-contains-and-siblings
     ;;                  lits sink path aignet)
     ;;                 (not (path-contains-contradictory-siblings
     ;;                       sink path aignet)))
     ;;            (not (cube-contradictionp lits)))
     ;;   :hints (("Goal" :use ((:instance path-contains-and-siblings-implies-member
     ;;                          (lit (cube-contradictionp lits))
     ;;                          (x (lit-list-fix lits)))
     ;;                         (:instance path-contains-and-siblings-implies-member
     ;;                          (lit (lit-negate (cube-contradictionp lits)))
     ;;                          (x (lit-list-fix lits))))
     ;;            :in-theory (disable path-contains-and-siblings-implies-member))))

     ;; (defthm path-contains-and-siblings-implies-not-member
     ;;   (implies (and (path-contains-and-siblings
     ;;                  lits sink path aignet)
     ;;                 (not (path-contains-and-sibling lit sink path aignet))
     ;;                 (litp lit) (lit-listp lits))
     ;;            (not (member lit lits)))
     ;;   :hints(("Goal" :in-theory (enable member path-contains-and-siblings))))


     (defthm obs-dom-fanout-ok-implies-reachable-and
       (implies (and (obs-dom-fanout-ok fanout obs-dom-array refcounts aignet)
                     (equal (stype (car (lookup-id fanout aignet))) :and)
                     (obs-dom-info->reached (nth fanout obs-dom-array))
                     (not (cube-contradictionp
                           (obs-dom-info->doms (nth fanout obs-dom-array))))
                     (not (cube-contradictionp (gate-node-supergate fanout refcounts aignet)))
                     (not (two-cubes-contradictionp
                           (obs-dom-info->doms (nth fanout obs-dom-array))
                           (gate-node-supergate fanout refcounts aignet)))
                     (< (nfix k) (len (gate-node-supergate fanout refcounts aignet))))
                (obs-dom-info->reached (nth (lit->var
                                             (nth k (gate-node-supergate fanout refcounts aignet)))
                                            obs-dom-array)))
       :hints(("Goal" :in-theory (e/d (obs-dom-info-for-child
                                       obs-dom-info-add-lits
                                       obs-dom-info-subsetp
                                       cube-contradictionp-of-append)
                                      (obs-dom-fanout-ok-implies-and-child))
               :expand ((:free (a b) (cube-contradictionp (cons a b))))
               :use ((:instance obs-dom-fanout-ok-implies-and-child
                      (lit (nth k (gate-node-supergate fanout refcounts aignet))))))))

     (defthm obs-dom-fanout-ok-implies-reachable-xor
       (implies (and (obs-dom-fanout-ok fanout obs-dom-array refcounts aignet)
                     (equal (stype (car (lookup-id fanout aignet))) :xor)
                     (obs-dom-info->reached (nth fanout obs-dom-array))
                     (not (cube-contradictionp
                           (obs-dom-info->doms (nth fanout obs-dom-array))))
                     (< (nfix k) (len (gate-node-supergate fanout refcounts aignet)))
                     ;; (not (member-equal
                     ;;       (lit-negate (fanin (b-not dir)
                     ;;                          (lookup-id fanout aignet)))
                     ;;       (obs-dom-info->doms (nth fanout obs-dom-array))))
                     )
                (obs-dom-info->reached (nth (lit->var
                                             (nth k (gate-node-supergate fanout refcounts aignet)))
                                            obs-dom-array)))
       :hints(("Goal" :in-theory (e/d (obs-dom-info-for-child
                                       obs-dom-info-add-lits
                                       obs-dom-info-subsetp
                                       cube-contradictionp-of-append)
                                      (obs-dom-fanout-ok-implies-xor-child))
               :expand ((:free (a b) (cube-contradictionp (cons a b))))
               :use ((:instance obs-dom-fanout-ok-implies-xor-child
                      (lit (nth k (gate-node-supergate fanout refcounts aignet))))))))



     (defthm subsetp-of-doms-when-reached
       (implies (and (obs-dom-info-subsetp x y)
                     (obs-dom-info->reached y)
                     (not (cube-contradictionp
                           (obs-dom-info->doms y))))
                (subsetp (obs-dom-info->doms x) (obs-dom-info->doms y)))
       :hints(("Goal" :in-theory (enable obs-dom-info-subsetp))))

     ;; (defthm path-contains-and-siblings-when-subsetp
     ;;   (implies (and (path-contains-and-siblings x sink path aignet)
     ;;                 (subsetp y x))
     ;;            (path-contains-and-siblings y sink path aignet))
     ;;   :hints(("Goal" :in-theory (enable path-contains-and-siblings subsetp)
     ;;           :induct (path-contains-and-siblings y sink path aignet)
     ;;           :expand ((path-contains-and-siblings y sink path aignet)
     ;;                    (subsetp y x)))))


     (defthm obs-dom-fanout-ok-implies-subsetp-xor
       (implies (and (obs-dom-fanout-ok fanout obs-dom-array refcounts aignet)
                     (equal (stype (car (lookup-id fanout aignet))) :xor)
                     (obs-dom-info->reached (nth fanout obs-dom-array))
                     (not (cube-contradictionp
                           (obs-dom-info->doms (nth fanout obs-dom-array))))
                     (< (nfix k) (len (gate-node-supergate fanout refcounts aignet))))
                (subsetp (obs-dom-info->doms
                          (nth (lit->var
                                (nth k (gate-node-supergate fanout refcounts aignet)))
                               obs-dom-array))
                         (obs-dom-info->doms
                          (nth fanout obs-dom-array))))
       :hints (("goal" :use ((:instance obs-dom-fanout-ok-implies-xor-child
                              (lit (nth k (gate-node-supergate fanout refcounts aignet)))))
                :in-theory (e/d (obs-dom-info-for-child)
                                (obs-dom-fanout-ok-implies-xor-child)))))

     (defthm obs-dom-fanout-ok-implies-subsetp-and
       (implies (and (obs-dom-fanout-ok fanout obs-dom-array refcounts aignet)
                     (equal (stype (car (lookup-id fanout aignet))) :and)
                     (obs-dom-info->reached (nth fanout obs-dom-array))
                     (not (cube-contradictionp
                           (obs-dom-info->doms (nth fanout obs-dom-array))))
                     (not (cube-contradictionp (gate-node-supergate fanout refcounts aignet)))
                     (not (two-cubes-contradictionp
                           (obs-dom-info->doms (nth fanout obs-dom-array))
                           (gate-node-supergate fanout refcounts aignet)))
                     (< (nfix k) (len (gate-node-supergate fanout refcounts aignet))))
                (subsetp (obs-dom-info->doms
                          (nth (lit->var
                                (nth k (gate-node-supergate fanout refcounts aignet)))
                               obs-dom-array))
                         (append (obs-dom-info->doms (nth fanout obs-dom-array))
                                 (gate-node-supergate fanout refcounts aignet))))
       :hints(("Goal" :in-theory (e/d (obs-dom-info-for-child
                                       obs-dom-info-add-lits
                                       obs-dom-info-subsetp
                                       cube-contradictionp-of-append)
                                      (obs-dom-fanout-ok-implies-and-child))
               :expand ((:free (a b) (cube-contradictionp (cons a b))))
               :use ((:instance obs-dom-fanout-ok-implies-and-child
                      (lit (nth k (gate-node-supergate fanout refcounts aignet))))))))

     (defthm obs-dom-fanout-ok-implies-subsetp-and-rw
       (implies (and (obs-dom-fanout-ok fanout obs-dom-array refcounts aignet)
                     (equal (stype (car (lookup-id fanout aignet))) :and)
                     (obs-dom-info->reached (nth fanout obs-dom-array))
                     (not (cube-contradictionp
                           (obs-dom-info->doms (nth fanout obs-dom-array))))
                     (not (cube-contradictionp (gate-node-supergate fanout refcounts aignet)))
                     (not (two-cubes-contradictionp
                           (obs-dom-info->doms (nth fanout obs-dom-array))
                           (gate-node-supergate fanout refcounts aignet)))
                     (< (nfix k) (len (gate-node-supergate fanout refcounts aignet)))
                     (subsetp
                      (append (obs-dom-info->doms (nth fanout obs-dom-array))
                              (gate-node-supergate fanout refcounts aignet))
                      full-set))
                (subsetp (obs-dom-info->doms
                          (nth (lit->var
                                (nth k (gate-node-supergate fanout refcounts aignet)))
                               obs-dom-array))
                         full-set))
       :hints (("goal" :use obs-dom-fanout-ok-implies-subsetp-and
                :in-theory (disable obs-dom-fanout-ok-implies-subsetp-and))))
     ))
     ;; (defthm subsetp-remove-equal
     ;;   (implies (subsetp x (cons k y))
     ;;            (subsetp (remove k x) y))
     ;;   :hints(("Goal" :in-theory (enable subsetp remove))))

  (local
   (defthm not-cube-contradictionp-when-subsetp
     (implies (and (subsetp-equal x y)
                   (not (cube-contradictionp y)))
              (not (cube-contradictionp x)))
     :hints(("Goal" :in-theory (enable cube-contradictionp-when-subsetp)))))

  (local
   (defthm not-two-cubes-contradictionp-when-subsetp
     (implies (and (subsetp-equal x y)
                   (not (two-cubes-contradictionp y z)))
              (not (two-cubes-contradictionp x z)))))

  (defthm obs-dom-array-implies-path-contains-dominators
    (b* ((path-lits (spath-and-literals sink path refcounts aignet)))
      (implies (and (obs-dom-array-correct obs-dom-array refcounts aignet)
                    (spath-existsp sink path refcounts aignet)
                    (not (cube-contradictionp path-lits))
                    (obs-dom-info->reached (nth sink obs-dom-array))
                    (equal (obs-dom-info->doms (nth sink obs-dom-array)) nil))
               (let ((source (spath-endpoint sink path refcounts aignet)))
                 (and (obs-dom-info->reached (nth source obs-dom-array))
                      (subsetp
                       (obs-dom-info->doms (nth source obs-dom-array)) path-lits)))))
    :hints (("goal" :induct (spath-induct-reverse path)
             :in-theory (enable (:i spath-induct-reverse)
                                cube-contradictionp-of-append
                                cube-contradictionp-when-subsetp)
             :expand ((:with spath-and-literals-in-terms-of-butlast
                       (spath-and-literals sink path refcounts aignet))
                      (:with spath-existsp-in-terms-of-butlast
                       (spath-existsp sink path refcounts aignet))
                      (:with spath-endpoint-in-terms-of-butlast
                       (spath-endpoint sink path refcounts aignet))))
            (and stable-under-simplificationp
                 ))))



(defthm toggle-does-not-affect-sink-when-not-reached
  (implies (and (obs-dom-array-correct obs-dom-array refcounts aignet)
                (not (obs-dom-info->reached (nth source obs-dom-array)))
                (obs-dom-info->reached (nth sink obs-dom-array))
                (equal (obs-dom-info->doms (nth sink obs-dom-array)) nil)
                (< 1 (nfix (nth source refcounts))))
           (equal (id-eval-toggle sink source invals regvals aignet)
                  (id-eval sink invals regvals aignet)))
  :hints (("goal" :use ((:instance obs-dom-array-implies-path-contains-dominators
                         (path (toggle-witness-spath sink source invals regvals refcounts aignet))))
           :in-theory (disable obs-dom-array-implies-path-contains-dominators))))



(defthm toggle-does-not-affect-output-when-dominator-false
  (implies (and (obs-dom-array-correct obs-dom-array refcounts aignet)
                (member-equal lit (obs-dom-info->doms (nth source obs-dom-array)))
                (equal (lit-eval lit invals regvals aignet) 0)
                (equal (lit-eval-toggle lit source invals regvals aignet) 0)
                (obs-dom-info->reached (nth sink obs-dom-array))
                (equal (obs-dom-info->doms (nth sink obs-dom-array)) nil)
                (< 1 (nfix (nth source refcounts))))
           (equal (id-eval-toggle sink source invals regvals aignet)
                  (id-eval sink invals regvals aignet)))
  :hints (("goal" :use ((:instance obs-dom-array-implies-path-contains-dominators
                         (path (toggle-witness-spath sink source invals regvals refcounts aignet)))
                        (:instance lit-list-has-const0-under-toggle-when-member
                         (x (spath-and-literals
                             sink
                             (toggle-witness-spath sink source invals regvals refcounts aignet)
                             refcounts aignet))
                         (toggle source)))
           :in-theory (disable obs-dom-array-implies-path-contains-dominators
                               lit-list-has-const0-under-toggle-when-member))))
