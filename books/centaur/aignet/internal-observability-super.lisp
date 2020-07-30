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
(include-book "std/util/termhints" :dir :system)
(include-book "prune") ;; for aignet-copy-dfs-outs, aignet-copy-dfs-nxsts

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


(define aignet-eval-conjunction-toggle ((lits lit-listp) (toggles nat-listp)
                                        invals regvals aignet)
  :guard (and (aignet-lit-listp lits aignet)
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  :returns (res bitp)
  (if (atom lits)
      1
    (acl2::b-and (lit-eval-toggle (car lits) toggles invals regvals aignet)
                 (aignet-eval-conjunction-toggle (cdr lits) toggles invals regvals aignet)))
  ///
  (defcong acl2::set-equiv equal (aignet-eval-conjunction-toggle lits toggles invals regvals aignet) 2))

(define ids-multiply-referenced ((ids nat-listp) refcounts)
  (if (atom ids)
      t
    (and (mbe :logic (non-exec (< 1 (nfix (nth (car ids) refcounts))))
              :exec (and (< (car ids) (u32-length refcounts))
                         (< 1 (get-u32 (car ids) refcounts))))
         (ids-multiply-referenced (cdr ids) refcounts)))
  ///
  (defthmd refcounts-greater-when-multiply-referenced
    (implies (and (ids-multiply-referenced ids refcounts)
                  (member-equal (nfix id) (acl2::nat-list-fix ids)))
             (< 1 (nfix (nth id refcounts))))))

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
    (implies (and (ids-multiply-referenced toggles aignet-refcounts)
                  (not use-muxes)
                  ;; (or (not top)
                  ;;     (not (member-equal (lit->var lit) (acl2::nat-list-fix toggles))))
                  )
             (equal (aignet-eval-conjunction-toggle res toggles invals regvals aignet)
                    (acl2::b-and (b-xor (bool->bit (and top
                                                        (equal (lit->neg lit) 0)
                                                        (posp limit)
                                                        (equal (stype (car (lookup-id (lit->var lit) aignet))) :and)
                                                        (aignet-litp lit aignet)
                                                        (member-equal (lit->var lit)
                                                                      (acl2::nat-list-fix toggles))))
                                        (lit-eval-toggle lit toggles invals regvals aignet))
                                 (aignet-eval-conjunction-toggle supergate toggles invals regvals aignet))))
    :hints (("goal" :induct <call>
             :do-not-induct t
             :in-theory (e/d (eval-and-of-lits-toggle
                              (:i <fn>)
                              refcounts-greater-when-multiply-referenced)
                             ((:definition lit-collect-supergate)))
             :expand ((:free (top use-muxes) <call>)))
            (and stable-under-simplificationp
                 '(:expand ((lit-eval-toggle lit toggles invals regvals aignet)
                            (id-eval-toggle (lit-id lit) toggles invals regvals aignet)
                            (:free (a b)
                             (aignet-eval-conjunction-toggle (cons a b) toggles invals regvals aignet))))))
    :fn lit-collect-supergate))

(define aignet-eval-parity-toggle ((lits lit-listp) (toggles nat-listp) invals regvals aignet)
  :guard (and (aignet-lit-listp lits aignet)
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  :returns (res bitp)
  (if (atom lits)
      0
    (b-xor (lit-eval-toggle (car lits) toggles invals regvals aignet)
           (aignet-eval-parity-toggle (cdr lits) toggles invals regvals aignet))))


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
     (defthm b-xor-b-not-2
       (equal (acl2::b-xor a (b-not b)) (b-not (acl2::b-xor a b)))
       :hints(("Goal" :in-theory (enable acl2::b-xor))))

     (in-theory (disable acl2::nth-when-too-large-cheap))))

  (defret eval-parity-toggle-of-lit-collect-superxor
    (implies (and (ids-multiply-referenced toggles aignet-refcounts)
                  ;; (or (not top)
                  ;;     (not (member-equal (lit->var lit) (acl2::nat-list-fix toggles))))
                  )
             (equal (aignet-eval-parity-toggle res toggles invals regvals aignet)
                    (acl2::b-xor 
                     (bool->bit (and top
                                     (equal (lit->neg lit) 0)
                                     (posp limit)
                                     (equal (stype (car (lookup-id (lit->var lit) aignet))) :xor)
                                     (aignet-litp lit aignet)
                                     (member-equal (lit->var lit)
                                                   (acl2::nat-list-fix toggles))))
                     (acl2::b-xor
                      (lit-eval-toggle lit toggles invals regvals aignet)
                      (aignet-eval-parity-toggle superxor toggles invals regvals aignet)))))
    :hints (("goal" :induct <call>
             :do-not-induct t
             :in-theory (e/d (eval-xor-of-lits-toggle
                              (:i <fn>)
                              refcounts-greater-when-multiply-referenced)
                             ((:definition lit-collect-superxor)))
             :expand ((:free (top use-muxes) <call>)))
            (and stable-under-simplificationp
                 '(:expand ((lit-eval-toggle lit toggles invals regvals aignet)
                            (id-eval-toggle (lit-id lit) toggles invals regvals aignet)
                            (:free (a b)
                             (aignet-eval-parity-toggle (cons a b) toggles invals regvals aignet))))))
    :fn lit-collect-superxor))


(define lit-list-has-const0-under-toggle ((x lit-listp)
                                          (toggle natp)
                                          (toggles nat-listp)
                                          invals regvals aignet)
  :guard (and (aignet-lit-listp x aignet)
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  (if (atom x)
      nil
    (or (and (eql (lit-eval-toggle (car x) (cons toggle toggles) invals regvals aignet) 0)
             (eql (lit-eval-toggle (car x) toggles invals regvals aignet) 0))
        (lit-list-has-const0-under-toggle (cdr x) toggle toggles invals regvals aignet)))
  ///
  (defthm lit-list-has-const0-under-toggle-of-append
    (equal (lit-list-has-const0-under-toggle (append x y) toggle toggles invals regvals aignet)
           (or (lit-list-has-const0-under-toggle x toggle toggles invals regvals aignet)
               (lit-list-has-const0-under-toggle y toggle toggles invals regvals aignet))))

  (defthm lit-list-has-const0-under-toggle-of-nil
    (not (lit-list-has-const0-under-toggle nil toggle toggles invals regvals aignet)))

  (defthmd aignet-eval-conjunction-when-lit-list-has-const0-under-toggle
    (implies (lit-list-has-const0-under-toggle x toggle toggles invals regvals aignet)
             (equal (aignet-eval-conjunction-toggle x toggles invals regvals aignet) 0))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction-toggle))))

  (defthmd aignet-eval-conjunction-toggle-when-lit-list-has-const0-under-toggle
    (implies (lit-list-has-const0-under-toggle x toggle toggles invals regvals aignet)
             (equal (aignet-eval-conjunction-toggle x (cons toggle toggles) invals regvals aignet) 0))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction-toggle))))

  (defthm lit-list-has-const0-under-toggle-of-and-supergate
    (implies (and (equal (stype (car (lookup-id sink aignet))) :and)
                  (not (equal (id-eval-toggle sink toggles invals regvals aignet)
                              (id-eval-toggle sink (cons toggle toggles) invals regvals aignet)))
                  (< 1 (nfix (nth toggle refcounts)))
                  (ids-multiply-referenced toggles refcounts)
                  (not (equal (nfix toggle) (nfix sink))))
             (not (lit-list-has-const0-under-toggle
                   (gate-node-supergate sink refcounts aignet)
                   toggle toggles invals regvals aignet)))
    :hints (("goal" :in-theory (enable gate-node-supergate)
             :use ((:instance aignet-eval-conjunction-toggle-when-lit-list-has-const0-under-toggle
                    (x (gate-node-supergate sink refcounts aignet)))
                   (:instance aignet-eval-conjunction-when-lit-list-has-const0-under-toggle
                    (x (gate-node-supergate sink refcounts aignet))))
            :expand ((:free (toggles) (aignet-eval-conjunction-toggle nil toggles invals regvals aignet))
                     (:free (var neg toggles) (lit-eval-toggle (make-lit var neg) toggles invals regvals aignet))
                     (:free (a b) (ids-multiply-referenced (cons a b) refcounts))))))

  (defthmd lit-list-has-const0-under-toggle-when-member
    (implies (and (member-equal lit (lit-list-fix x))
                  (equal (lit-eval-toggle lit toggles invals regvals aignet) 0)
                  (equal (lit-eval-toggle lit (cons toggle toggles) invals regvals aignet) 0))
             (lit-list-has-const0-under-toggle x toggle toggles invals regvals aignet))
    :hints(("Goal" :in-theory (enable member-equal lit-list-fix)))))


(defsection cube-contradictionp
  (local (defthm aignet-eval-conjunction-when-member-0
           (implies (and (member-equal k (lit-list-fix x))
                         (equal (lit-eval-toggle k toggles invals regvals aignet) 0))
                    (equal (aignet-eval-conjunction-toggle x toggles invals regvals aignet) 0))
           :hints(("Goal" :in-theory (enable aignet-eval-conjunction-toggle member-equal)))))

  (local (defthm b-xor-b-not
           (equal (b-xor (b-not a) b)
                  (b-not (b-xor a b)))
           :hints(("Goal" :in-theory (enable b-not)))))
  
  (defthm lit-eval-toggle-of-lit-negate
    (equal (lit-eval-toggle (lit-negate x) toggles invals regvals aignet)
           (b-not (lit-eval-toggle x toggles invals regvals aignet)))
    :hints(("Goal" :expand ((:free (x) (lit-eval-toggle x toggles invals regvals aignet))))))
  
  (defthm aignet-eval-conjunction-toggle-when-cube-contradictionp
    (implies (cube-contradictionp x)
             (equal (aignet-eval-conjunction-toggle x toggles invals regvals aignet) 0))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction-toggle
                                      cube-contradictionp))))

  (defthm cube-contradictionp-of-gate-node-supergate-when-and
    (implies (and (equal (stype (car (lookup-id sink aignet))) :and)
                  (not (equal (id-eval-toggle sink toggles invals regvals aignet)
                              (id-eval-toggle sink (cons toggle toggles) invals regvals aignet)))
                  (< 1 (nfix (nth toggle refcounts)))
                  (ids-multiply-referenced toggles refcounts)
                  (not (equal (nfix toggle) (nfix sink)))
                  ;; (not (member-equal (nfix sink) (acl2::nat-list-fix toggles)))
                  )
             (not (cube-contradictionp (gate-node-supergate sink refcounts aignet))))
    :hints (("goal" :in-theory (e/d (gate-node-supergate)
                                    (aignet-eval-conjunction-toggle-when-cube-contradictionp
                                     cube-contradictionp-correct))
             :use ((:instance aignet-eval-conjunction-toggle-when-cube-contradictionp
                    (x (gate-node-supergate sink refcounts aignet)))
                   (:instance aignet-eval-conjunction-toggle-when-cube-contradictionp
                    (x (gate-node-supergate sink refcounts aignet))
                    (toggles (cons toggle toggles))))
            :expand ((:free (a b) (ids-multiply-referenced (cons a b) refcounts))
                     (:free (toggles) (aignet-eval-conjunction-toggle nil toggles invals regvals aignet))
                     (:free (var neg toggles) (lit-eval-toggle (make-lit var neg) toggles invals regvals aignet)))))))
                  

(define has-toggling-lit ((x lit-listp) (toggle natp) (toggles nat-listp) invals regvals aignet)
  :guard (and (aignet-lit-listp x aignet)
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  (if (atom x)
      nil
    (or (not (eql (lit-eval-toggle (car x) (cons toggle toggles) invals regvals aignet)
                  (lit-eval-toggle (car x) toggles invals regvals aignet)))
        (has-toggling-lit (cdr x) toggle toggles invals regvals aignet)))

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

  (local (defthm nat-listp-of-remove
           (implies (nat-listp x)
                    (nat-listp (remove-equal k x)))))

  ;; (local (defthm member-of-cons-remove
  ;;          (iff (member k (cons x (remove x y)))
  ;;               (or (equal k x) (member k y)))))

  (local (defthm cons-remove-under-set-equiv
           (acl2::set-equiv (cons x (remove x y))
                            (if (member x y)
                                y
                              (cons x y)))
           :hints(("Goal" :in-theory (enable acl2::set-equiv)))))

  (local (defthm remove-under-set-equiv-when-not-member
           (implies (not (member x y))
                    (acl2::set-equiv (remove x y) y))
           :hints(("Goal" :in-theory (enable acl2::set-equiv)))))

  (local (defret <fn>-remove-toggle-when-greater
           (implies (< (nfix id) (nfix toggle))
                    (equal (let ((toggles (remove toggle toggles))) <call>)
                           val))
           :hints (("goal" :use ((:instance <fn>-add-toggle-when-greater
                                  (toggles (remove toggle toggles))))
                    :in-theory (disable <fn>-add-toggle-when-greater)))
           :fn id-eval-toggle))

  (local (defret <fn>-remove-toggle-when-greater
           (implies (< (lit->var lit) (nfix toggle))
                    (equal (let ((toggles (remove toggle toggles))) <call>)
                           val))
           :hints (("goal" :use ((:instance <fn>-add-toggle-when-greater
                                  (toggles (remove toggle toggles))))
                    :in-theory (disable <fn>-add-toggle-when-greater)))
           :fn lit-eval-toggle))


  (local (defthm id-eval-toggle-of-toggle
           (equal (id-eval-toggle toggle (cons toggle toggles) invals regvals aignet)
                  (b-not (id-eval-toggle toggle (remove (nfix toggle)
                                                 (acl2::nat-list-fix toggles)) invals regvals aignet)))
           :hints (("goal" :expand
                    ((:free (toggles) (id-eval-toggle toggle toggles invals regvals aignet)))
                    :in-theory (enable eval-xor-of-lits-toggle
                                       eval-xor-of-lits
                                       eval-and-of-lits-toggle
                                       eval-and-of-lits
                                       lit-eval-toggle
                                       lit-eval)))))

  
  (local (defthmd lit-eval-toggle-when-lit->var-equal-toggle
           (implies (equal (lit->var lit) (nfix toggle))
                    (equal (lit-eval-toggle lit (cons toggle toggles) invals regvals aignet)
                           (b-not (lit-eval-toggle lit
                                                   (remove (nfix toggle)
                                                           (acl2::nat-list-fix toggles))
                                                   invals regvals aignet))))
           :hints(("Goal" :in-theory (enable lit-eval-toggle lit-eval)
                   :expand ((lit-eval-toggle lit toggles invals regvals aignet)
                            (lit-eval lit invals regvals aignet))))))

  ;; (local (defthm lit-eval-toggle-of-lit->var
  ;;          (equal (lit-eval-toggle lit (lit->var lit) invals regvals aignet)
  ;;                 (b-not (lit-eval lit invals regvals aignet)))
  ;;          :hints (("goal" :in-theory (enable lit-eval-toggle-when-lit->var-equal-toggle)))))

  
  (local (defthm has-toggling-lit-when-member
           (implies (and (member-equal lit (lit-list-fix supergate))
                         (not (equal (lit-eval-toggle lit (cons toggle toggles) invals regvals aignet)
                                     (lit-eval-toggle lit toggles invals regvals aignet))))
                    (has-toggling-lit supergate toggle toggles invals regvals aignet))
           :hints(("Goal" :in-theory (enable has-toggling-lit lit-list-fix member-equal)))))

  (local (defthmd has-toggling-lit-when-eval-conjunction-differs
           (implies (not (equal (aignet-eval-conjunction-toggle x (cons toggle toggles) invals regvals aignet)
                                (aignet-eval-conjunction-toggle x toggles invals regvals aignet)))
                    (has-toggling-lit x toggle toggles invals regvals aignet))
           :hints(("Goal" :in-theory (enable aignet-eval-conjunction
                                             aignet-eval-conjunction-toggle)))))

  (local (defthmd has-toggling-lit-when-eval-parity-differs
           (implies (not (equal (aignet-eval-parity-toggle x (cons toggle toggles) invals regvals aignet)
                                (aignet-eval-parity-toggle x toggles invals regvals aignet)))
                    (has-toggling-lit x toggle toggles invals regvals aignet))
           :hints(("Goal" :in-theory (enable aignet-eval-parity
                                             aignet-eval-parity-toggle)))))

  ;; (local (defthm lit-collect-supergate-preserves-supergate-toggle
  ;;          (implies (has-toggling-lit supergate toggles invals regvals aignet)
  ;;                   (has-toggling-lit
  ;;                    (mv-nth 0 (lit-collect-supergate lit top use-muxes limit supergate refcounts aignet))
  ;;                    toggles invals regvals aignet))
  ;;          :hints (("goal" :induct (lit-collect-supergate lit top use-muxes limit supergate refcounts aignet)
  ;;                   :in-theory (enable (:i lit-collect-supergate))
  ;;                   :expand ((:free (top use-muxes limit)
  ;;                             (lit-collect-supergate lit top use-muxes limit supergate refcounts aignet))
  ;;                            (lit-eval-toggle 0 toggles invals regvals aignet)
  ;;                            (id-eval-toggle 0 toggles invals regvals aignet))))))
  
  ;; (local (defthm id-eval-toggle-in-terms-of-supergate
  ;;          (implies (and (not (equal (lit-eval lit invals regvals aignet)
  ;;                                    (lit-eval-toggle lit toggles invals regvals aignet)))
  ;;                        (< 1 (nfix (nth toggles refcounts)))
  ;;                        (or (not top)
  ;;                            (not (equal (lit->var lit) (nfix toggle)))))
  ;;                   (has-toggling-lit
  ;;                    (mv-nth 0 (lit-collect-supergate lit top use-muxes limit supergate refcounts aignet))
  ;;                                     toggles invals regvals aignet))
  ;;          :hints (("goal" :induct (lit-collect-supergate lit top use-muxes limit supergate refcounts aignet)
  ;;                   :in-theory (enable (:i lit-collect-supergate) b-and)
  ;;                   :expand ((:free (top use-muxes limit)
  ;;                             (lit-collect-supergate lit top use-muxes limit supergate refcounts aignet))
  ;;                            (lit-eval lit invals regvals aignet)
  ;;                            (lit-eval-toggle lit toggles invals regvals aignet)
  ;;                            (id-eval (lit->var lit) invals regvals aignet)
  ;;                            (:free (toggle) (id-eval-toggle (lit->var lit) toggles invals regvals aignet))
  ;;                            (:free (a b) (eval-and-of-lits a b invals regvals aignet))
  ;;                            (:free (a b) (eval-xor-of-lits a b invals regvals aignet))
  ;;                            (:free (a b) (eval-and-of-lits-toggle a b toggles invals regvals aignet))
  ;;                            (:free (a b) (eval-xor-of-lits-toggle a b toggles invals regvals aignet)))
  ;;                   :do-not-induct t)
  ;;                  (and stable-under-simplificationp
  ;;                       '(:in-theory (enable lit-eval-toggle-when-lit->var-equal-toggle))))))

  ;; (local (defthm lit-collect-superxor-preserves-supergate-toggle
  ;;          (implies (has-toggling-lit supergate toggles invals regvals aignet)
  ;;                   (has-toggling-lit
  ;;                    (mv-nth 0 (lit-collect-superxor lit top limit supergate refcounts aignet))
  ;;                    toggles invals regvals aignet))
  ;;          :hints (("goal" :induct (lit-collect-superxor lit top limit supergate refcounts aignet)
  ;;                   :in-theory (enable (:i lit-collect-superxor))
  ;;                   :expand ((:free (top limit)
  ;;                             (lit-collect-superxor lit top limit supergate refcounts aignet))
  ;;                            (lit-eval-toggle 0 toggles invals regvals aignet)
  ;;                            (id-eval-toggle 0 toggles invals regvals aignet))))))
  
  ;; (local (defthm id-eval-toggle-in-terms-of-superxor
  ;;          (implies (and (not (equal (lit-eval lit invals regvals aignet)
  ;;                                    (lit-eval-toggle lit toggles invals regvals aignet)))
  ;;                        (< 1 (nfix (nth toggles refcounts)))
  ;;                        (or (not top)
  ;;                            (not (equal (lit->var lit) (nfix toggle)))))
  ;;                   (has-toggling-lit
  ;;                    (mv-nth 0 (lit-collect-superxor lit top limit supergate refcounts aignet))
  ;;                                     toggles invals regvals aignet))
  ;;          :hints (("goal" :induct (lit-collect-superxor lit top limit supergate refcounts aignet)
  ;;                   :in-theory (enable (:i lit-collect-superxor) b-and)
  ;;                   :expand ((:free (top limit)
  ;;                             (lit-collect-superxor lit top limit supergate refcounts aignet))
  ;;                            (lit-eval lit invals regvals aignet)
  ;;                            (lit-eval-toggle lit toggles invals regvals aignet)
  ;;                            (id-eval (lit->var lit) invals regvals aignet)
  ;;                            (id-eval-toggle (lit->var lit) toggles invals regvals aignet)
  ;;                            (:free (a b) (eval-and-of-lits a b invals regvals aignet))
  ;;                            (:free (a b) (eval-xor-of-lits a b invals regvals aignet))
  ;;                            (:free (a b) (eval-and-of-lits-toggle a b toggles invals regvals aignet))
  ;;                            (:free (a b) (eval-xor-of-lits-toggle a b toggles invals regvals aignet)))
  ;;                   :do-not-induct t))))
  
  (local (defthm equal-of-b-xors
           (equal (equal (b-xor a b) (b-xor a c))
                  (equal (bfix b) (bfix c)))
           :hints(("Goal" :in-theory (enable b-xor)))))

  (defthm supergate-has-toggling-lit-when-toggles
    (implies (and (not (equal (id-eval-toggle sink (cons toggle toggles) invals regvals aignet)
                              (id-eval-toggle sink toggles invals regvals aignet)))
                  (< 1 (nfix (nth toggle refcounts)))
                  (ids-multiply-referenced toggles refcounts) 
                  (not (equal (nfix toggle) (nfix sink)))
                  ;; (not (member (nfix sink) (acl2::nat-list-fix toggles)))
                  )
             (has-toggling-lit (gate-node-supergate sink refcounts aignet)
                               toggle toggles invals regvals aignet))
    :hints(("Goal" :in-theory (e/d (gate-node-supergate)
                                   (has-toggling-lit-when-eval-parity-differs
                                    has-toggling-lit-when-eval-conjunction-differs
                                    has-toggling-lit))
            :use ((:instance has-toggling-lit-when-eval-parity-differs
                   (x (gate-node-supergate sink refcounts aignet)))
                  (:instance has-toggling-lit-when-eval-conjunction-differs
                   (x (gate-node-supergate sink refcounts aignet))))
            :expand ((:free (toggles) (aignet-eval-parity-toggle nil toggles invals regvals aignet))
                     (:free (toggles) (aignet-eval-conjunction-toggle nil toggles invals regvals aignet))
                     (:free (var neg toggles) (lit-eval-toggle (make-lit var neg) toggles invals regvals aignet))
                     (:Free (a b) (ids-multiply-referenced (cons a b) refcounts)))))))



(define min-toggling-lit ((x lit-listp) (toggle natp) (toggles nat-listp) invals regvals aignet)
  :guard (and (aignet-lit-listp x aignet)
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  :returns (min-index natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (b* ((togglep (not (eql (lit-eval-toggle (car x) (cons toggle toggles) invals regvals aignet)
                            (lit-eval-toggle (car x) toggles invals regvals aignet))))
         (rest (min-toggling-lit (cdr x) toggle toggles invals regvals aignet))
         ((unless togglep) (+ 1 rest))
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
         (has-toggling-lit x toggle toggles invals regvals aignet))
    :hints(("Goal" :in-theory (enable has-toggling-lit))))

  (defret min-toggling-lit-bound-strong-linear
    (implies (has-toggling-lit x toggle toggles invals regvals aignet)
             (< min-index (len x)))
    :rule-classes :linear)

  (defret min-toggling-lit-bound-equal-rw
    (iff (equal min-index (len x))
         (not (has-toggling-lit x toggle toggles invals regvals aignet)))
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
    (implies (has-toggling-lit x toggle toggles invals regvals aignet)
             (not (equal (id-eval-toggle (lit->var (nth min-index x)) (cons toggle toggles) invals regvals aignet)
                         (id-eval-toggle (lit->var (nth min-index x)) toggles invals regvals aignet))))
    :hints(("Goal" :in-theory (e/d (lit-eval-toggle)
                                   (min-toggling-lit-bound-strong-linear))
            :expand ((has-toggling-lit x toggle toggles invals regvals aignet)))))

  (local (defthm has-toggling-lit-when-member
           (implies (and (member-equal lit (lit-list-fix supergate))
                         (not (equal (lit-eval-toggle lit (cons toggle toggles) invals regvals aignet)
                                     (lit-eval-toggle lit toggles invals regvals aignet))))
                    (has-toggling-lit supergate toggle toggles invals regvals aignet))
           :hints(("Goal" :in-theory (enable has-toggling-lit lit-list-fix member-equal)))))
  
  (defret min-toggling-lit-is-minimum
    (implies (and (not (equal (lit-eval-toggle k (cons toggle toggles) invals regvals aignet)
                              (lit-eval-toggle k toggles invals regvals aignet)))
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
                                x toggle toggles invals regvals aignet))
                          (not (has-toggling-lit x toggle toggles invals regvals aignet)))
                     (lit-list-has-const0-under-toggle
                      y toggle toggles invals regvals aignet))
            :hints(("Goal" :in-theory (enable lit-list-has-const0-under-toggle
                                              has-toggling-lit
                                              two-cubes-contradictionp
                                              lit-list-has-const0-under-toggle-when-member)))))
   
   (defthmd not-two-cubes-contradictionp-lemma
     (implies (and (not (lit-list-has-const0-under-toggle
                         x toggle toggles invals regvals aignet))
                   (not (lit-list-has-const0-under-toggle
                         y toggle toggles invals regvals aignet))
                   (has-toggling-lit x toggle toggles invals regvals aignet)
                   (< (lits-max-id-val y)
                      (lit->var (nth (min-toggling-lit x toggle toggles invals regvals aignet)
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
                      (min-toggling-lit x toggle toggles invals regvals aignet)
                      (:free (n) (nth n x))
                      (has-toggling-lit x toggle toggles invals regvals aignet)
                      (lit-list-has-const0-under-toggle
                       x toggle toggles invals regvals aignet))
             :do-not-induct t)))))

(define toggle-witness-spath ((sink natp) (source natp) (toggles nat-listp) invals regvals refcounts aignet)
  ;; Given that sink is toggled by source, find a path from sink to source
  ;; containing no contradictory AND siblings and no const0 siblings.
  :guard (and (id-existsp sink aignet)
              (id-existsp source aignet)
              (<= (num-fanins aignet) (u32-length refcounts))
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals))
              (not (equal (id-eval-toggle sink (cons source toggles) invals regvals aignet)
                          (id-eval-toggle sink toggles invals regvals aignet)))
              (ids-multiply-referenced toggles refcounts)
              (< 1 (get-u32 source refcounts)))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable aignet-idp))))
  :measure (nfix sink)
  :returns (path nat-listp)
  ;; :verify-guards nil
  (b* (((when (or (<= (lnfix sink) (lnfix source))
                  (not (eql (id->type sink aignet) (gate-type)))))
        nil)
       (supergate (gate-node-supergate sink refcounts aignet))
       (next-idx (min-toggling-lit supergate source toggles invals regvals aignet)))
    (cons next-idx (toggle-witness-spath (lit->var (nth next-idx supergate))
                                        source toggles invals regvals refcounts aignet)))
  ///
  (local (in-theory (disable (:d toggle-witness-spath))))
  
  (defret spath-existsp-of-<fn>
    (implies (and (not (equal (id-eval-toggle sink toggles invals regvals aignet)
                              (id-eval-toggle sink (cons source toggles) invals regvals aignet)))
                  (< 1 (nfix (nth source refcounts)))
                  (ids-multiply-referenced toggles refcounts))
             (spath-existsp sink path refcounts aignet))
    :hints (("Goal" :induct <call> :expand (<call>))))

  (local (defthm nat-listp-of-remove
           (implies (nat-listp x)
                    (nat-listp (remove-equal k x)))))

  (defret id-eval-toggle-when-not-gate
    (implies (not (equal (ctype (stype (car (lookup-id x aignet)))) :gate))
             (equal (id-eval-toggle x (cons toggle toggles) invals regvals aignet)
                    (b-xor (bool->bit (equal (nfix x) (nfix toggle)))
                           (id-eval-toggle x (remove-equal (nfix toggle) (acl2::nat-list-fix toggles))
                                           invals regvals aignet))))
    :hints(("Goal" :in-theory (enable* id-eval-toggle acl2::arith-equiv-forwarding))))

  (defret id-eval-toggle-of-remove-equal-when-not-gate
    (implies (And (not (equal (ctype (stype (car (lookup-id x aignet)))) :gate))
                  (natp toggle) (nat-listp toggles))
             (equal (id-eval-toggle x (remove-equal toggle toggles)
                                    invals regvals aignet)
                    (b-xor (bool->bit (and (equal (nfix x) toggle)
                                           (member-equal toggle toggles)))
                           (id-eval-toggle x toggles invals regvals aignet))))
    :hints(("Goal" :in-theory (enable* id-eval-toggle acl2::arith-equiv-forwarding))))
                        
  
  (defret spath-endpoint-of-<fn>
    (implies (and (not (equal (id-eval-toggle sink toggles invals regvals aignet)
                              (id-eval-toggle sink (cons source toggles) invals regvals aignet)))
                  (< 1 (nfix (nth source refcounts)))
                  (ids-multiply-referenced toggles refcounts))
             (equal (spath-endpoint sink path refcounts aignet)
                    (nfix source)))
    :hints (("Goal" :induct <call> :expand (<call>))))

  (defret has-const0-of-<fn>
    (implies (and (not (equal (id-eval-toggle sink toggles invals regvals aignet)
                              (id-eval-toggle sink (cons source toggles) invals regvals aignet)))
                  (< 1 (nfix (nth source refcounts)))
                  (ids-multiply-referenced toggles refcounts))
             (not (lit-list-has-const0-under-toggle
                   (spath-and-literals sink path refcounts aignet)
                   source toggles invals regvals aignet)))
    :hints (("Goal" :induct <call> :expand (<call>))))


 (local (defthm not-two-cubes-contradictionp-lemma-rw
           (implies (and (bind-free '((toggle . source)
                                      (toggles . toggles)
                                      (invals . invals)
                                      (regvals . regvals)
                                      (aignet . aignet))
                                    (toggle toggles invals regvals aignet))
                         (not (lit-list-has-const0-under-toggle
                               x toggle toggles invals regvals aignet))
                         (not (lit-list-has-const0-under-toggle
                               y toggle toggles invals regvals aignet))
                         (has-toggling-lit x toggle toggles invals regvals aignet)
                         (< (lits-max-id-val y)
                            (lit->var (nth (min-toggling-lit x toggle toggles invals regvals aignet)
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
    (implies (and (not (equal (id-eval-toggle sink toggles invals regvals aignet)
                              (id-eval-toggle sink (cons source toggles) invals regvals aignet)))
                  (< 1 (nfix (nth source refcounts)))
                  (ids-multiply-referenced toggles refcounts))
             (not (cube-contradictionp
                   (spath-and-literals sink path refcounts aignet))))
    :hints (("Goal" :induct <call> :expand (<call>)
             :in-theory (enable cube-contradictionp-of-append))
            (and stable-under-simplificationp
                 '(:cases ((zp (lit->var
                                (nth (min-toggling-lit
                                      (gate-node-supergate sink refcounts aignet)
                                      source toggles invals regvals aignet)
                                     (gate-node-supergate sink refcounts aignet))))))))))




;; Dominator info for each node is stored as either
;; (1) T, signifying that every path from an output to the node contains
;;     contradictory literals, or
;; (2) a list of literals, all of which must occur as AND-siblings in every
;;     path from an output to the node not containing contradictory literals,
;;     mergesorted.

(define obs-sdom-info-p (x)
  (or (eq x t)
      (and (lit-listp x) (set::setp x)))
  ///
  (define obs-sdom-info-fix ((x obs-sdom-info-p))
    :returns (new-x obs-sdom-info-p)
    :inline t
    (mbe :logic (if (eq x t) t (set::mergesort (lit-list-fix x)))
         :exec x)
    ///
    (defthm obs-sdom-info-fix-when-obs-sdom-info-p
      (implies (obs-sdom-info-p x)
               (equal (obs-sdom-info-fix x) x)))

    (fty::deffixtype obs-sdom-info :pred obs-sdom-info-p :fix obs-sdom-info-fix
      :equiv obs-sdom-info-equiv :define t :forward t)))

(define make-obs-sdom-info-unreached ()
  :returns (info obs-sdom-info-p)
  :inline t
  t)

(define make-obs-sdom-info-reached ((doms lit-listp))
  :guard (set::setp doms)
  :returns (info obs-sdom-info-p
                 :hints (("goal" :in-theory (Enable obs-sdom-info-p))))
  :inline t
  (mbe :logic (set::mergesort (lit-list-fix doms))
       :exec doms))

(define obs-sdom-info->reached ((x obs-sdom-info-p))
  :inline t
  :hooks nil
  (not (eq x t))
  ///
  (defthm obs-sdom-info->reached-of-make-obs-sdom-info-reached
    (obs-sdom-info->reached (make-obs-sdom-info-reached doms)))

  (fty::deffixequiv obs-sdom-info->reached
    :hints (("goal" :in-theory (enable obs-sdom-info-fix)))))


(define obs-sdom-info->doms ((x obs-sdom-info-p))
  :inline t
  ;; :guard (obs-sdom-info->reached x)
  :returns (doms lit-listp)
  :guard-hints (("goal" :in-theory (enable obs-sdom-info-p obs-sdom-info->reached)))
  :hooks nil
  (if (eq x t)
      nil
    (mbe :logic (set::mergesort (lit-list-fix x))
         :exec x))
  ///
  (defret setp-of-<fn>
    (set::setp doms))
  
  (defthm obs-sdom-info->doms-of-make-obs-sdom-info-reached
    (equal (obs-sdom-info->doms (make-obs-sdom-info-reached doms))
           (set::mergesort (lit-list-fix doms)))
    :hints (("goal" :in-theory (enable make-obs-sdom-info-reached))))

  (fty::deffixequiv obs-sdom-info->doms
    :hints (("goal" :in-theory (enable obs-sdom-info-fix))))

  (defthm make-obs-sdom-info-reached-of-doms
    (implies (obs-sdom-info->reached x)
             (equal (make-obs-sdom-info-reached (obs-sdom-info->doms x))
                    (obs-sdom-info-fix x)))
    :hints(("Goal" :in-theory (enable make-obs-sdom-info-reached
                                      obs-sdom-info-fix)))))


(acl2::def-b*-binder
  obs-sdom-info
  :body (std::da-patbind-fn 'obs-sdom-info
                            '((reached . obs-sdom-info->reached)
                              (doms . obs-sdom-info->doms))
                            args acl2::forms acl2::rest-expr))

(define obs-sdom-info-well-formedp ((info obs-sdom-info-p) aignet)
  :returns wfp
  (b* (((obs-sdom-info info)))
    (or (not info.reached)
        (aignet-lit-listp info.doms aignet)))
  ///
  (defret aignet-lit-listp-of-doms-when-<fn>
    (b* (((obs-sdom-info info)))
      (implies wfp
               (aignet-lit-listp info.doms aignet)))
    :hints (("goal" :in-theory (enable obs-sdom-info->reached obs-sdom-info->doms))))

  ;; (local (defthmd lits-max-id-val-when-aignet-lit-listp
  ;;          (implies (aignet-lit-listp x aignet)
  ;;                   (< (lits-max-id-val x) (num-fanins aignet)))
  ;;          :hints(("Goal" :in-theory (enable aignet-lit-listp
  ;;                                            lits-max-id-val
  ;;                                            aignet-idp)))))

  ;; (defret lits-max-id-val-when-<fn>
  ;;   (b* (((obs-sdom-info info)))
  ;;     (implies wfp
  ;;              (< (lits-max-id-val info.doms) (num-fanins aignet))))
  ;;   :hints (("goal" :use ((:instance lits-max-id-val-when-aignet-lit-listp
  ;;                          (x (obs-sdom-info->doms info))))))
  ;;   :rule-classes :linear)
  (defthm obs-sdom-info-well-formedp-of-nil
    (obs-sdom-info-well-formedp nil aignet))
  )

(local (defthm lits-max-id-val-of-num-fanins
         (equal (< (lits-max-id-val x) (+ 1 (fanin-count aignet)))
                (aignet-lit-listp x aignet))
         :hints(("Goal" :in-theory (enable lits-max-id-val aignet-lit-listp
                                           aignet-idp)))))





(fty::deflist obs-sdom-info-list :elt-type obs-sdom-info :true-listp t)

(make-event
 `(acl2::def-1d-arr obs-sdom-array
    :slotname sdominfo
    :pred obs-sdom-info-p
    :fix obs-sdom-info-fix
    :default-val ,(make-obs-sdom-info-unreached)
    :rename ((resize-sdominfos . resize-sdominfo)
             (sdominfos-length . sdominfo-length))))

(defthm obs-sdom-array$ap-is-obs-sdom-info-list-p
  (equal (obs-sdom-array$ap x)
         (obs-sdom-info-list-p x)))

(defsection obs-sdom-array-well-formedp
  (defun-sk obs-sdom-array-well-formedp (obs-sdom-array aignet)
    (forall i
            (obs-sdom-info-well-formedp (nth i obs-sdom-array) aignet))
    :rewrite :direct)

  (in-theory (disable obs-sdom-array-well-formedp))

  (defthm obs-sdom-array-well-formedp-of-update
    (implies (and (obs-sdom-array-well-formedp obs-sdom-array aignet)
                  (obs-sdom-info-well-formedp val aignet))
             (obs-sdom-array-well-formedp (update-nth n val obs-sdom-array) aignet))
    :hints (("goal" :expand ((obs-sdom-array-well-formedp (update-nth n val obs-sdom-array) aignet)))))

  ;; (defthm lits-max-id-val-when-obs-sdom-array-well-formedp
  ;;   (implies (obs-sdom-array-well-formedp obs-sdom-array aignet)
  ;;            (< (lits-max-id-val
  ;;                (obs-sdom-info->doms (nth n obs-sdom-array))) (num-fanins aignet)))
  ;;   :hints (("goal" :use ((:instance lits-max-id-val-when-obs-sdom-info-well-formedp
  ;;                          (info (nth n obs-sdom-array))))
  ;;            :in-theory (enable lits-max-id-val-when-obs-sdom-info-well-formedp)))
  ;;   :rule-classes :linear)
  (local (defthm obs-sdom-info-well-formedp-when-boolean
           (implies (booleanp info)
                    (obs-sdom-info-well-formedp info aignet))
           :hints(("Goal" :in-theory (enable obs-sdom-info-well-formedp booleanp)))))

  (defthm obs-sdom-array-well-formedp-of-repeat-t
    (obs-sdom-array-well-formedp (acl2::repeat n t) aignet)
    :hints(("Goal" :in-theory (enable obs-sdom-array-well-formedp))))
  )


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

(define obs-sdom-info-subsetp ((x obs-sdom-info-p)
                              (y obs-sdom-info-p))
  :returns (subsetp)
  (b* (((obs-sdom-info x))
       ((obs-sdom-info y)))
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
                  (obs-sdom-info->reached y)
                  (not (cube-contradictionp (obs-sdom-info->doms y)))
                  )
             (obs-sdom-info->reached x)))

  (defretd <fn>-implies-member
    (implies (and subsetp
                  (obs-sdom-info->reached y)
                  (not (cube-contradictionp (obs-sdom-info->doms y)))
                  (not (member-equal lit (obs-sdom-info->doms y))))
             (not (member lit (obs-sdom-info->doms x)))))
  
  (defthmd obs-sdom-info-subsetp-transitive
    (implies (and (obs-sdom-info-subsetp a b)
                  (obs-sdom-info-subsetp b c))
             (obs-sdom-info-subsetp a c))
    :hints(("Goal" :in-theory (enable cube-contradictionp-when-subsetp))))

  (defthm obs-sdom-info-subsetp-self
    (obs-sdom-info-subsetp x x)))



(define obs-sdom-info-add-lits ((lits lit-listp) (x obs-sdom-info-p))
  :returns (new obs-sdom-info-p)
  (b* (((obs-sdom-info x)))
    (if x.reached
        (make-obs-sdom-info-reached (set::union (set::mergesort (lit-list-fix lits)) x.doms))
      (make-obs-sdom-info-unreached)))
  ///

  (defret <fn>-when-unreached
    (implies (not (obs-sdom-info->reached x))
             (equal new (make-obs-sdom-info-unreached))))

  (defret <fn>-when-reached
    (implies (obs-sdom-info->reached x)
             (obs-sdom-info->reached new)))

  (defret member-of-<fn>
    (implies (obs-sdom-info->reached x)
             (iff (member-equal dom (obs-sdom-info->doms new))
                  (or (member-equal dom (lit-list-fix lits))
                      (member-equal dom (obs-sdom-info->doms x))))))

  (defret obs-sdom-info-well-formedp-of-obs-sdom-info-add-lits
    (implies (and (aignet-lit-listp lits aignet)
                  (obs-sdom-info-well-formedp x aignet))
             (obs-sdom-info-well-formedp new aignet))
    :hints(("Goal" :in-theory (enable obs-sdom-info-well-formedp)))))

(define obs-sdom-info-for-child ((fanout-info obs-sdom-info-p)
                                (fanout natp)
                                refcounts
                                aignet)
  :guard (and (id-existsp fanout aignet)
              (eql (id->type fanout aignet) (gate-type))
              (< fanout (u32-length refcounts)))
  :returns (child-fanout-info obs-sdom-info-p)
  (b* (;; (fanin0 (gate-id->fanin0 fanout aignet))
       ;; (fanin1 (gate-id->fanin1 fanout aignet))
       (xor (eql 1 (id->regp fanout aignet))))
    (if xor
        ;; Won't complicate things with this optimization since hashing should prevent this anyhow.
        ;; (if (or (eql fanin0 fanin1)
        ;;         (eql fanin0 (lit-negate fanin1)))
        ;;     (make-obs-sdom-info-unreached)
        (obs-sdom-info-fix fanout-info)
      ;; (cond ((eql fanin0 fanin1) (obs-sdom-info-fix fanout-info))
      ;;       ((eql fanin0 (lit-negate fanin1)) (make-obs-sdom-info-unreached))
      ;;       (t
      (obs-sdom-info-add-lits
       (gate-node-supergate fanout refcounts aignet)
       fanout-info)))
  ///

  (defret <fn>-when-xor
    (implies (equal (stype (car (lookup-id fanout aignet))) :xor)
             (equal child-fanout-info
                    (obs-sdom-info-fix fanout-info))))
  
  (defret <fn>-when-and
    (implies (equal (stype (car (lookup-id fanout aignet))) :and)
             (equal child-fanout-info
                    (obs-sdom-info-add-lits (gate-node-supergate fanout refcounts aignet)
                                           fanout-info)))))


(define obs-sdom-fanins-ok ((super lit-listp)
                           (parent-info obs-sdom-info-p)
                           obs-sdom-array)
  :guard (< (lits-max-id-val super) (sdominfo-length obs-sdom-array))
  (if (atom super)
      t
    (and (obs-sdom-info-subsetp (get-sdominfo (lit->var (car super)) obs-sdom-array)
                               parent-info)
         (obs-sdom-fanins-ok (cdr super) parent-info obs-sdom-array)))
  ///
  (defthm obs-sdom-fanins-ok-implies-member-subset
    (implies (and (obs-sdom-fanins-ok super parent-info obs-sdom-array)
                  (member lit super))
             (obs-sdom-info-subsetp (nth (lit->var lit) obs-sdom-array) parent-info)))

  (defthm obs-sdom-fanins-ok-when-unreached
    (implies (not (obs-sdom-info->reached parent-info))
             (obs-sdom-fanins-ok super parent-info obs-sdom-array))
    :hints(("Goal" :in-theory (enable obs-sdom-info-subsetp)))))

(define obs-sdom-fanout-ok ((fanout natp) obs-sdom-array refcounts aignet)
  :guard (and (id-existsp fanout aignet)
              (<= (num-fanins aignet) (sdominfo-length obs-sdom-array))
              (<= (num-fanins aignet) (u32-length refcounts)))
  (or (not (eql (id->type fanout aignet) (gate-type)))
      (let* ((super (gate-node-supergate fanout refcounts aignet))
             (sdominfo (get-sdominfo fanout obs-sdom-array)))
        (if (eql (id->regp fanout aignet) 1)
            (obs-sdom-fanins-ok super sdominfo obs-sdom-array)
          (obs-sdom-fanins-ok
           super (obs-sdom-info-add-lits super sdominfo) obs-sdom-array))))
  ///
  (defthm obs-sdom-fanout-ok-implies-xor-child
    (implies (and (obs-sdom-fanout-ok fanout obs-sdom-array refcounts aignet)
                  (equal (stype (car (lookup-id fanout aignet))) :xor)
                  (member lit (gate-node-supergate fanout refcounts aignet)))
             (obs-sdom-info-subsetp (nth (lit->var lit) obs-sdom-array)
                                   (nth fanout obs-sdom-array))))

  (defthm obs-sdom-fanout-ok-implies-and-child
    (implies (and (obs-sdom-fanout-ok fanout obs-sdom-array refcounts aignet)
                  (equal (stype (car (lookup-id fanout aignet))) :and)
                  (member lit (gate-node-supergate fanout refcounts aignet)))
             (obs-sdom-info-subsetp (nth (lit->var lit) obs-sdom-array)
                                   (obs-sdom-info-add-lits
                                    (gate-node-supergate fanout refcounts aignet)
                                    (nth fanout obs-sdom-array)))))

  (defthmd obs-sdom-fanout-ok-out-of-bounds
    (implies (< (fanin-count aignet) (nfix n))
             (obs-sdom-fanout-ok n obs-sdom-array refcounts aignet))
    :hints(("Goal" :in-theory (enable obs-sdom-fanout-ok)))))



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

(define obs-sdom-info-normalize ((x obs-sdom-info-p))
  :returns (new-x obs-sdom-info-p)
  (b* (((obs-sdom-info x)))
    (if (and x.reached
             (cube-contradictionp-sorted x.doms))
        (make-obs-sdom-info-unreached)
      (obs-sdom-info-fix x)))
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
    (iff (obs-sdom-info-subsetp new-x y)
         (obs-sdom-info-subsetp x y))
    :hints(("Goal" :in-theory (enable obs-sdom-info-subsetp
                                      cube-contradictionp-when-subsetp))))

  (defret subsetp-of-<fn>-2
    (iff (obs-sdom-info-subsetp y new-x)
         (obs-sdom-info-subsetp y x))
    :hints(("Goal" :in-theory (enable obs-sdom-info-subsetp)))))



(define obs-sdom-info-intersect ((x obs-sdom-info-p) (y obs-sdom-info-p))
  :returns (int obs-sdom-info-p)
  (b* (((obs-sdom-info x))
       ((obs-sdom-info y)))
    (if (and x.reached (not (cube-contradictionp-sorted x.doms)))
        (if (and y.reached (not (cube-contradictionp-sorted y.doms)))
            (make-obs-sdom-info-reached (set::intersect x.doms y.doms))
          (obs-sdom-info-fix x))
      (obs-sdom-info-normalize y)))
  ///
  (local (in-theory (enable obs-sdom-info-subsetp
                            obs-sdom-info-normalize)))
  
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
  
  (defret obs-sdom-info-subsetp-of-obs-sdom-info-intersect-1
    (obs-sdom-info-subsetp int x))

  (defret obs-sdom-info-subsetp-of-obs-sdom-info-intersect-2
    (obs-sdom-info-subsetp int y))

  (defret obs-sdom-info-intersect-preserves-obs-sdom-info-subsetp-1
    (implies (obs-sdom-info-subsetp x z)
             (obs-sdom-info-subsetp int z)))
  
  (defret obs-sdom-info-intersect-preserves-obs-sdom-info-subsetp-2
    (implies (obs-sdom-info-subsetp y z)
             (obs-sdom-info-subsetp int z)))

  (local (defthm cube-contradictionp-of-intersect
           (implies (and (not (cube-contradictionp x))
                         (set::setp x))
                    (not (cube-contradictionp (set::intersect x y))))
           :hints(("Goal" :use ((:instance cube-contradictionp-when-subsetp
                                 (x (set::intersect x y))
                                 (y x)))))))
  
  (defret obs-sdom-info-intersect-idempotent
    (equal (obs-sdom-info-intersect (obs-sdom-info-intersect x y) y)
           (obs-sdom-info-intersect x y)))

  (defret obs-sdom-info-well-formedp-of-intersect
    (implies (and (obs-sdom-info-well-formedp x aignet)
                  (obs-sdom-info-well-formedp y aignet))
             (obs-sdom-info-well-formedp int aignet))
    :hints(("Goal" :in-theory (enable obs-sdom-info-well-formedp
                                      aignet-lit-listp-when-subsetp)))))



(defstub set-filter-elem-okp (x) nil)
(define set-filter (x)
  :returns (new-x)
  (if (atom x)
      nil
    (if (set-filter-elem-okp (car x))
        (cons (car x) (set-filter (cdr x)))
      (set-filter (cdr x))))
  ///
  (defret first-elem-bound-of-<fn>
    (implies (and (set::setp x)
                  (consp new-x))
             (not (acl2::<< (car new-x) (car x))))
    :hints(("Goal" :in-theory (enable set::setp
                                      acl2::<<-transitive
                                      acl2::<<-irreflexive))))

  (local
   (defthm <<-transitive-strong
     (implies (and (acl2::<< b c)
                   (not (acl2::<< b a)))
              (acl2::<< a c))
     :hints (("goal" :use ((:instance acl2::<<-trichotomy
                            (x b) (y a)))
              :in-theory (enable acl2::<<-transitive)))))

  (defret setp-of-set-filter
    (implies (set::setp x)
             (set::setp new-x))
    :hints(("Goal" :in-theory (enable set::setp
                                      acl2::<<-transitive
                                      acl2::<<-irreflexive)
            :induct <call>)
           (and stable-under-simplificationp
                '(:use ((:instance first-elem-bound-of-<fn>
                         (x (cdr x))))
                  :in-theory (disable first-elem-bound-of-<fn>))))))


(define filter-lits-by-level ((bound natp) (x lit-listp) aignet-levels)
  :guard (< (lits-max-id-val x) (u32-length aignet-levels))
  :returns (new-x lit-listp)
  (if (atom x)
      nil
    (if (< (get-u32 (lit->var (car x)) aignet-levels) (lnfix bound))
        (cons (lit-fix (car x))
              (filter-lits-by-level bound (cdr x) aignet-levels))
      (filter-lits-by-level bound (cdr x) aignet-levels)))
  ///
  (local (defun-nx filter-lits-by-level-no-fix (bound x aignet-levels)
           (if (atom x)
               nil
             (if (< (get-u32 (lit->var (car x)) aignet-levels) (lnfix bound))
                 (cons (car x)
                       (filter-lits-by-level-no-fix bound (cdr x) aignet-levels))
               (filter-lits-by-level-no-fix bound (cdr x) aignet-levels)))))
  (local (defthmd filter-lits-by-level-in-terms-of-no-fix
           (implies (lit-listp x)
                    (equal (filter-lits-by-level bound x aignet-levels)
                           (filter-lits-by-level-no-fix bound x aignet-levels)))
           :hints(("Goal" :in-theory (enable lit-listp)))))

  (defret setp-of-filter-lits-by-level
    (implies (and (set::setp x) (lit-listp x))
             (set::setp new-x))
    :hints(("Goal" :use ((:functional-instance setp-of-set-filter
                          (set-filter-elem-okp (lambda (x) (< (get-u32 (lit->var x) aignet-levels) (nfix bound))))
                          (set-filter (lambda (x)
                                        (filter-lits-by-level-no-fix bound x aignet-levels)))))
            :in-theory (enable filter-lits-by-level-in-terms-of-no-fix))))

  (defret subsetp-equal-of-<fn>
    (subsetp-equal new-x (lit-list-fix x)))

  (defret aignet-lit-listp-of-<fn>
    (implies (aignet-lit-listp x aignet)
             (aignet-lit-listp new-x aignet))))
                                          

(define obs-sdom-info-store-intersections ((super lit-listp)
                                           (sdominfo obs-sdom-info-p)
                                           (aignet-levels)
                                           (obs-sdom-array))
  :guard (and (< (lits-max-id-val super) (sdominfo-length obs-sdom-array))
              (< (lits-max-id-val super) (u32-length aignet-levels))
              (< (lits-max-id-val (obs-sdom-info->doms sdominfo)) (u32-length aignet-levels)))
  :returns (new-obs-sdom-array)
  (b* (((when (atom super)) obs-sdom-array)
       (var (lit->var (car super)))
       (var-sdominfo (get-sdominfo var obs-sdom-array))
       (obs-sdom-array
        (set-sdominfo var
                      (obs-sdom-info-intersect
                       var-sdominfo
                       (b* (((obs-sdom-info sdominfo))
                            ((obs-sdom-info var-sdominfo)))
                         (if (and sdominfo.reached
                                  (not var-sdominfo.reached)
                                  ;; (set::in (lit-fix (car super)) sdominfo.doms)
                                  )
                             (make-obs-sdom-info-reached
                              (filter-lits-by-level
                               (get-u32 (lit->var (car super)) aignet-levels)
                               sdominfo.doms aignet-levels))
                              ;; (set::delete (lit-fix (car super)) sdominfo.doms))
                           sdominfo)))
                      obs-sdom-array)))
    (obs-sdom-info-store-intersections (cdr super) sdominfo aignet-levels obs-sdom-array))
  ///
  (defret <fn>-length
    (implies (< (lits-max-id-val super) (len obs-sdom-array))
             (equal (len new-obs-sdom-array)
                    (len obs-sdom-array))))

  (defret <fn>-index-unchanged
    (implies (not (member-equal (nfix i) (lit-list-vars super)))
             (equal (nth i new-obs-sdom-array)
                    (nth i obs-sdom-array)))
    :hints(("Goal" :in-theory (enable lit-list-vars))))

  (local (defthm obs-sdom-info-subsetp-of-filter
           (implies (obs-sdom-info->reached sdominfo)
                    (obs-sdom-info-subsetp
                     (make-obs-sdom-info-reached
                      (filter-lits-by-level lev
                                            (obs-sdom-info->doms sdominfo)
                                            aignet-levels))
                     sdominfo))
           :hints(("Goal" :in-theory (e/d (obs-sdom-info-subsetp)
                                          (subsetp-equal-of-filter-lits-by-level))
                   :use ((:instance subsetp-equal-of-filter-lits-by-level
                          (x (obs-sdom-info->doms sdominfo)) (bound lev)))))))

  (defret <fn>-index-new
    (implies (member-equal (nfix i) (lit-list-vars super))
             (obs-sdom-info-subsetp (nth i new-obs-sdom-array) sdominfo))
    :hints(("Goal" :in-theory (enable lit-list-vars)
            :induct <call>
            :do-not-induct t)))

  (defret <fn>-index-new-subsetp-of-previous
    (obs-sdom-info-subsetp (nth i new-obs-sdom-array)
                           (nth i obs-sdom-array))
    :hints(("Goal" :in-theory (enable lit-list-vars
                                      obs-sdom-info-subsetp-transitive)
            :induct <call>
            :do-not-induct t)))


  (local (defthmd obs-sdom-info-subsetp-transitive2
           (implies (and (obs-sdom-info-subsetp b c)
                         (obs-sdom-info-subsetp a b))
                    (obs-sdom-info-subsetp a c))
           :hints(("Goal" :in-theory (enable obs-sdom-info-subsetp-transitive)))))

  (local (defthm member-lit->var-of-lit-list-vars
           (implies (member k x)
                    (member (lit->var k) (lit-list-vars x)))
           :hints(("Goal" :in-theory (enable member lit-list-vars)))))

  (defret obs-sdom-fanins-ok-of-obs-sdom-info-store-intersections
    (implies (obs-sdom-fanins-ok lits fanout-sdominfo obs-sdom-array)
             (obs-sdom-fanins-ok lits fanout-sdominfo new-obs-sdom-array))
    :hints (("goal" :in-theory (enable obs-sdom-fanins-ok
                                       obs-sdom-info-subsetp-transitive2)
             :induct (obs-sdom-fanins-ok lits fanout-sdominfo obs-sdom-array))))

  (defret obs-sdom-fanins-ok-of-obs-sdom-info-store-intersections
    (implies (obs-sdom-fanins-ok lits fanout-sdominfo obs-sdom-array)
             (obs-sdom-fanins-ok lits fanout-sdominfo new-obs-sdom-array))
    :hints (("goal" :in-theory (enable obs-sdom-fanins-ok)
             :induct (obs-sdom-fanins-ok lits fanout-sdominfo obs-sdom-array))))
  
  (defret obs-sdom-fanins-ok-of-obs-sdom-info-store-intersections-self
    (implies (subsetp-equal lits super)
             (obs-sdom-fanins-ok lits sdominfo new-obs-sdom-array))
    :hints (("goal" :in-theory (enable obs-sdom-fanins-ok subsetp-equal)
             :induct (subsetp-equal lits super))))

  (local (defthm obs-sdom-info-well-formedp-of-make
           (implies (aignet-lit-listp x aignet)
                    (obs-sdom-info-well-formedp
                     (make-obs-sdom-info-reached x) aignet))
           :hints(("Goal" :in-theory (enable obs-sdom-info-well-formedp)))))

  (defret obs-sdom-array-well-formedp-of-<fn>
    (implies (and (obs-sdom-array-well-formedp obs-sdom-array aignet)
                  (obs-sdom-info-well-formedp sdominfo aignet))
             (obs-sdom-array-well-formedp new-obs-sdom-array aignet)))

  (local (defthm obs-sdom-info-intersect-nil
           (equal (obs-sdom-info-intersect nil sdominfo) nil)
           :hints(("Goal" :in-theory (enable obs-sdom-info-intersect
                                             set::intersect)))))

  (defret <fn>-preserves-empty-dominators
    (implies (equal (nth i obs-sdom-array)
                    (make-obs-sdom-info-reached nil))
             (equal (nth i new-obs-sdom-array)
                    (make-obs-sdom-info-reached nil)))))



(define obs-sdom-info-sweep-node ((n natp) obs-sdom-array refcounts aignet-levels aignet)
  :guard (and (id-existsp n aignet)
              (ec-call (obs-sdom-array-well-formedp obs-sdom-array aignet))
              (< n (sdominfo-length obs-sdom-array))
              (< n (u32-length refcounts))
              (<= (num-fanins aignet) (u32-length aignet-levels)))
  :returns new-obs-sdom-array
  (b* ((slot0 (id->slot n 0 aignet))
       (type (snode->type slot0)))
    (aignet-case
      type
      :gate (b* ((sdominfo (get-sdominfo n obs-sdom-array))
                 ((unless (obs-sdom-info->reached sdominfo))
                  obs-sdom-array)
                 (super (gate-node-supergate n refcounts aignet))
                 (xor (eql (id->regp n aignet) 1))
                 (child-sdominfo (if xor sdominfo (obs-sdom-info-add-lits super sdominfo))))
              (obs-sdom-info-store-intersections
               super child-sdominfo aignet-levels obs-sdom-array))
      :otherwise obs-sdom-array))
  ///
  (defret <fn>-length
    (implies (< (nfix n) (len obs-sdom-array))
             (equal (len new-obs-sdom-array)
                    (len obs-sdom-array))))

  (local (defthm member-lit-list-vars-when-lits-max-id-val
           (implies (< (lits-max-id-val lits) i)
                    (not (member-equal i (lit-list-vars lits))))
           :hints(("Goal" :in-theory (enable lits-max-id-val lit-list-vars)))))
  
  (defret <fn>-preserves-correct
    (implies (and (< (nfix n) (nfix i))
                  (obs-sdom-fanout-ok i obs-sdom-array refcounts aignet))
             (obs-sdom-fanout-ok i new-obs-sdom-array refcounts aignet))
    :hints(("Goal" :in-theory (enable obs-sdom-fanout-ok)
            :do-not-induct t))
    :otf-flg t)

  (defret <fn>-sets-correct
    (obs-sdom-fanout-ok n new-obs-sdom-array refcounts aignet)
    :hints(("Goal" :in-theory (enable obs-sdom-fanout-ok)
            :do-not-induct t)))

  ;; (local (defthm intersection-with-nil
  ;;          (equal (intersection-equal x nil) nil)
  ;;          :hints(("Goal" :in-theory (enable intersection-equal)))))
  (local (defthm intersect-with-nil
           (equal (set::intersect nil x) nil)
           :hints(("Goal" :use ((:instance set::double-containment
                                 (x (set::intersect nil x)) (y nil)))))))
  
  (defret <fn>-preserves-empty-dominators
    (implies (equal (nth i obs-sdom-array)
                    (make-obs-sdom-info-reached nil))
             (equal (nth i new-obs-sdom-array)
                    (make-obs-sdom-info-reached nil)))
    :hints(("Goal" :in-theory (enable obs-sdom-info-intersect))))

  (defret <fn>-preserves-well-formedp
    (implies (obs-sdom-array-well-formedp obs-sdom-array aignet)
             (obs-sdom-array-well-formedp new-obs-sdom-array aignet))))


(define obs-sdom-info-sweep-nodes ((n natp) obs-sdom-array refcounts aignet-levels aignet)
  :guard (and (<= n (num-fanins aignet))
              (<= n (sdominfo-length obs-sdom-array))
              (<= n (u32-length refcounts))
              (ec-call (obs-sdom-array-well-formedp obs-sdom-array aignet))
              (<= (num-fanins aignet) (u32-length aignet-levels)))
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  :returns new-obs-sdom-array
  (b* (((when (zp n))
        obs-sdom-array)
       (obs-sdom-array (obs-sdom-info-sweep-node (1- n) obs-sdom-array refcounts aignet-levels aignet)))
    (obs-sdom-info-sweep-nodes (1- n) obs-sdom-array refcounts aignet-levels aignet))
  ///
  (defret <fn>-length
    (implies (<= (nfix n) (len obs-sdom-array))
             (equal (len new-obs-sdom-array)
                    (len obs-sdom-array))))

  (defret <fn>-preserves-correct
    (implies (and (<= (nfix n) (nfix i))
                  (obs-sdom-fanout-ok i obs-sdom-array refcounts aignet))
             (obs-sdom-fanout-ok i new-obs-sdom-array refcounts aignet)))

  (defret <fn>-sets-correct
    (implies (< (nfix i) (nfix n))
             (obs-sdom-fanout-ok i new-obs-sdom-array refcounts aignet)))
  
  (defret <fn>-preserves-empty-dominators
    (implies (equal (nth i obs-sdom-array)
                    (make-obs-sdom-info-reached nil))
             (equal (nth i new-obs-sdom-array)
                    (make-obs-sdom-info-reached nil)))
    :hints(("Goal" :in-theory (enable obs-sdom-info-intersect))))

  (defret <fn>-preserves-well-formedp
    (implies (obs-sdom-array-well-formedp obs-sdom-array aignet)
             (obs-sdom-array-well-formedp new-obs-sdom-array aignet))))


(define obs-sdom-info-set-pos ((n natp) obs-sdom-array aignet)
  :guard (and (<= n (num-outs aignet))
              (<= (num-fanins aignet) (sdominfo-length obs-sdom-array)))
  :measure (nfix n)
  :returns new-obs-sdom-array
  (b* (((when (zp n))
        obs-sdom-array)
       (fanin-node (lit->var (outnum->fanin (1- n) aignet)))
       (obs-sdom-array (set-sdominfo fanin-node (make-obs-sdom-info-reached nil) obs-sdom-array)))
    (obs-sdom-info-set-pos (1- n) obs-sdom-array aignet))
  ///
  (defret <fn>-length
    (implies (< (fanin-count aignet) (len obs-sdom-array))
             (equal (len new-obs-sdom-array)
                    (len obs-sdom-array))))

  (defret <fn>-preserves-empty-dominators
    (implies (equal (nth i obs-sdom-array)
                    (make-obs-sdom-info-reached nil))
             (equal (nth i new-obs-sdom-array)
                    (make-obs-sdom-info-reached nil))))

  (defret fanin-sdominfo-of-<fn>
    (implies (< (nfix k) (nfix n))
             (equal (nth (lit->var (fanin 0 (lookup-stype k :po aignet))) new-obs-sdom-array)
                    (make-obs-sdom-info-reached nil))))

  (defret <fn>-preserves-well-formedp
    (implies (obs-sdom-array-well-formedp obs-sdom-array aignet)
             (obs-sdom-array-well-formedp new-obs-sdom-array aignet))))

(define obs-sdom-info-set-nxsts ((n natp) obs-sdom-array aignet)
  :guard (and (<= n (num-regs aignet))
              (<= (num-fanins aignet) (sdominfo-length obs-sdom-array)))
  :measure (nfix n)
  :returns new-obs-sdom-array
  (b* (((when (zp n))
        obs-sdom-array)
       (fanin-node (lit->var (regnum->nxst (1- n) aignet)))
       (obs-sdom-array (set-sdominfo fanin-node (make-obs-sdom-info-reached nil) obs-sdom-array)))
    (obs-sdom-info-set-nxsts (1- n) obs-sdom-array aignet))
  ///
  (defret <fn>-length
    (implies (< (fanin-count aignet) (len obs-sdom-array))
             (equal (len new-obs-sdom-array)
                    (len obs-sdom-array))))

  (defret <fn>-preserves-empty-dominators
    (implies (equal (nth i obs-sdom-array)
                    (make-obs-sdom-info-reached nil))
             (equal (nth i new-obs-sdom-array)
                    (make-obs-sdom-info-reached nil))))

  (defret fanin-sdominfo-of-<fn>
    (implies (< (nfix k) (nfix n))
             (equal (nth (lit->var (lookup-reg->nxst k aignet)) new-obs-sdom-array)
                    (make-obs-sdom-info-reached nil))))

  (defret <fn>-preserves-well-formedp
    (implies (obs-sdom-array-well-formedp obs-sdom-array aignet)
             (obs-sdom-array-well-formedp new-obs-sdom-array aignet))))


(define aignet-compute-obs-sdom-info (obs-sdom-array refcounts aignet-levels aignet)
  :returns new-obs-sdom-array
  :guard (and (<= (num-fanins aignet) (u32-length refcounts))
              (<= (num-fanins aignet) (u32-length aignet-levels)))
  (b* ((obs-sdom-array (resize-sdominfo 0 obs-sdom-array))
       (obs-sdom-array (resize-sdominfo (num-fanins aignet) obs-sdom-array))
       (obs-sdom-array (obs-sdom-info-set-pos (num-outs aignet) obs-sdom-array aignet))
       (obs-sdom-array (obs-sdom-info-set-nxsts (num-regs aignet) obs-sdom-array aignet)))
    (obs-sdom-info-sweep-nodes (num-fanins aignet) obs-sdom-array refcounts aignet-levels aignet))
  ///
  (defret <fn>-length
    (equal (len new-obs-sdom-array) (num-fanins aignet)))

  (defret po-sdominfo-of-<fn>
    (implies (< (nfix k) (num-outs aignet))
             (equal (nth (lit->var (fanin 0 (lookup-stype k :po aignet))) new-obs-sdom-array)
                    (make-obs-sdom-info-reached nil))))

  (defret nxst-sdominfo-of-<fn>
    (implies (< (nfix k) (num-regs aignet))
             (equal (nth (lit->var (lookup-reg->nxst k aignet)) new-obs-sdom-array)
                    (make-obs-sdom-info-reached nil))))

  (defret <fn>-fanouts-ok
    (obs-sdom-fanout-ok i new-obs-sdom-array refcounts aignet)
    :hints(("Goal" :in-theory (enable obs-sdom-fanout-ok-out-of-bounds)
            :cases ((< (nfix i) (+ 1 (fanin-count aignet)))))))

  (defret well-formedp-of-<fn>
    (obs-sdom-array-well-formedp new-obs-sdom-array aignet)))

(define aignet-compute-obs-sdom-info-n-outputs ((n natp) obs-sdom-array refcounts aignet-levels aignet)
  :returns new-obs-sdom-array
  :guard (and (<= n (num-outs aignet))
              (<= (num-fanins aignet) (u32-length refcounts))
              (<= (num-fanins aignet) (u32-length aignet-levels)))
  (b* ((obs-sdom-array (resize-sdominfo 0 obs-sdom-array))
       (obs-sdom-array (resize-sdominfo (num-fanins aignet) obs-sdom-array))
       (obs-sdom-array (obs-sdom-info-set-pos n obs-sdom-array aignet)))
    (obs-sdom-info-sweep-nodes (num-fanins aignet) obs-sdom-array refcounts aignet-levels aignet))
  ///
  (defret <fn>-length
    (equal (len new-obs-sdom-array) (num-fanins aignet)))

  (defret po-sdominfo-of-<fn>
    (implies (< (nfix k) (nfix n))
             (equal (nth (lit->var (fanin 0 (lookup-stype k :po aignet))) new-obs-sdom-array)
                    (make-obs-sdom-info-reached nil))))

  (defret <fn>-fanouts-ok
    (obs-sdom-fanout-ok i new-obs-sdom-array refcounts aignet)
    :hints(("Goal" :in-theory (enable obs-sdom-fanout-ok-out-of-bounds)
            :cases ((< (nfix i) (+ 1 (fanin-count aignet)))))))

  (defret well-formedp-of-<fn>
    (obs-sdom-array-well-formedp new-obs-sdom-array aignet)))



(defsection obs-sdom-array-correct
  
  (defun-sk obs-sdom-array-correct (obs-sdom-array refcounts aignet)
    (forall fanout
            (obs-sdom-fanout-ok fanout obs-sdom-array refcounts aignet))
    :rewrite :direct)

  (in-theory (disable obs-sdom-array-correct))

  (defthm obs-sdom-array-correct-of-obs-sdom-info-sweep-nodes
    (obs-sdom-array-correct
     (obs-sdom-info-sweep-nodes (+ 1 (fanin-count aignet)) obs-sdom-array refcounts aignet-levels aignet)
     refcounts
     aignet)
    :hints(("Goal" :in-theory (enable obs-sdom-array-correct
                                      obs-sdom-fanout-ok-out-of-bounds)
            :cases ((<= (nfix
                         (obs-sdom-array-correct-witness
                          (obs-sdom-info-sweep-nodes (+ 1 (fanin-count aignet)) 
                                                    obs-sdom-array refcounts aignet-levels aignet)
                          refcounts
                          aignet))
                        (fanin-count aignet))))))

  (defthm obs-sdom-array-correct-of-aignet-compute-obs-sdom-info
    (obs-sdom-array-correct (aignet-compute-obs-sdom-info obs-sdom-array refcounts aignet-levels aignet)
                           refcounts aignet)
    :hints(("Goal" :in-theory (enable obs-sdom-array-correct))))

  (defthm obs-sdom-array-correct-of-aignet-compute-obs-sdom-info-n-outputs
    (obs-sdom-array-correct (aignet-compute-obs-sdom-info-n-outputs n obs-sdom-array refcounts aignet-levels aignet)
                           refcounts aignet)
    :hints(("Goal" :in-theory (enable obs-sdom-array-correct)))))





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



(defsection obs-sdom-array-implies-path-contains-dominators
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


     (defthm obs-sdom-fanout-ok-implies-reachable-and
       (implies (and (obs-sdom-fanout-ok fanout obs-sdom-array refcounts aignet)
                     (equal (stype (car (lookup-id fanout aignet))) :and)
                     (obs-sdom-info->reached (nth fanout obs-sdom-array))
                     (not (cube-contradictionp
                           (obs-sdom-info->doms (nth fanout obs-sdom-array))))
                     (not (cube-contradictionp (gate-node-supergate fanout refcounts aignet)))
                     (not (two-cubes-contradictionp
                           (obs-sdom-info->doms (nth fanout obs-sdom-array))
                           (gate-node-supergate fanout refcounts aignet)))
                     (< (nfix k) (len (gate-node-supergate fanout refcounts aignet))))
                (obs-sdom-info->reached (nth (lit->var
                                             (nth k (gate-node-supergate fanout refcounts aignet)))
                                            obs-sdom-array)))
       :hints(("Goal" :in-theory (e/d (obs-sdom-info-for-child
                                       obs-sdom-info-add-lits
                                       obs-sdom-info-subsetp
                                       cube-contradictionp-of-append)
                                      (obs-sdom-fanout-ok-implies-and-child))
               :expand ((:free (a b) (cube-contradictionp (cons a b))))
               :use ((:instance obs-sdom-fanout-ok-implies-and-child
                      (lit (nth k (gate-node-supergate fanout refcounts aignet))))))))

     (defthm obs-sdom-fanout-ok-implies-reachable-xor
       (implies (and (obs-sdom-fanout-ok fanout obs-sdom-array refcounts aignet)
                     (equal (stype (car (lookup-id fanout aignet))) :xor)
                     (obs-sdom-info->reached (nth fanout obs-sdom-array))
                     (not (cube-contradictionp
                           (obs-sdom-info->doms (nth fanout obs-sdom-array))))
                     (< (nfix k) (len (gate-node-supergate fanout refcounts aignet)))
                     ;; (not (member-equal
                     ;;       (lit-negate (fanin (b-not dir)
                     ;;                          (lookup-id fanout aignet)))
                     ;;       (obs-sdom-info->doms (nth fanout obs-sdom-array))))
                     )
                (obs-sdom-info->reached (nth (lit->var
                                             (nth k (gate-node-supergate fanout refcounts aignet)))
                                            obs-sdom-array)))
       :hints(("Goal" :in-theory (e/d (obs-sdom-info-for-child
                                       obs-sdom-info-add-lits
                                       obs-sdom-info-subsetp
                                       cube-contradictionp-of-append)
                                      (obs-sdom-fanout-ok-implies-xor-child))
               :expand ((:free (a b) (cube-contradictionp (cons a b))))
               :use ((:instance obs-sdom-fanout-ok-implies-xor-child
                      (lit (nth k (gate-node-supergate fanout refcounts aignet))))))))



     (defthm subsetp-of-doms-when-reached
       (implies (and (obs-sdom-info-subsetp x y)
                     (obs-sdom-info->reached y)
                     (not (cube-contradictionp
                           (obs-sdom-info->doms y))))
                (subsetp (obs-sdom-info->doms x) (obs-sdom-info->doms y)))
       :hints(("Goal" :in-theory (enable obs-sdom-info-subsetp))))

     ;; (defthm path-contains-and-siblings-when-subsetp
     ;;   (implies (and (path-contains-and-siblings x sink path aignet)
     ;;                 (subsetp y x))
     ;;            (path-contains-and-siblings y sink path aignet))
     ;;   :hints(("Goal" :in-theory (enable path-contains-and-siblings subsetp)
     ;;           :induct (path-contains-and-siblings y sink path aignet)
     ;;           :expand ((path-contains-and-siblings y sink path aignet)
     ;;                    (subsetp y x)))))


     (defthm obs-sdom-fanout-ok-implies-subsetp-xor
       (implies (and (obs-sdom-fanout-ok fanout obs-sdom-array refcounts aignet)
                     (equal (stype (car (lookup-id fanout aignet))) :xor)
                     (obs-sdom-info->reached (nth fanout obs-sdom-array))
                     (not (cube-contradictionp
                           (obs-sdom-info->doms (nth fanout obs-sdom-array))))
                     (< (nfix k) (len (gate-node-supergate fanout refcounts aignet))))
                (subsetp (obs-sdom-info->doms
                          (nth (lit->var
                                (nth k (gate-node-supergate fanout refcounts aignet)))
                               obs-sdom-array))
                         (obs-sdom-info->doms
                          (nth fanout obs-sdom-array))))
       :hints (("goal" :use ((:instance obs-sdom-fanout-ok-implies-xor-child
                              (lit (nth k (gate-node-supergate fanout refcounts aignet)))))
                :in-theory (e/d (obs-sdom-info-for-child)
                                (obs-sdom-fanout-ok-implies-xor-child)))))

     (defthm obs-sdom-fanout-ok-implies-subsetp-and
       (implies (and (obs-sdom-fanout-ok fanout obs-sdom-array refcounts aignet)
                     (equal (stype (car (lookup-id fanout aignet))) :and)
                     (obs-sdom-info->reached (nth fanout obs-sdom-array))
                     (not (cube-contradictionp
                           (obs-sdom-info->doms (nth fanout obs-sdom-array))))
                     (not (cube-contradictionp (gate-node-supergate fanout refcounts aignet)))
                     (not (two-cubes-contradictionp
                           (obs-sdom-info->doms (nth fanout obs-sdom-array))
                           (gate-node-supergate fanout refcounts aignet)))
                     (< (nfix k) (len (gate-node-supergate fanout refcounts aignet))))
                (subsetp (obs-sdom-info->doms
                          (nth (lit->var
                                (nth k (gate-node-supergate fanout refcounts aignet)))
                               obs-sdom-array))
                         (append (obs-sdom-info->doms (nth fanout obs-sdom-array))
                                 (gate-node-supergate fanout refcounts aignet))))
       :hints(("Goal" :in-theory (e/d (obs-sdom-info-for-child
                                       obs-sdom-info-add-lits
                                       obs-sdom-info-subsetp
                                       cube-contradictionp-of-append)
                                      (obs-sdom-fanout-ok-implies-and-child))
               :expand ((:free (a b) (cube-contradictionp (cons a b))))
               :use ((:instance obs-sdom-fanout-ok-implies-and-child
                      (lit (nth k (gate-node-supergate fanout refcounts aignet))))))))

     (defthm obs-sdom-fanout-ok-implies-subsetp-and-rw
       (implies (and (obs-sdom-fanout-ok fanout obs-sdom-array refcounts aignet)
                     (equal (stype (car (lookup-id fanout aignet))) :and)
                     (obs-sdom-info->reached (nth fanout obs-sdom-array))
                     (not (cube-contradictionp
                           (obs-sdom-info->doms (nth fanout obs-sdom-array))))
                     (not (cube-contradictionp (gate-node-supergate fanout refcounts aignet)))
                     (not (two-cubes-contradictionp
                           (obs-sdom-info->doms (nth fanout obs-sdom-array))
                           (gate-node-supergate fanout refcounts aignet)))
                     (< (nfix k) (len (gate-node-supergate fanout refcounts aignet)))
                     (subsetp
                      (append (obs-sdom-info->doms (nth fanout obs-sdom-array))
                              (gate-node-supergate fanout refcounts aignet))
                      full-set))
                (subsetp (obs-sdom-info->doms
                          (nth (lit->var
                                (nth k (gate-node-supergate fanout refcounts aignet)))
                               obs-sdom-array))
                         full-set))
       :hints (("goal" :use obs-sdom-fanout-ok-implies-subsetp-and
                :in-theory (disable obs-sdom-fanout-ok-implies-subsetp-and))))
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

  (defthm obs-sdom-array-implies-path-contains-dominators
    (b* ((path-lits (spath-and-literals sink path refcounts aignet)))
      (implies (and (obs-sdom-array-correct obs-sdom-array refcounts aignet)
                    (spath-existsp sink path refcounts aignet)
                    (not (cube-contradictionp path-lits))
                    (obs-sdom-info->reached (nth sink obs-sdom-array))
                    (equal (obs-sdom-info->doms (nth sink obs-sdom-array)) nil))
               (let ((source (spath-endpoint sink path refcounts aignet)))
                 (and (obs-sdom-info->reached (nth source obs-sdom-array))
                      (subsetp
                       (obs-sdom-info->doms (nth source obs-sdom-array)) path-lits)))))
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



(defthm toggle-does-not-affect-sink-when-sdom-info-not-reached
  (implies (and (obs-sdom-array-correct obs-sdom-array refcounts aignet)
                (not (obs-sdom-info->reached (nth source obs-sdom-array)))
                (obs-sdom-info->reached (nth sink obs-sdom-array))
                (equal (obs-sdom-info->doms (nth sink obs-sdom-array)) nil)
                (< 1 (nfix (nth source refcounts)))
                (ids-multiply-referenced toggles refcounts))
           (equal (id-eval-toggle sink (cons source toggles) invals regvals aignet)
                  (id-eval-toggle sink toggles invals regvals aignet)))
  :hints (("goal" :use ((:instance obs-sdom-array-implies-path-contains-dominators
                         (path (toggle-witness-spath sink source toggles invals regvals refcounts aignet))))
           :in-theory (disable obs-sdom-array-implies-path-contains-dominators))))



(defthm toggle-does-not-affect-output-when-sdom-false
  (implies (and (obs-sdom-array-correct obs-sdom-array refcounts aignet)
                (member-equal lit (obs-sdom-info->doms (nth source obs-sdom-array)))
                (equal (lit-eval-toggle lit toggles invals regvals aignet) 0)
                (equal (lit-eval-toggle lit (cons source toggles) invals regvals aignet) 0)
                (obs-sdom-info->reached (nth sink obs-sdom-array))
                (equal (obs-sdom-info->doms (nth sink obs-sdom-array)) nil)
                (< 1 (nfix (nth source refcounts)))
                (ids-multiply-referenced toggles refcounts))
           (equal (id-eval-toggle sink (cons source toggles) invals regvals aignet)
                  (id-eval-toggle sink toggles invals regvals aignet)))
  :hints (("goal" :use ((:instance obs-sdom-array-implies-path-contains-dominators
                         (path (toggle-witness-spath sink source toggles invals regvals refcounts aignet)))
                        (:instance lit-list-has-const0-under-toggle-when-member
                         (x (spath-and-literals
                             sink
                             (toggle-witness-spath sink source toggles invals regvals refcounts aignet)
                             refcounts aignet))
                         (toggle source)))
           :in-theory (disable obs-sdom-array-implies-path-contains-dominators
                               lit-list-has-const0-under-toggle-when-member))))


(define obs-sdom-array-collect ((n natp) obs-sdom-array)
  :guard (<= n (sdominfo-length obs-sdom-array))
  :measure (nfix (- (sdominfo-length obs-sdom-array) (nfix n)))
  (b* (((when (mbe :logic (zp (- (sdominfo-length obs-sdom-array) (nfix n)))
                   :exec (eql (sdominfo-length obs-sdom-array) n)))
        nil))
    (cons (get-sdominfo n obs-sdom-array)
          (obs-sdom-array-collect (1+ (lnfix n)) obs-sdom-array))))





