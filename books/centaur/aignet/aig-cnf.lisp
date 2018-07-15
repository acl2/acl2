; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
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

;; mechanism for transforming AIG -> AIGNET -> CNF and showing them
;; equisatisfiable

;; To find the major theorems in this book, search for "induces" -- there are
;; four of them

(in-package "AIGNET")

(include-book "cnf")
(include-book "from-hons-aig")
(include-book "refcounts")
(include-book "centaur/aig/accumulate-nodes-vars" :dir :system)
(local (include-book "centaur/satlink/cnf-basics" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))
(local (include-book "centaur/aig/eval-restrict" :dir :system)) ;; for congruences
(local (in-theory (e/d (aiglist-to-aignet)
                       (create-sat-lits
                        (create-sat-lits)
                        resize-aignet->sat
                        nth update-nth
                        acl2::make-list-ac-redef
                        make-list-ac
                        aignet-count-refs
                        acl2::nth-with-large-index
                        (aignet-clear)
                        aignet-lit->cnf))))


(define aignet-one-lit->cnf ((lit litp)
                             sat-lits aignet)
  :guard (fanin-litp lit aignet)
  :returns (mv (cnf satlink::lit-list-listp)
               (sat-lits (sat-lits-wfp sat-lits aignet)))
  (b* ((sat-lits (sat-lits-empty (num-nodes aignet) sat-lits))
       ((when (eql (mbe :logic (lit-fix lit) :exec lit) 1))
        ;; true -- empty cnf
        (mv nil sat-lits))
       ((when (eql (mbe :logic (lit-fix lit) :exec lit) 0))
        ;; false -- empty clause
        (mv '(nil) sat-lits))
       ((local-stobjs aignet-refcounts)
        (mv cnf sat-lits aignet-refcounts))
       (aignet-refcounts (resize-u32 (num-nodes aignet) aignet-refcounts))
       (aignet-refcounts (aignet-count-refs aignet-refcounts aignet))
       ((mv sat-lits cnf)
        (aignet-lit->cnf lit t aignet-refcounts sat-lits aignet nil))
       (sat-lit (aignet-lit->sat-lit lit sat-lits)))
    (mv (list* (list sat-lit) ;; lit is true
               cnf)
        sat-lits aignet-refcounts))
  ///
  (defthm aignet-one-lit->cnf-normalize-sat-lits
    (implies (syntaxp (not (equal sat-lits ''nil)))
             (equal (aignet-one-lit->cnf lit sat-lits aignet)
                    (aignet-one-lit->cnf lit nil aignet))))


  (local (in-theory (e/d (satlink-eval-lit-of-make-lit-of-lit-var)
                         (satlink::eval-lit-of-make-lit))))

  ;; (local (defthm lit-when-var-and-neg-known
  ;;          (implies (and (syntaxp (quotep var))
  ;;                        (natp var)
  ;;                        (syntaxp (or (acl2::rewriting-negative-literal-fn
  ;;                                      `(equal (satlink::lit->var$inline ,lit) ,var)
  ;;                                      mfc state)
  ;;                                     (acl2::rewriting-negative-literal-fn
  ;;                                      `(equal ,var (satlink::lit->var$inline ,lit))
  ;;                                      mfc state)))
  ;;                        (equal (lit->neg lit) neg)
  ;;                        (syntaxp (quotep neg)))
  ;;                   (equal (equal (lit->var lit) var)
  ;;                          (lit-equiv lit (make-lit var neg))))))

  ;; (local (in-theory (disable satlink::equal-of-lit-fix-hyp)))
                         

  (defthm aignet-satisfying-assign-induces-cnf-satisfying-assign
    (b* (((mv cnf sat-lits) (aignet-one-lit->cnf lit sat-lits aignet))
         (cnf-vals (aignet->cnf-vals invals regvals cnf-vals sat-lits aignet)))
      (implies (and (aignet-litp lit aignet)
                    (sat-lits-wfp sat-lits aignet))
               (equal (satlink::eval-formula cnf cnf-vals)
                      (lit-eval lit invals regvals aignet))))
    :hints(("Goal" :in-theory (e/d ()
                                   (cnf-for-aignet-implies-cnf-sat-when-lit-sat))
            :use ((:instance cnf-for-aignet-implies-cnf-sat-when-lit-sat
                   (cnf-vals cnf-vals)
                   (cnf (cdr (mv-nth 0 (aignet-one-lit->cnf lit sat-lits aignet))))
                   (sat-lits (mv-nth 1 (aignet-one-lit->cnf lit sat-lits aignet))))))))




  (defthm cnf-satisfying-assign-induces-aignet-satisfying-assign
    (b* (((mv cnf sat-lits) (aignet-one-lit->cnf lit sat-lits aignet))
         (invals (cnf->aignet-invals invals cnf-vals sat-lits aignet))
         (regvals (cnf->aignet-regvals regvals cnf-vals sat-lits aignet)))
      (implies (and (aignet-litp lit aignet)
                    (equal (satlink::eval-formula cnf cnf-vals) 1))
               (equal (lit-eval lit invals regvals aignet)
                      1)))
    :hints (("goal" :use ((:instance
                           cnf-for-aignet-implies-lit-sat-when-cnf-sat
                           (cnf (cdr (mv-nth 0 (aignet-one-lit->cnf lit sat-lits aignet))))
                           (sat-lits (mv-nth 1 (aignet-one-lit->cnf lit sat-lits aignet)))
                           (cnf-vals cnf-vals)))
             :in-theory (e/d ()
                             (aignet-lit->cnf
                              cnf-for-aignet-implies-lit-sat-when-cnf-sat))))))



(defthm good-varmap-p-of-nil
  (good-varmap-p nil x)
  :hints(("Goal" :in-theory (enable good-varmap-p))))

(local (defthmd equal-of-hons-assoc-equal
             (equal (equal (hons-assoc-equal k x) y)
                    (if (hons-assoc-equal k x)
                        (and (consp y)
                             (equal (car y) k)
                             (equal (cdr y) (cdr (hons-assoc-equal k x))))
                      (not y)))
             :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

(define aig->aignet (aig aignet &key ((gatesimp gatesimp-p) '(default-gatesimp)))
  :returns (mv (vars "variables from the hons aig, as ordered in the aignet")
               new-aignet)
  (b* (((local-stobjs strash)
        (mv vars aignet strash))
       (aiglist (list aig))
       (vars (acl2::aig-vars-unordered-list aiglist))
       (aignet (aignet-clear aignet))
       (aignet (aignet-add-ins (len vars) aignet))
       (varmap (consecutive-vars-to-varmap 1 vars nil))
       (strash (strashtab-init 100 nil nil strash))
       ((mv lits strash aignet)
        (aiglist-to-aignet-top aiglist varmap gatesimp strash aignet))
       (aignet (aignet-add-out (car lits) aignet)))
    (fast-alist-free varmap)
    (mv vars aignet strash))
  ///
  (defthm normalize-aig->aignet
    (implies (syntaxp (not (equal aignet ''nil)))
             (equal (aig->aignet aig aignet :gatesimp gatesimp)
                    (aig->aignet aig nil :gatesimp gatesimp))))

  (defret num-outs-of-aig->aignet
    (equal (stype-count :po new-aignet) 1))

  (defret num-regs-of-aig->aignet
    (equal (stype-count :reg new-aignet) 0))

  (defret num-nxsts-of-aig->aignet
    (equal (stype-count :nxst new-aignet) 0))

  (defret num-ins-of-aig->aignet
    (equal (stype-count :pi new-aignet)
           (len (acl2::aig-vars-unordered-list (list aig)))))

  ;; (defret aignet-nodes-ok-aig->aignet
  ;;   (aignet-nodes-ok new-aignet))

  (local (defthm acl2-numberp-of-index-of-when-member
             (implies (member x lst)
                      (acl2-numberp (acl2::index-of x lst)))
             :hints(("Goal" :in-theory (enable acl2::index-of member)))))

  (local (defthm aignet-eval-to-env-of-consecutive-vars-to-varmap
           (implies (and (no-duplicatesp vars)
                         (acl2::aig-var-listp vars))
                    (acl2::alist-equiv (aignet-eval-to-env
                                        (consecutive-vars-to-varmap 1 vars nil)
                                        invals regvals
                                        (aignet-add-ins (len vars) nil))
                                       (aignet-bitarr-to-aig-env vars invals)))
           :hints (("goal" :in-theory (enable acl2::alist-equiv-iff-agree-on-bad-guy
                                              equal-of-hons-assoc-equal)
                    :do-not-induct t))))

  (defret eval-output-of-aig->aignet
    (equal (output-eval 0 invals regvals new-aignet)
           (acl2::bool->bit (aig-eval aig (aignet-bitarr-to-aig-env vars invals))))
    :hints(("Goal" :in-theory (enable lookup-stype output-eval)
            :expand ((:free (n aignet) (id-eval (+ 1 n) invals regvals aignet)))
            :do-not-induct t)))

  (defret vars-of-aig->aignet
    (equal vars
           (acl2::aig-vars-unordered-list (list aig)))))

(local (defthm lit-eval-of-fanin-equals-output-eval
         (implies (< (nfix n) (stype-count :po aignet))
                  (equal (lit-eval (fanin :co (lookup-stype n :po aignet))
                                   invals regvals aignet)
                         (output-eval n invals regvals aignet)))
         :hints(("Goal" :in-theory (enable output-eval)
                 :expand ((:free (invals regvals aignet)
                           (id-eval (node-count (lookup-stype n :po aignet))
                                    invals regvals aignet)))))))

(encapsulate
  (((aig->cnf-aignet-transform aignet *) => aignet
    :guard t :formals (aignet config)))

  (local (defun aig->cnf-aignet-transform (aignet config)
           (Declare (xargs :guard t :stobjs aignet)
                    (ignore config))
           aignet))

  (defthm comb-equiv-of-aig->cnf-aignet-transform
    (comb-equiv (aig->cnf-aignet-transform aignet config)
                aignet))

  (defthm num-ins-of-aig->cnf-aignet-transform
    (equal (stype-count :pi (aig->cnf-aignet-transform aignet config))
           (stype-count :pi aignet)))

  (defthm num-outs-of-aig->cnf-aignet-transform
    (equal (stype-count :po (aig->cnf-aignet-transform aignet config))
           (stype-count :po aignet)))

  (defthm num-regs-of-aig->cnf-aignet-transform
    (equal (stype-count :reg (aig->cnf-aignet-transform aignet config))
           (stype-count :reg aignet))))

(defun aig->cnf-default-aignet-transform (aignet config)
  (declare (xargs :guard t :stobjs aignet)
           (ignore config))
  aignet)

(defattach aig->cnf-aignet-transform aig->cnf-default-aignet-transform)

(define aig->cnf-aignet-transform-wrapper (aignet config)
  :returns (new-aignet)
  (if config
      (aig->cnf-aignet-transform aignet config)
    aignet)
  ///
  
  (defret comb-equiv-of-aig->cnf-aignet-transform-wrapper
    (comb-equiv new-aignet
                aignet))

  (defret num-ins-of-aig->cnf-aignet-transform-wrapper
    (equal (stype-count :pi new-aignet)
           (stype-count :pi aignet)))

  (defret num-outs-of-aig->cnf-aignet-transform-wrapper
    (equal (stype-count :po new-aignet)
           (stype-count :po aignet)))

  (defret num-regs-of-aig->cnf-aignet-transform-wrapper
    (equal (stype-count :reg new-aignet)
           (stype-count :reg aignet))))

(define aig->cnf (aig sat-lits aignet &key (transform-config 'nil) ((gatesimp gatesimp-p) '(default-gatesimp)))
  :returns (mv (cnf satlink::lit-list-listp)
               (lit litp)
               (vars "variables from the hons aig, as ordered in the aignet")
               new-sat-lits
               new-aignet)
  :guard-hints (("goal" :in-theory (enable lookup-stype-in-bounds)))
  (b* (((mv vars aignet) (aig->aignet aig aignet :gatesimp gatesimp))
       (aignet (aig->cnf-aignet-transform-wrapper aignet transform-config))
       (aignet-lit (co-id->fanin (outnum->id 0 aignet) aignet))
       ((mv cnf sat-lits)
        (aignet-one-lit->cnf aignet-lit sat-lits aignet)))
    (mv cnf aignet-lit vars sat-lits aignet))

  ///

  (defret aignet-litp-of-aig->cnf
    (aignet-litp lit new-aignet)
    :hints(("Goal" :in-theory (enable lookup-stype-in-bounds))))

  (defthm normalize-aig->cnf-aignet
    (implies (syntaxp (not (equal aignet ''nil)))
             (equal (aig->cnf aig sat-lits aignet :transform-config transform-config :gatesimp gatesimp)
                    (aig->cnf aig sat-lits nil :transform-config transform-config :gatesimp gatesimp))))

  (defthm normalize-aig->cnf-sat-lits
    (implies (syntaxp (not (equal sat-lits ''nil)))
             (equal (aig->cnf aig sat-lits aignet :transform-config transform-config :gatesimp gatesimp)
                    (aig->cnf aig nil aignet :transform-config transform-config :gatesimp gatesimp))))

  ;; (defthm aignet-nodes-ok-aig->cnf
  ;;   (aignet-nodes-ok (mv-nth 4 (aig->cnf aig sat-lits aignet :transform-config transform-config)))
  ;;   :hints(("Goal" :in-theory (enable aig->cnf))))

  (defret sat-lits-wfp-of-aig->cnf
    (sat-lits-wfp new-sat-lits new-aignet)
    :hints(("Goal" :in-theory (enable aig->cnf))))

  (defret eval-lit-of-aig->aignet
    (equal (lit-eval lit invals regvals new-aignet)
           (acl2::bool->bit (aig-eval aig (aignet-bitarr-to-aig-env vars invals))))
    :hints(("Goal" :use (eval-output-of-aig->aignet)
            :in-theory (disable eval-output-of-aig->aignet)
            :expand ((:free (aignet aignet2)
                      (id-eval (node-count (lookup-stype 0 :po aignet))
                               invals regvals aignet2))))))

  (defret vars-of-aig->cnf
    (equal vars
           (acl2::aig-vars-unordered-list (list aig))))

  (defret num-outs-of-aig->cnf
    (equal (stype-count :po new-aignet) 1))

  (defret num-regs-of-aig->cnf
    (equal (stype-count :reg new-aignet) 0))

  ;; (defret num-nxsts-of-aig->cnf
  ;;   (equal (stype-count :nxst new-aignet) 0))

  (defret num-ins-of-aig->cnf
    (equal (stype-count :pi new-aignet)
           (len (acl2::aig-vars-unordered-list (list aig))))))





(defun satisfying-assign-for-env (env vars sat-lits aignet cnf-vals)
  (declare (xargs :stobjs (sat-lits aignet cnf-vals)
                  :guard (sat-lits-wfp sat-lits aignet)))
  (b* ((in-vals (env-to-bitarr vars env))
       (cnf-vals (resize-bits 0 cnf-vals))
       (cnf-vals (resize-bits (sat-next-var sat-lits) cnf-vals))
       (cnf-vals (non-exec
                  (b* ((cnf-vals (aignet->cnf-vals in-vals nil cnf-vals sat-lits aignet)))
                    cnf-vals))))
    cnf-vals))


;; (defthm lookup-in-make-varmap-iff
;;   (iff (hons-assoc-equal v (mv-nth 0 (make-varmap vars nil varmap0 aignet0)))
;;        (or (member v vars)
;;            (hons-assoc-equal v varmap0)))
;;   :hints(("Goal" :in-theory (enable make-varmap))))



;; (defun lst-position (x lst)
;;   (cond ((endp lst) nil)
;;         ((equal x (car lst)) 0)
;;         (t (let ((rst (lst-position x (cdr lst))))
;;              (and rst (+ 1 rst))))))

;; (defthm lst-position-iff-member
;;   (iff (lst-position x lst)
;;        (member x lst)))

(local (include-book "arithmetic/top-with-meta" :dir :system))

;; (defthm lookup-in-make-varmap
;;   (implies (and (no-duplicatesp vars)
;;                 (not (intersectp-equal vars (alist-keys varmap0))))
;;            (equal (cdr (hons-assoc-equal v (mv-nth 0 (make-varmap vars nil varmap0
;;                                                                   aignet0))))
;;                   (if (member v vars)
;;                       (mk-lit (+ (lst-position v vars)
;;                                  (num-nodes aignet0))
;;                               0)
;;                     (cdr (hons-assoc-equal v varmap0)))))
;;   :hints(("Goal" :in-theory (enable make-varmap
;;                                     intersectp-equal
;;                                     alist-keys)
;;           :induct (make-varmap vars nil varmap0 aignet0))))



(local (in-theory (enable (:i aig-to-aignet))))



(encapsulate nil
  ;; (local
  ;;  (defthm aignet-idp-in-make-varmap
  ;;    (implies (and (natp id)
  ;;                  (force (< (nfix id) (+ (num-nodes aignet0)
  ;;                                           (len vars)))))
  ;;             (aignet-idp id (mv-nth 1 (make-varmap vars regp varmap0 aignet0))))
  ;;    :hints(("Goal" :in-theory (enable make-varmap)
  ;;            :induct (make-varmap vars regp varmap0 aignet0))
  ;;           (and stable-under-simplificationp
  ;;                '(:in-theory (enable aignet-idp))))))

  ;; (local
  ;;  (defthm aignet-idp-of-aignet-add-reg
  ;;    (implies (and (idp id)
  ;;                  (<= (id-val id) (num-nodes aignet)))
  ;;             (aignet-idp id (mv-nth 1 (Aignet-add-reg aignet))))
  ;;    :hints(("Goal" :in-theory (enable aignet-add-reg
  ;;                                      aignet-idp)))))

  ;; (local
  ;;  (defthm aignet-idp-of-aignet-add-in
  ;;    (implies (and (idp id)
  ;;                  (<= (id-val id) (num-nodes aignet)))
  ;;             (aignet-idp id (mv-nth 1 (Aignet-add-in aignet))))
  ;;    :hints(("Goal" :in-theory (enable aignet-add-in
  ;;                                      aignet-idp)))))

  (local (defthm aignet-id-by-bound
           (implies (<= (nfix id) (node-count aignet))
                    (aignet-idp id aignet))
           :hints(("Goal" :in-theory (enable aignet-idp)))))

  ;; (local
  ;;  (defthm node-type-in-make-varmap
  ;;    (implies (and (natp id)
  ;;                  (<= (num-nodes aignet0) (nfix id))
  ;;                  (force (< (nfix id) (+ (num-nodes aignet0)
  ;;                                           (len vars)))))
  ;;             (let ((node (car (lookup-id
  ;;                               id
  ;;                               (mv-nth 1 (make-varmap vars regp varmap0
  ;;                                                      aignet0))))))
  ;;               (equal (stype node)
  ;;                      (if regp (reg-stype) (pi-stype)))))
  ;;    :hints(("Goal" :in-theory (enable make-varmap)
  ;;            :induct (make-varmap vars regp varmap0 aignet0)))))

  ;; (defthm id-eval-of-make-varmap-input
  ;;   (implies (and (natp id)
  ;;                 (<= (num-nodes aignet0) (nfix id))
  ;;                 (< (nfix id) (+ (num-nodes aignet0)
  ;;                                   (len vars))))
  ;;            (equal (id-eval id in-vals reg-vals
  ;;                            (mv-nth 1 (make-varmap vars nil varmap0 aignet0)))
  ;;                   (bfix (nth (+ (nfix id)
  ;;                                 (- (num-nodes aignet0))
  ;;                                 (num-ins aignet0))
  ;;                              in-vals))))
  ;;   :hints(("Goal" :in-theory (enable make-varmap)
  ;;           :induct (make-varmap vars nil varmap0 aignet0))
  ;;          (and stable-under-simplificationp
  ;;               '(:expand ((:free (aignet)
  ;;                           (id-eval id in-vals reg-vals aignet)))))))

  ;; (defthm lit-eval-of-make-varmap-input
  ;;   (implies (and (<= (num-nodes aignet0)
  ;;                     (lit-id lit))
  ;;                 (< (lit-id lit)
  ;;                    (+ (num-nodes aignet0)
  ;;                       (len vars))))
  ;;            (equal (lit-eval lit in-vals reg-vals
  ;;                             (mv-nth 1 (make-varmap vars nil varmap0
  ;;                                                    aignet0)))
  ;;                   (b-xor (lit-neg lit)
  ;;                          (nth (+ (lit-id lit)
  ;;                                  (- (num-nodes aignet0))
  ;;                                  (num-ins aignet0))
  ;;                               in-vals))))
  ;;   :hints(("Goal"
  ;;           :expand ((:free (aignet)
  ;;                     (lit-eval lit in-vals reg-vals aignet)))
  ;;           :do-not-induct t)))
  )






(local (defthm intersectp-equal-of-switch
         (implies (and (no-duplicatesp a)
                       (not (intersectp-equal a b)))
                  (not (intersectp-equal (cdr a)
                                          (cons (car a) b))))
         :hints(("Goal" :in-theory (enable intersectp-equal)))))


(defthm id-eval-of-aignet-add-in
  (equal (id-eval (+ 1 (node-count aignet))
                  in-vals reg-vals
                  (cons (list (pi-stype)) aignet))
         (bfix (nth (num-ins aignet) in-vals)))
  :hints(("Goal" :in-theory (enable id-eval))))

(defthm id-eval-of-aignet-add-reg
  (equal (id-eval (+ 1 (node-count aignet))
                  in-vals reg-vals
                  (cons (list (reg-stype)) aignet))
         (bfix (nth (num-regs aignet) reg-vals)))
  :hints(("Goal" :in-theory (enable id-eval))))

(defthm lit-eval-of-aignet-add-in
  (implies (equal (lit-id lit)
                  (num-nodes aignet))
           (equal (lit-eval lit in-vals reg-vals
                            (cons (list (pi-stype)) aignet))
                  (b-xor (lit-neg lit)
                         (nth (num-ins aignet) in-vals))))
  :hints(("Goal" :in-theory (e/d (lit-eval)
                                 (id-eval-of-aignet-add-in))
          :use ((:instance id-eval-of-aignet-add-in)))))

(defthm lit-eval-of-aignet-add-reg
  (implies (equal (lit-id lit)
                  (nfix (num-nodes aignet)))
           (equal (lit-eval lit in-vals reg-vals
                            (cons (list (reg-stype)) aignet))
                  (b-xor (lit-neg lit)
                         (nth (num-regs aignet) reg-vals))))
  :hints(("Goal" :in-theory (e/d (lit-eval)
                                 (id-eval-of-aignet-add-reg))
          :use ((:instance id-eval-of-aignet-add-reg)))))



(local (in-theory (disable acl2::aig-env-lookup)))

(local (defthm member-implies-index-of-natp-type
         (implies (member v vars)
                  (natp (acl2::index-of v vars)))
         :rule-classes :type-prescription))


;; (defthm aig-env-lookup-of-aignet-eval-to-env-of-consecutive-vars-to-varmap
;;   (implies (and (member v vars)
;;                 (equal (len (alist-keys varmap0))
;;                        (num-ins aignet0))
;;                 (no-duplicatesp-equal vars)
;;                 (not (intersectp-equal vars (alist-keys varmap0))))
;;            (let ((varmap (consecutive-vars-to-varmap (+ 1 (node-count aignet0)) vars varmap0))
;;                  (aignet (aignet-add-ins (len vars) aignet0)))
;;              (equal (acl2::aig-env-lookup
;;                      v (aignet-eval-to-env
;;                         varmap
;;                         in-vals reg-vals aignet))
;;                     (equal (nth (+ (stype-count :pi aignet0)
;;                                    (acl2::index-of v vars))
;;                                 in-vals)
;;                            1))))
;;   :hints (("Goal" :do-not-induct t
;;            ;; :in-theory (enable aignet-idp)
;;            ;; :expand ((:free (id aignet) (lit-eval (mk-lit id 0) in-vals reg-vals aignet))
;;            ;;          (:free (id aignet) (id-eval id in-vals reg-vals aignet)))
;;            ))
;;   :otf-flg t)

;; (defthm aig-env-lookup-of-aignet-eval-to-env-of-consecutive-vars-to-varmap-init
;;   (implies (and (member v vars)
;;                 (no-duplicatesp-equal vars)
;;                 (equal (node-count aignet0) 0))
;;            (let ((varmap (consecutive-vars-to-varmap 1 vars nil))
;;                  (aignet (aignet-add-ins (len vars) aignet0)))
;;              (equal (acl2::aig-env-lookup
;;                      v (aignet-eval-to-env
;;                         varmap
;;                         in-vals reg-vals aignet))
;;                     (equal (nth (acl2::index-of v vars)
;;                                 in-vals)
;;                            1))))
;;   :hints (("Goal" :do-not-induct t
;;            :in-theory (enable aignet-idp)
;;            :expand ((:free (id aignet) (lit-eval (mk-lit id 0) in-vals reg-vals aignet))
;;                     (:free (id aignet) (id-eval id in-vals reg-vals aignet)))))
;;   :otf-flg t)

;; (local (in-theory (disable aig-env-lookup-of-aignet-eval-to-env)))





;; (defthm lst-position-less-when-member
;;   (implies (member v vars)
;;            (< (lst-position v vars) (len vars))))

;; (defthm nth-lst-position
;;   (implies (member v vars)
;;            (equal (nth (lst-position v vars) vars) v))
;;   :hints(("Goal" :in-theory (enable nth))))

;; (defthm lst-position-type-when-member
;;   (implies (member v vars)
;;            (natp (lst-position v vars)))
;;   :rule-classes :type-prescription)


(defthm aig-eval-of-aignet-eval-to-env-of-consecutive-vars-to-varmap
  (implies (and (subsetp-equal (aig-vars aig) vars)
                (equal (len (alist-keys varmap0))
                       (num-ins aignet0))
                (no-duplicatesp-equal vars)
                (not (intersectp-equal vars (alist-keys varmap0))))
           (let ((varmap (consecutive-vars-to-varmap (+ 1 (node-count aignet0)) vars varmap0))
                 (aignet (aignet-add-ins (len vars) aignet0)))
             (equal (aig-eval aig
                              (aignet-eval-to-env
                               varmap
                               (env-to-bitarr
                                (revappend (alist-keys varmap0) vars)
                                env)
                               nil
                               aignet))
                    (aig-eval aig env))))
  :hints(("Goal" :in-theory (e/d (aig-eval)
                                 (lookup-in-aignet-eval-to-env
                                  acl2::aig-env-lookup
                                  acl2::revappend-removal))
          :induct (aig-eval aig env))))

(defthm aig-eval-of-aignet-eval-to-env-of-consecutive-vars-to-varmap-init
  (implies (and (double-rewrite
                 (subsetp-equal (aig-vars aig) vars))
                (no-duplicatesp-equal vars)
                (equal (num-ins aignet0) 0)
                (equal (node-count aignet0) 0))
           (let ((varmap (consecutive-vars-to-varmap 1 vars nil))
                 (aignet (aignet-add-ins (len vars) aignet0)))
             (equal (aig-eval aig
                              (aignet-eval-to-env
                               varmap
                               (env-to-bitarr vars env)
                               nil
                               aignet))
                    (aig-eval aig env))))
  :hints(("Goal" :in-theory (e/d (aig-eval)
                                 (lookup-in-aignet-eval-to-env
                                  acl2::aig-env-lookup
                                  acl2::revappend-removal
                                  aig-eval-of-aignet-eval-to-env-of-consecutive-vars-to-varmap))
          :use ((:instance aig-eval-of-aignet-eval-to-env-of-consecutive-vars-to-varmap
                 (varmap0 nil))))))


(defthm aignet-bitarr-to-aig-env-of-env-to-bitarr
  (acl2::alist-equiv (aignet-bitarr-to-aig-env
                      vars (env-to-bitarr vars env))
                     (acl2::aig-env-extract vars env))
  :hints(("Goal" :in-theory (enable acl2::alist-equiv-iff-agree-on-bad-guy
                                    equal-of-hons-assoc-equal
                                    acl2::aig-env-lookup))))

(defcong acl2::set-equiv acl2::alist-equiv (acl2::aig-env-extract vars env) 1
  :hints(("Goal" :in-theory (enable acl2::alist-equiv-iff-agree-on-bad-guy))))


#!acl2
(defthm aig-eval-of-aig-env-extract
  (implies (subsetp (aig-vars x) vars)
           (equal (aig-eval x (aig-env-extract vars env))
                  (aig-eval x env))))

(defthm aig-satisfying-assign-induces-aig->cnf-satisfying-assign
  (b* (((mv cnf ?lit vars sat-lits aignet) (aig->cnf aig sat-lits aignet :transform-config transform-config :gatesimp gatesimp))
       (cnf-vals (satisfying-assign-for-env env vars sat-lits aignet cnf-vals)))
    (equal (satlink::eval-formula cnf cnf-vals)
           (if (aig-eval aig env) 1 0)))
  :hints (("goal" :use ((:instance
                         aignet-satisfying-assign-induces-cnf-satisfying-assign
                         (aignet (mv-nth 4 (aig->cnf aig sat-lits aignet :transform-config transform-config :gatesimp gatesimp)))
                         (lit (mv-nth 1 (aig->cnf aig sat-lits aignet :transform-config transform-config :gatesimp gatesimp)))
                         (invals
                          (env-to-bitarr
                           (mv-nth 2 (aig->cnf aig sat-lits aignet :transform-config transform-config :gatesimp gatesimp))
                           env))
                         (regvals nil)
                         (cnf-vals (resize-bits (sat-next-var
                                                 (mv-nth 3 (aig->cnf aig sat-lits aignet :transform-config transform-config :gatesimp gatesimp)))
                                                nil))))
           :in-theory (e/d* (aignet-regvals->vals
                             aignet-regvals->vals-iter
                             lookup-stype-in-bounds)
                            (aignet-satisfying-assign-induces-cnf-satisfying-assign)))
          (and stable-under-simplificationp
               '(:in-theory (enable aig->cnf)))))


(local (defthm len-equal-0
         (equal (equal (len x) 0)
                (atom x))))

;; (defun aignet-vals-make-env (vars innum vals aignet)
;;   (Declare (xargs :stobjs (vals aignet)
;;                   :guard (and (<= (num-nodes aignet) (bits-length vals))
;;                               (natp innum)
;;                               (<= (+ (len vars) innum) (num-ins aignet)))))
;;   (if (atom vars)
;;       nil
;;     (cons (cons (car vars)
;;                 (equal 1 (get-bit (innum->id innum aignet) vals)))
;;           (aignet-vals-make-env (cdr vars) (1+ (lnfix innum)) vals aignet))))





;; (defthm memo-tablep-cnf->aignet-vals-iter
;;   (implies (< (node-count aignet) (len vals))
;;            (< (node-count aignet)
;;               (len (cnf->aignet-vals-iter n vals cnf-vals sat-lits aignet1))))
;;   :hints(("Goal" :in-theory (enable cnf->aignet-vals-iter)))
;;   :rule-classes :linear)

;; (defthm memo-tablep-cnf->aignet-vals
;;   (implies (< (node-count aignet) (len vals))
;;            (< (node-count aignet)
;;               (len (cnf->aignet-vals vals cnf-vals sat-lits aignet1))))
;;   :hints(("Goal" :in-theory (enable cnf->aignet-vals))))


(defun aig-cnf-vals->env (cnf-vals vars sat-lits aignet)
  (declare (xargs :stobjs (cnf-vals sat-lits aignet)
                  :guard (and (sat-lits-wfp sat-lits aignet)
                              (<= (len vars) (num-ins aignet))
                              (true-listp vars))))
  (b* (((local-stobjs invals)
        (mv env invals))
       (invals (resize-bits (num-ins aignet) invals))
       (invals (cnf->aignet-invals invals cnf-vals sat-lits aignet))
       (env (aignet-bitarr-to-aig-env vars invals)))
    (mv env invals)))


;; (defthm lookup-in-aignet-vals-make-env
;;   (equal (acl2::aig-env-lookup v (aignet-vals-make-env vars innum vals
;;                                                        aignet))
;;          (or (not (member v vars))
;;              (equal 1 (get-bit (innum->id (+ (nfix innum)
;;                                              (acl2::index-of v vars))
;;                                               aignet)
;;                                    vals))))
;;   :hints(("Goal" :in-theory (enable acl2::aig-env-lookup acl2::index-of))))

;; (defthm aignet-vals-make-env-of-extension
;;   (implies (and (aignet-extension-binding)
;;                 (<= (+ (nfix innum) (len vars)) (num-ins orig)))
;;            (equal (aignet-vals-make-env vars innum vals new)
;;                   (aignet-vals-make-env vars innum vals orig)))
;;   :hints(("Goal" :in-theory (enable lookup-stype-in-bounds))))

;; (defthm aignet-vals-in-vals-iter-of-extension
;;   (implies (and (aignet-extension-binding)
;;                 (equal (num-ins new) (num-ins orig)))
;;            (bits-equiv (aignet-vals->invals in-vals vals new)
;;                        (aignet-vals->invals in-vals vals orig)))
;;   :hints ((and stable-under-simplificationp
;;                `(:expand (,(car (last clause)))
;;                  :in-theory (enable lookup-stype-in-bounds)))))

;; (defthm aignet-vals-reg-vals-iter-of-extension
;;   (implies (and (aignet-extension-binding)
;;                 (equal (num-regs new) (num-regs orig)))
;;            (bits-equiv (aignet-vals->regvals reg-vals vals new)
;;                        (aignet-vals->regvals reg-vals vals orig)))
;;   :hints ((and stable-under-simplificationp
;;                `(:expand (,(car (last clause)))
;;                  :in-theory (enable lookup-stype-in-bounds)))))


(defthm bit-equiv-under-equal-to-1-second-arg
  (implies (bit-equiv x y)
           (equal (equal 1 x)
                  (equal 1 y)))
  :rule-classes :congruence)

(defthm bit-equiv-under-equal-to-1-first-arg
  (implies (bit-equiv x y)
           (equal (equal x 1)
                  (equal y 1)))
  :rule-classes :congruence)


;; (encapsulate nil
;;   (local (in-theory (disable aignet-vals-make-env
;;                              no-duplicatesp-equal
;;                              subsetp-equal acl2::aig-env-lookup
;;                              aignet-eval-to-env)))
;;   (defthm aig-eval-of-aignet-vals-make-env
;;     (implies (and (equal (num-ins aignet) 0)
;;                   (equal (node-count aignet) 0)
;;                   (no-duplicatesp-equal vars)
;;                   (double-rewrite (subsetp-equal (aig-vars aig) vars)))
;;            (let ((varmap (consecutive-vars-to-varmap 1 vars nil))
;;                  (new (aignet-add-ins (len vars) aignet)))
;;              (equal (aig-eval aig
;;                               (aignet-vals-make-env
;;                                vars 0 vals new))
;;                     (aig-eval aig
;;                               (aignet-eval-to-env
;;                                varmap
;;                                invals regvals new)))))
;;     :hints(("Goal" :in-theory (e/d (aig-eval
;;                                     equal-1-rewrite-under-congruence))
;;             :induct t))))


(defcong bits-equiv equal (aignet-eval-to-env varmap in-vals reg-vals aignet) 2
  :hints(("Goal" :in-theory (enable aignet-eval-to-env))))

(defcong bits-equiv equal (aignet-eval-to-env varmap in-vals reg-vals aignet) 3
  :hints(("Goal" :in-theory (enable aignet-eval-to-env))))

;; (local (defthm lookup-exists-of-aignet-vals-make-env
;;          (iff (hons-assoc-equal k (aignet-vals-make-env vars innum vals aignet))
;;               (member k vars))
;;          :hints(("Goal" :in-theory (enable aignet-vals-make-env)))))

;; (local (defthm cdr-lookup-of-aignet-vals-make-env
;;          (implies (member k vars)
;;                   (equal (cdr (hons-assoc-equal k (aignet-vals-make-env vars innum vals aignet)))
;;                          (acl2::bit->bool (nth (innum->id (+ (lnfix innum) (acl2::index-of k vars)) aignet)
;;                                                vals))))
;;          :hints(("Goal" :in-theory (enable aignet-vals-make-env acl2::index-of)))))


;; (defthm aignet-vals-make-env-is-aignet-bitarr-to-aig-env-of-aignet-vals->invals
;;   (implies (<= (+ (nfix n) (len vars)) (stype-count :pi aignet))
;;            (acl2::alist-equiv (aignet-vals-make-env vars n vals aignet)
;;                               (Aignet-bitarr-to-aig-env vars (nthcdr n (aignet-vals->invals nil vals aignet)))))
;;   :hints(("Goal" :in-theory (enable acl2::alist-equiv-iff-agree-on-bad-guy
;;                                     equal-of-hons-assoc-equal)
;;           :do-not-induct t)))

(defthm cnf-satisfying-assign-induces-aig-satisfying-assign
  (b* (((mv cnf ?lit vars sat-lits aignet)
        (aig->cnf aig sat-lits aignet :transform-config transform-config :gatesimp gatesimp))
       (env (aig-cnf-vals->env cnf-vals vars sat-lits aignet)))
    (implies (equal (satlink::eval-formula cnf cnf-vals) 1)
             (aig-eval aig env)))
  :hints(("Goal" :in-theory (e/d ()
                                 (cnf-satisfying-assign-induces-aignet-satisfying-assign
                                  b-and b-ior b-xor b-not))
          :use ((:instance
                 cnf-satisfying-assign-induces-aignet-satisfying-assign
                 (lit (mv-nth 1 (aig->cnf aig sat-lits aignet :transform-config transform-config :gatesimp gatesimp)))
                 (aignet (mv-nth 4 (aig->cnf aig sat-lits aignet :transform-config transform-config :gatesimp gatesimp)))
                 (invals (acl2::repeat (len (mv-nth 2 (aig->cnf aig sat-lits aignet :transform-config transform-config :gatesimp gatesimp))) 0))))
          :do-not-induct t)
           (and stable-under-simplificationp
                '(:in-theory (enable aig->cnf)))))

(defthm len-vars-of-aig->cnf
  (equal (len (mv-nth 2 (aig->cnf aig sat-lits aignet :transform-config transform-config :gatesimp gatesimp)))
         (stype-count (pi-stype) (mv-nth 4 (aig->cnf aig sat-lits aignet :transform-config transform-config :gatesimp gatesimp))))
  :hints(("Goal" :in-theory (enable* aig->cnf))))

(in-theory (disable aig->cnf
                    aig-cnf-vals->env
                    satisfying-assign-for-env))
