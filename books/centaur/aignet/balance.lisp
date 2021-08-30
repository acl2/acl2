; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2017 Centaur Technology
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
(include-book "centaur/aignet/cnf" :dir :system) ;; for supergate
(include-book "centaur/aignet/construction" :dir :system)
(include-book "centaur/aignet/prune" :dir :system)
(include-book "defsort/defsort" :dir :system)
(include-book "centaur/aignet/levels" :dir :system)
(include-book "count")
(include-book "supergate")
(include-book "literal-sort-aignet")
(local (include-book "centaur/satlink/cnf-basics" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system ))
(local (include-book "centaur/aignet/bit-lemmas" :dir :system))
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (in-theory (disable nth
                           update-nth
                           nfix
                           ifix
                           (tau-system)
                           resize-list
                           acl2::resize-list-when-atom)))
(local (std::add-default-post-define-hook :fix))
(std::make-returnspec-config :hints-sub-returnnames t)

;; BOZO skipping node-list-fix congruence proofs here
(local (table fty::fixtypes 'fty::fixtype-alist
              (b* ((fixtype-alist (cdr (assoc 'fty::fixtype-alist (table-alist 'fty::fixtypes world)))))
                (remove-equal (assoc 'aignet fixtype-alist)
                              fixtype-alist))))

(local (xdoc::set-default-parents balance))

(fty::defprod balance-config
  ((search-higher-levels booleanp :default t
                         "Says whether to search literals with higher fanin depths
                          when looking for a pairing for a given literal.  Tends
                          to find more reductions, may take somewhat longer.")
   (search-second-lit booleanp :default t
                      "If no reducing pairing is found for the first literal of
                       a supergate, says whether to search for a pairing for the
                       next literal before defaulting to pairing it with the first
                       literal.  Tends to find more reductions but reduce the network
                       depth less and take somewhat longer.")
   (search-limit natp :default 1000
                 "Search at most this many literals for a match.")
   (supergate-limit posp :default 1000
                    "Build supergates at most this big.")
   (verbosity-level natp :default 1
                    "Controls the level of output during balance
                     transformation. Level 0 will speed things up for larger aignets.")
   (gatesimp gatesimp-p :default (default-gatesimp)
             "Gate simplification parameters.  Warning: This transform will do
              nothing good if hashing is turned off."))
  :tag :balance-config)




                    



(defsection levels-sort

  (define lit-in-bounds ((x litp) (var-bound natp))
    :enabled t
    (< (lit-id x) (lnfix var-bound)))

  (define litp-for-levels (x levels)
    :enabled t
    (and (litp x) (lit-in-bounds x (u32-length levels))))

  (define lit-list-for-levels (x levels)
    (if (atom x)
        t
      (and (litp-for-levels (car x) levels)
           (lit-list-for-levels (cdr x) levels))))

  (define levels-sort-< (x y levels)
    :guard (and (litp-for-levels x levels)
                (litp-for-levels y levels))
    (< (get-u32 (lit-id x) levels)
       (get-u32 (lit-id y) levels)))

  (local (in-theory (enable levels-sort-<)))

  (acl2::defsort levels-sort (x levels)
    :extra-args-stobjs (levels)
    :extra-args-stobj-recognizers (u32arr$ap levels)
    :compare< levels-sort-<
    :comparablep litp-for-levels)

  (defthm set-equiv-of-levels-sort-insert
    (acl2::set-equiv (levels-sort-insert x y levels)
                     (cons x y))
    :hints(("Goal" :in-theory (enable levels-sort-insert)
            :induct t)
           (acl2::set-reasoning)))

  (defthm set-equiv-of-levels-sort
    (acl2::set-equiv (levels-sort-insertsort x levels) x)
    :hints(("Goal" :in-theory (enable levels-sort-insertsort))))

  (defthm lit-listp-of-levels-sort-insert
    (implies (and (litp x) (lit-listp y))
             (lit-listp (levels-sort-insert x y levels)))
    :hints(("Goal" :in-theory (enable levels-sort-insert))))

  (defthm lit-listp-of-levels-sort-insertsort
    (implies (lit-listp x)
             (lit-listp (levels-sort-insertsort x levels)))
    :hints(("Goal" :in-theory (enable levels-sort-insertsort))))

  ;; (defthm aignet-lit-listp-of-levels-sort-insert
  ;;   (implies (and (aignet-litp x aignet) (aignet-lit-listp y aignet))
  ;;            (aignet-lit-listp (levels-sort-insert x y levels) aignet))
  ;;   :hints(("Goal" :in-theory (enable levels-sort-insert))))

  ;; (defthm aignet-lit-listp-of-levels-sort-insertsort
  ;;   (implies (aignet-lit-listp x aignet)
  ;;            (aignet-lit-listp (levels-sort-insertsort x levels) aignet))
  ;;   :hints(("Goal" :in-theory (enable levels-sort-insertsort))))

  (defthm len-of-levels-sort-insert
    (equal (len (levels-sort-insert x y levels))
           (+ 1 (len y)))
    :hints(("Goal" :in-theory (enable levels-sort-insert))))

  (defcong acl2::set-equiv equal (levels-sort-list-p lits levels) 1
  :hints (("goal" :use ((:instance (:functional-instance
                                    acl2::element-list-p-set-equiv-congruence
                                    (acl2::element-list-final-cdr-p (lambda (x) t))
                                    (acl2::element-p (lambda (x) (litp-for-levels x levels)))
                                    (acl2::element-example (lambda () 0))
                                    (acl2::element-list-p (lambda (x) (levels-sort-list-p x levels))))
                         (x lits) (y lits-equiv)))
           :in-theory (enable levels-sort-list-p)
           :do-not-induct t)))

  
  (defthm aignet-eval-parity-of-levels-sort-insert
    (equal (aignet-eval-parity (levels-sort-insert x y levels) invals regvals aignet)
           (aignet-eval-parity (cons x y) invals regvals aignet))
    :hints(("Goal" :in-theory (enable aignet-eval-parity levels-sort-insert )
            :induct (levels-sort-insert x y levels))))

  (defthm aignet-eval-parity-of-levels-sort-insertsort
    (equal (aignet-eval-parity (levels-sort-insertsort x levels) invals regvals aignet)
           (aignet-eval-parity x invals regvals aignet))
    :hints(("Goal" :in-theory (enable aignet-eval-parity levels-sort-insertsort )
            :induct (levels-sort-insertsort x levels)))))

(define supergate-has-contradiction ((x lit-listp "literal-sorted"))
  :guard (consp x)
  :returns (contradictionp)
  (or (and (mbt (consp x)) (eql (lit-fix (car x)) 0))
      (and (consp (cdr x))
           (or (eql (lit-fix (car x)) (lit-negate (cadr x)))
               (supergate-has-contradiction (cdr x)))))
  ///
  (local (defthm lit-eval-when-equal-lit-negate
           (implies (equal (lit-fix x) (lit-negate y))
                    (equal (lit-eval x invals regvals aignet)
                           (b-not (lit-eval y invals regvals aignet))))
           :hints(("Goal" :expand ((:free (x) (lit-eval x invals regvals aignet)))))))

  (defret supergate-has-contradiction-correct
    (implies (supergate-has-contradiction x)
             (equal (aignet-eval-conjunction x invals regvals aignet) 0))
    :hints (("goal" :induct t
             :expand ((aignet-eval-conjunction x invals regvals aignet)
                      (aignet-eval-conjunction (cdr x) invals regvals aignet))))))

(define supergate-has-contradiction-top ((x lit-listp))
  :enabled t
  (mbe :logic (supergate-has-contradiction x)
       :exec (and (consp x)
                  (supergate-has-contradiction x))))

(defthm aignet-eval-conjunction-when-0-member
  (implies (member 0 (lit-list-fix x))
           (equal (aignet-eval-conjunction x invals regvals aignet) 0))
  :hints(("Goal" :in-theory (enable aignet-eval-conjunction lit-list-fix))))

(defthm aignet-eval-conjunction-of-remove-1
  (equal (aignet-eval-conjunction (remove 1 (lit-list-fix x)) invals regvals aignet)
         (aignet-eval-conjunction x invals regvals aignet))
  :hints(("Goal" :in-theory (enable aignet-eval-conjunction lit-list-fix))))

(define aignet-update-node-level ((id natp)
                                  (levels)
                                  (aignet))
  :guard (< id (num-fanins aignet))
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  :returns (new-levels)
  (b* ((id (lnfix id))
       (levels (if (< (u32-length levels) (num-fanins aignet))
                   (resize-u32 (max 16 (* 2 (num-fanins aignet))) levels)
                 levels))
       ((unless (eql (id->type id aignet) (gate-type)))
        (set-u32 id 0 levels))
       (flev0 (get-u32 (lit-id (gate-id->fanin0 id aignet)) levels))
       (flev1 (get-u32 (lit-id (gate-id->fanin1 id aignet)) levels)))
    (set-u32 id (+ 1 (max flev0 flev1)) levels))
  ///
  (defret aignet-update-node-level-length-increases
    (<= (len levels) (len new-levels))
    :rule-classes :linear)

  (defret aignet-update-node-level-length-lower-bound
    (< (fanin-count aignet) (len new-levels))
    :rule-classes :linear))



(fty::deffixequiv aignet-eval-conjunction
  :hints(("Goal" :in-theory (enable aignet-eval-conjunction))))

(defthm aignet-eval-conjunction-of-atom
  (implies (not (consp x))
           (equal (aignet-eval-conjunction x invals regvals aignet) 1))
  :hints(("Goal" :in-theory (enable aignet-eval-conjunction))))

(defthm cdr-of-lit-list-fix
  (equal (cdr (lit-list-fix x))
         (lit-list-fix (cdr x))))

;; (fty::deffixequiv aignet-litp
;;   :hints(("Goal" :in-theory (enable aignet-litp))))

(defthm aignet-lit-listp-of-lit-list-fix
  (implies (aignet-lit-listp x aignet)
           (aignet-lit-listp (lit-list-fix x) aignet)))

(define aignet-balance-find-pairing-rec ((first litp :type (unsigned-byte 30))
                                         (limit natp)
                                         (level-ref litp)
                                         (rest lit-listp)
                                         levels
                                         (gatesimp gatesimp-p)
                                         aignet2 strash)
  :guard (and (fanin-litp first aignet2)
              (fanin-litp level-ref aignet2)
              (aignet-lit-listp rest aignet2)
              (<= (num-fanins aignet2) (u32-length levels)))
  :returns (mv (pairing (iff (litp pairing) pairing))
               (remaining lit-listp))
  :measure (len rest)
  :verify-guards nil
  (b* ((rest (lit-list-fix rest))
       ((when (or (atom rest)
                  (zp limit)
                  (and (not (lit-equiv 0 level-ref))
                       (levels-sort-< (lit-fix level-ref) (car rest) levels))))
        (mv nil rest))
       (candidate (lit-fix (car rest)))
       ((when (eql (lit-id candidate) (lit-id first)))
        (mv candidate (cdr rest)))
       ((mv existing & & &)
        (mbe :logic (aignet-and-gate-simp/strash first candidate gatesimp strash aignet2)
             :exec (if (<= (car rest) #x1fffffff) ;; bozo
                       (aignet-and-gate-simp/strash first candidate gatesimp strash aignet2)
                     (ec-call (aignet-and-gate-simp/strash first candidate gatesimp strash aignet2)))))
       ((when existing)
        (mv candidate (cdr rest)))
       ((mv pairing remaining)
        (aignet-balance-find-pairing-rec first (1- limit) level-ref (cdr rest) levels gatesimp aignet2 strash))
       ((when pairing)
        (mv pairing (cons candidate remaining))))
    (mv nil rest))
  ///
  (verify-guards aignet-balance-find-pairing-rec :guard-debug t
    :hints (("goal" :do-not-induct t :in-theory (enable aignet-idp))) :otf-flg t)

  (defret aignet-balance-find-pairing-rec-correct-when-found
    (implies pairing
             (equal (b-and (lit-eval pairing invals regvals aignet2)
                           (aignet-eval-conjunction remaining invals regvals aignet2))
                    (aignet-eval-conjunction rest invals regvals aignet2)))
    :hints(("Goal" 
            :induct t
            :expand ((:free (a b) (aignet-eval-conjunction (cons a b) invals regvals aignet2))
                     (aignet-eval-conjunction rest invals regvals aignet2)
                     (lit-list-fix rest)))
           (and stable-under-simplificationp
                '(:in-theory (enable b-and)))))

  (defret aignet-balance-find-pairing-rec-correct-when-found-rest
    (implies pairing
             (equal (b-and (lit-eval pairing invals regvals aignet2)
                           (b-and (aignet-eval-conjunction remaining invals regvals aignet2)
                                  c))
                    (b-and (aignet-eval-conjunction rest invals regvals aignet2)
                           c)))
    :hints(("Goal" 
            :induct t
            :expand ((:free (a b) (aignet-eval-conjunction (cons a b) invals regvals aignet2))
                     (aignet-eval-conjunction rest invals regvals aignet2)
                     (lit-list-fix rest)))
           (and stable-under-simplificationp
                '(:in-theory (enable b-and)))))

  (defret aignet-balance-find-pairing-rec-when-not-found
    (implies (not pairing)
             (equal remaining (lit-list-fix rest))))

  (defret len-of-aignet-balance-find-pairing-rec
    (equal (len remaining)
           (if pairing
               (1- (len rest))
             (len rest))))

  (defret aignet-lit-listp-of-aignet-balance-find-pairing-rec
    (implies (aignet-lit-listp rest aignet)
             (aignet-lit-listp remaining aignet))
    :hints(("Goal" :in-theory (enable aignet-lit-listp))))

  (defret aignet-litp-of-aignet-balance-find-pairing-rec
    (implies (and (aignet-lit-listp rest aignet)
                  pairing)
             (aignet-litp pairing aignet))))
        
        

(define aignet-balance-find-pairing ((lits lit-listp)
                                     (config balance-config-p)
                                     levels aignet2 strash)
  :guard (and (consp lits)
              (consp (cdr lits))
              (aignet-lit-listp lits aignet2)
              (<= (num-fanins aignet2) (u32-length levels)))
  :returns (mv (first litp) (second litp) (rest lit-listp))
  (b* ((first (lit-fix (car lits)))
       (second (lit-fix (cadr lits)))
       ((balance-config config))
       (level-ref1 (if config.search-higher-levels 0 second))
       ((mv pairing rest)
        ;; second passed in is just used for level comparison, so we do want rest, not rest-rest
        (mbe :logic
             (aignet-balance-find-pairing-rec first config.search-limit level-ref1 (cdr lits) levels config.gatesimp aignet2 strash)
             :exec (if (<= first #x1fffffff) ;; bozo
                       (aignet-balance-find-pairing-rec first config.search-limit level-ref1 (cdr lits) levels config.gatesimp aignet2 strash)
                     (ec-call (aignet-balance-find-pairing-rec first config.search-limit level-ref1 (cdr lits) levels config.gatesimp aignet2 strash)))))
       ((when pairing) (mv first pairing rest))
       ((when (or (not config.search-second-lit)
                  (atom (cddr lits))))
        (mv first second (lit-list-fix (cddr lits))))
       (level-ref2 (if config.search-higher-levels 0 (caddr lits))) 
       ((mv pairing rest)
        (mbe :logic
             (aignet-balance-find-pairing-rec second config.search-limit level-ref2 (cddr lits) levels config.gatesimp aignet2 strash)
             :exec (if (<= second #x1fffffff) ;; bozo
                       (aignet-balance-find-pairing-rec second config.search-limit level-ref2 (cddr lits) levels config.gatesimp aignet2 strash)
                     (ec-call (aignet-balance-find-pairing-rec second config.search-limit level-ref2 (cddr lits) levels config.gatesimp aignet2 strash)))))
       ((when pairing)
        (mv second pairing (cons first rest))))
    (mv first second (lit-list-fix (cddr lits))))
  ///
  (local (defthm move-pairing-over-lit-eval-insts
           (implies (syntaxp (not (and (consp lit) (eq (car lit) 'mv-nth))))
                    (equal (b-and (lit-eval (mv-nth 0 mv-nth-lit)
                                            invals1 regvals1 aignet1)
                                  (b-and (lit-eval lit invals regvals aignet)
                                         rest))
                           (b-and (lit-eval lit invals regvals aignet)
                                  (b-and (lit-eval (mv-nth 0 mv-nth-lit)
                                                   invals1 regvals1 aignet1)
                                         rest))))
           :hints(("Goal" :in-theory '(b-and (acl2::zbp))))))
                         

  (defret aignet-balance-find-pairing-correct
    (implies (and (consp lits) (consp (cdr lits)))
             (equal (aignet-eval-conjunction (list* first second rest) invals regvals aignet2)
                    (aignet-eval-conjunction lits invals regvals aignet2)))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (a b) (aignet-eval-conjunction (cons a b) invals regvals aignet2))
                            (aignet-eval-conjunction lits invals regvals aignet2)
                            (aignet-eval-conjunction (list (cadr lits)) invals regvals aignet2)
                            (aignet-eval-conjunction (cdr lits) invals regvals aignet2)
                            (aignet-eval-conjunction nil invals regvals aignet2)
                            (lit-list-fix lits))))
            (and stable-under-simplificationp
                 '(:in-theory (enable b-and))))
    :otf-flg t)

  (local (defthm cdr-lit-list-fix
           (equal (cdr (lit-list-fix x))
                  (lit-list-fix (cdr x)))))

  (defret len-of-aignet-balance-find-pairing
    (implies (and (consp lits) (consp (cdr lits)))
             (equal (len rest) (- (len lits) 2))))

  (defret aignet-lit-listp-of-aignet-balance-find-pairing
    (implies (and (aignet-lit-listp lits aignet)
                  (consp lits) (consp (cdr lits)))
             (aignet-lit-listp rest aignet))
    :hints(("Goal" :in-theory (enable aignet-lit-listp))))

  (defret aignet-litp-of-aignet-balance-find-pairing
    (implies (and (aignet-lit-listp lits aignet)
                  (consp lits) (consp (cdr lits)))
             (and (aignet-litp first aignet)
                  (aignet-litp second aignet)))))
       
       
(defthm levels-sort-list-p-when-aignet-lit-listp
  (implies (and (aignet-lit-listp lits aignet2)
                (lit-listp lits)
                (<= (num-fanins aignet2) (u32-length levels)))
           (levels-sort-list-p lits levels))
  :hints(("Goal" :in-theory (enable levels-sort-list-p aignet-idp))))

(defthm levels-sort-list-p-when-aignet-lit-listp-bind-free
  (implies (and (bind-free '((aignet2 . aignet2)) (aignet2))
                (aignet-lit-listp lits aignet2)
                (lit-listp lits)
                (<= (num-fanins aignet2) (u32-length levels)))
           (levels-sort-list-p lits levels))
  :hints(("Goal" :in-theory (enable levels-sort-list-p))))

(local (defretd max-fanin-of-aignet-install-gate
         (implies (and (aignet-litp x0 aignet)
                       (aignet-litp x1 aignet))
                  (equal (fanin-count new-aignet)
                         (if (> (lit-id lit) (fanin-count aignet))
                             (lit-id lit)
                           (fanin-count aignet))))
         :fn aignet-install-gate
         :hints(("Goal" :in-theory (e/d (aignet-install-gate aignet-idp))))))

(local (defret fanin-count-of-aignet-hash-and-casesplit
         (implies (and (aignet-litp lit1 aignet)
                       (aignet-litp lit2 aignet))
                  (equal (fanin-count new-aignet)
                         (if (> (lit-id and-lit) (fanin-count aignet))
                             (lit-id and-lit)
                           (fanin-count aignet))))
         :fn aignet-hash-and
         :hints(("Goal" :in-theory (e/d (aignet-hash-and max-fanin-of-aignet-install-gate))))))

(defthm aignet-hash-and-id-less-than-fanin-count
  (implies (and (aignet-litp lit1 aignet)
                (aignet-litp lit2 aignet))
           (b* (((mv lit ?strash new-aignet) (aignet-hash-and lit1 lit2 gatesimp strash aignet)))
             (<= (lit-id lit) (fanin-count new-aignet))))
  :rule-classes :linear)

;; ;; (local (defret max-fanin-of-aignet-hash-xor-casesplit
;; ;;          (equal (fanin-count (find-max-fanin new-aignet))
;; ;;                 (if (> (lit-id xor-lit) (fanin-count aignet))
;; ;;                     (lit-id xor-lit)
;; ;;                   (fanin-count aignet)))
;; ;;          :fn aignet-hash-xor
;; ;;          :hints(("Goal" :in-theory (e/d (aignet-hash-xor max-fanin-of-aignet-install-gate))))))

(defthm aignet-hash-xor-id-less-than-max-fanin
  (b* (((mv lit ?strash new-aignet) (aignet-hash-xor lit1 lit2 gatesimp strash aignet)))
    (<= (lit-id lit) (fanin-count new-aignet)))
  :hints (("goal" :use ((:instance aignet-litp-of-aignet-hash-xor))
           :in-theory (e/d (aignet-idp) (aignet-litp-of-aignet-hash-xor))))
  :rule-classes :linear)



;; (defthm aignet-lit-listp-of-cdr
;;   (implies (aignet-lit-listp x aignet)
;;            (aignet-lit-listp (cdr x) aignet))
;;   :hints(("Goal" :in-theory (enable aignet-lit-listp))))

(defthm aignet-eval-conjunction-of-extend
  (implies (and (aignet-extension-binding)
                (aignet-lit-listp lits orig))
           (equal (aignet-eval-conjunction lits invals regvals new)
                  (aignet-eval-conjunction lits invals regvals orig)))
  :hints(("Goal" :in-theory (enable aignet-eval-conjunction))))

(define aignet-balance-build-supergate-rec ((lits lit-listp)
                                            (config balance-config-p)
                                            (levels)
                                            (aignet2)
                                            (strash))
  :returns (mv (result-lit litp)
               (new-levels)
               (new-aignet2)
               (new-strash))
  :guard (and (consp lits)
              (aignet-lit-listp lits aignet2)
              (<= (num-fanins aignet2) (u32-length levels)))
  :measure (len lits)
  (b* (((when (atom (cdr lits)))
        (mv (lit-fix (car lits)) levels aignet2 strash))
       ((mv lit1 lit2 rest)
        (aignet-balance-find-pairing lits config levels aignet2 strash))
       ((balance-config config))
       ((mv new-lit strash aignet2) (aignet-hash-and lit1 lit2 config.gatesimp strash aignet2))
       ((when (eql (lit-id new-lit) 0))
        ;; this way we don't insert constant nodes into the list
        (if (eql (lit->neg new-lit) 0)
            ;; constant 0 -- done
            (mv 0 levels aignet2 strash)
          ;; constant 1 -- don't insert
          (if (consp rest)
              (aignet-balance-build-supergate-rec rest config levels aignet2 strash)
            (mv 1 levels aignet2 strash))))
       (levels (aignet-update-node-level (lit-id new-lit) levels aignet2))
       (rest (levels-sort-insert new-lit rest levels)))
    (aignet-balance-build-supergate-rec rest config levels aignet2 strash))
  ///
  (local (defthm aignet-eval-conjunction-of-hash-and
           (b* (((mv lit & new-aignet)
                 (aignet-hash-and lit1 lit2 gatesimp strash aignet)))
             (implies (and (aignet-litp lit1 aignet)
                           (aignet-litp lit2 aignet))
                      (equal (aignet-eval-conjunction (cons lit rest) invals regvals new-aignet)
                             (aignet-eval-conjunction (cons lit1 (cons lit2 rest))
                                                      invals regvals new-aignet))))
           :hints(("Goal" :in-theory (enable aignet-eval-conjunction b-and)
                   :do-not-induct t))))


  (defret aignet-balance-build-supergate-rec-correct
    (implies (and (aignet-lit-listp lits aignet2)
                  (Consp lits))
             (equal (lit-eval result-lit invals regvals new-aignet2)
                    (aignet-eval-conjunction lits invals regvals aignet2)))
    :hints (("goal" :induct t
             :expand (<call>
                      (:free (b) (aignet-eval-conjunction (cons (car lits) b) invals regvals aignet2))
                      (aignet-eval-conjunction lits invals regvals aignet2)))
            (and stable-under-simplificationp
                 '(:use ((:instance aignet-eval-conjunction-of-hash-and
                          (aignet aignet2)
                          (gatesimp (balance-config->gatesimp config))
                          (lit1 (mv-nth 0 (aignet-balance-find-pairing
                                           lits config levels aignet2 strash)))
                          (lit2 (mv-nth 1 (aignet-balance-find-pairing
                                           lits config levels aignet2 strash)))
                          (rest (mv-nth 2 (aignet-balance-find-pairing
                                           lits config levels aignet2 strash)))))
                   :in-theory (e/d (aignet-eval-conjunction lit-eval)
                                   (aignet-eval-conjunction-of-hash-and
                                    lit-eval-of-aignet-hash-and))
                   :do-not-induct t))))

  (defret aignet-litp-of-aignet-balance-build-supergate-rec
    (implies (aignet-lit-listp lits aignet2)
             (aignet-litp result-lit new-aignet2))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret levels-length-of-aignet-balance-build-supergate-rec
    (implies (and (<= (num-fanins aignet2) (len levels))
                  (aignet-lit-listp lits aignet2))
             (< (fanin-count new-aignet2) (len new-levels)))
    :hints (("goal" :induct <call> :expand (<call>)))
    :rule-classes :linear)

  (defret aignet-extension-p-of-aignet-balance-build-supergate-rec
    (aignet-extension-p new-aignet2 aignet2))

  (defret stype-counts-of-aignet-balance-build-supergate-rec
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2) (stype-count stype aignet2)))))

(defthm aignet-lit-listp-of-remove
  (implies (aignet-lit-listp x aignet)
           (aignet-lit-listp (remove k x) aignet))
  :hints(("Goal" :in-theory (enable aignet-lit-listp))))
    

(defthm lit-listp-of-remove
  (implies (lit-listp x)
           (lit-listp (remove k x)))
  :hints(("Goal" :in-theory (enable lit-listp))))

(define remove-duplicate-lits ((x lit-listp "literal-sorted"))
  :returns (new-x lit-listp)
  (if (or (atom x) (atom (cdr x)))
      (lit-list-fix x)
    (if (lit-equiv (car x) (cadr x))
        (remove-duplicate-lits (cdr x))
      (cons-with-hint (lit-fix (car x))
                      (remove-duplicate-lits (cdr x))
                      (lit-list-fix x))))
  ///
  (defret remove-duplicate-lits-set-equiv
    (acl2::set-equiv new-x (lit-list-fix x))))


(define aignet-balance-build-supergate ((lits lit-listp)
                                        (config balance-config-p)
                                        (levels)
                                        (aignet2)
                                        (strash))
  :returns (mv (result-lit litp)
               (new-levels)
               (new-aignet2)
               (new-strash))
  :guard (and (aignet-lit-listp lits aignet2)
              (<= (num-fanins aignet2) (u32-length levels)))
  :guard-debug t
  (b* ((lits (lit-list-fix lits))
       ((when (member 0 lits))
        (mv 0 levels aignet2 strash))
       (lits (remove-duplicate-lits (literal-sort (lit-list-fix lits))))
       ((when (supergate-has-contradiction-top lits))
        (mv 0 levels aignet2 strash))
       (lits (remove 1 lits))
       ((when (atom lits))
        (mv 1 levels aignet2 strash))
       (lits (levels-sort lits levels)))
    (aignet-balance-build-supergate-rec lits config levels aignet2 strash))
  ///
  (local (defthm aignet-lit-listp-lemma
           (implies (and (aignet-lit-listp lits aignet)
                         (lit-listp lits))
                    (and (aignet-lit-listp
                          (levels-sort-insertsort
                           (remove k (remove-duplicate-lits (literal-sort-insertsort lits)))
                           levels)
                          aignet)
                         (aignet-lit-listp
                          (remove k (remove-duplicate-lits (literal-sort-insertsort lits)))
                          aignet)))))

  (local (defthm consp-of-remove-equal-lemma
           (implies (lit-listp lits)
                    (equal (consp (remove k (remove-duplicate-lits (literal-sort-insertsort lits))))
                           (consp (remove k lits))))))

  (defret aignet-balance-build-supergate-correct
    (implies (aignet-lit-listp lits aignet2)
             (equal (lit-eval result-lit invals regvals new-aignet2)
                    (aignet-eval-conjunction lits invals regvals aignet2)))
    :hints (("goal" :use ((:instance supergate-has-contradiction-correct
                           (x (remove-duplicate-lits
                               (literal-sort-insertsort
                                (lit-list-fix lits))))
                           (aignet aignet2))
                          (:instance aignet-eval-conjunction-of-remove-1
                           (x (lit-list-fix lits)) (aignet aignet2)))
             :in-theory (disable supergate-has-contradiction-correct
                                 aignet-eval-conjunction-of-remove-1))))

  (defret aignet-litp-of-aignet-balance-build-supergate
    (implies (aignet-lit-listp lits aignet2)
             (aignet-litp result-lit new-aignet2)))

  (defret levels-length-of-aignet-balance-build-supergate
    (implies (and (<= (num-fanins aignet2) (len levels))
                  (aignet-lit-listp lits aignet2))
             (< (fanin-count new-aignet2) (len new-levels)))
    :rule-classes :linear)

  (defret aignet-extension-p-of-aignet-balance-build-supergate
    (aignet-extension-p new-aignet2 aignet2))

  (defret stype-counts-of-aignet-balance-build-supergate
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2) (stype-count stype aignet2)))))

(define cancel-parity-lits ((x lit-listp "literal-sorted")
                            (neg bitp))
  :returns (mv (negate bitp :rule-classes :type-prescription)
               (new-x lit-listp))
  (b* (((when (or (atom x) (atom (cdr x))))
        (mv (lbfix neg) (lit-list-fix x)))
       (lit1 (lit-fix (car x)))
       ((when (eql lit1 1))
        (cancel-parity-lits (cdr x) (b-not neg)))
       ((when (eql lit1 0))
        (cancel-parity-lits (cdr x) neg))
       (lit2 (lit-fix (cadr x)))
       ((when (eql lit1 lit2))
        (cancel-parity-lits (cddr x) neg))
       ((when (eql lit1 (lit-negate lit2)))
        (cancel-parity-lits (cddr x) (b-not neg)))
       ((mv neg rest) (cancel-parity-lits (cdr x) neg)))
    (mv neg (cons lit1 rest)))
  ///
  (local (defthm lit-eval-when-equal-lit-negate
           (implies (equal (lit-fix x) (lit-negate y))
                    (equal (lit-eval y invals regvals aignet)
                           (b-not (lit-eval x invals regvals aignet))))
           :hints(("Goal" :expand ((:free (x) (lit-eval x invals regvals aignet)))))))

  (defret aignet-eval-parity-of-cancel-parity-lits
    (equal (aignet-eval-parity new-x invals regvals aignet)
           (b-xor (b-xor neg negate)
                  (aignet-eval-parity x invals regvals aignet)))
    :hints(("Goal" :in-theory (enable aignet-eval-parity))))

  (defret aignet-lit-listp-of-cancel-parity-lits
    (implies (aignet-lit-listp x aignet)
             (aignet-lit-listp new-x aignet))))

(define aignet-balance-find-xor-pairing-rec ((first litp :type (unsigned-byte 30))
                                         (limit natp)
                                         (level-ref litp)
                                         (rest lit-listp)
                                         levels
                                         (gatesimp gatesimp-p) aignet2 strash)
  :guard (and (fanin-litp first aignet2)
              (fanin-litp level-ref aignet2)
              (aignet-lit-listp rest aignet2)
              (<= (num-fanins aignet2) (u32-length levels)))
  :returns (mv (pairing (iff (litp pairing) pairing))
               (remaining lit-listp))
  :measure (len rest)
  :verify-guards nil
  (b* ((rest (lit-list-fix rest))
       ((when (or (atom rest)
                  (zp limit)
                  (and (not (lit-equiv 0 level-ref))
                       (levels-sort-< (lit-fix level-ref) (car rest) levels))))
        (mv nil rest))
       (candidate (lit-fix (car rest)))
       ((when (eql (lit-id candidate) (lit-id first)))
        (mv candidate (cdr rest)))
       ((mv existing & & &)
        (mbe :logic (aignet-xor-gate-simp/strash first candidate gatesimp strash aignet2)
             :exec (if (<= (car rest) #x1fffffff) ;; bozo
                       (aignet-xor-gate-simp/strash first candidate gatesimp strash aignet2)
                     (ec-call (aignet-xor-gate-simp/strash first candidate gatesimp strash aignet2)))))
       ((when existing)
        (mv candidate (cdr rest)))
       ((mv pairing remaining)
        (aignet-balance-find-xor-pairing-rec first (1- limit) level-ref (cdr rest) levels gatesimp aignet2 strash))
       ((when pairing)
        (mv pairing (cons candidate remaining))))
    (mv nil rest))
  ///
  ;; (local (defthmd make-lit-of-0
  ;;          (equal (make-lit 0 bit) (bfix bit))
  ;;          :hints(("Goal" :in-theory (enable make-lit)))))

  (verify-guards aignet-balance-find-xor-pairing-rec :guard-debug t
    :hints (("goal" :do-not-induct t :in-theory (enable aignet-idp))) :otf-flg t)

  ;; (local (defthm lit-eval-of-make-lit-0
  ;;          (equal (lit-eval (make-lit 0 bit) invals regvals aignet)
  ;;                 (bfix bit))
  ;;          :hints(("Goal" :in-theory (enable lit-eval id-eval)))))

  (defret aignet-balance-find-xor-pairing-rec-correct-when-found
    (implies pairing
             (equal (b-xor (lit-eval pairing invals regvals aignet2)
                           (aignet-eval-parity remaining invals regvals aignet2))
                    (aignet-eval-parity rest invals regvals aignet2)))
    :hints(("Goal" 
            :induct t
            :expand ((:free (a b) (aignet-eval-parity (cons a b) invals regvals aignet2))
                     (aignet-eval-parity rest invals regvals aignet2)
                     (lit-list-fix rest)))
           (and stable-under-simplificationp
                '(:in-theory (enable b-and)))))

  (defret aignet-balance-find-xor-pairing-rec-correct-when-found-rest
    (implies pairing
             (equal (b-xor (lit-eval pairing invals regvals aignet2)
                           (b-xor (aignet-eval-parity remaining invals regvals aignet2)
                                  c))
                    (b-xor (aignet-eval-parity rest invals regvals aignet2)
                           c)))
    :hints(("Goal" 
            :induct t
            :expand ((:free (a b) (aignet-eval-parity (cons a b) invals regvals aignet2))
                     (aignet-eval-parity rest invals regvals aignet2)
                     (lit-list-fix rest)))
           (and stable-under-simplificationp
                '(:in-theory (enable b-and)))))

  (defret aignet-balance-find-xor-pairing-rec-when-not-found
    (implies (not pairing)
             (equal remaining (lit-list-fix rest))))

  (defret len-of-aignet-balance-find-xor-pairing-rec
    (equal (len remaining)
           (if pairing
               (1- (len rest))
             (len rest))))

  (defret aignet-lit-listp-of-aignet-balance-find-xor-pairing-rec
    (implies (aignet-lit-listp rest aignet)
             (aignet-lit-listp remaining aignet))
    :hints(("Goal" :in-theory (enable aignet-lit-listp))))

  (defret aignet-litp-of-aignet-balance-find-xor-pairing-rec
    (implies (and (aignet-lit-listp rest aignet)
                  pairing)
             (aignet-litp pairing aignet))))

(define aignet-balance-find-xor-pairing ((lits lit-listp)
                                         (config balance-config-p)
                                         levels aignet2 strash)
  :guard (and (consp lits)
              (consp (cdr lits))
              (aignet-lit-listp lits aignet2)
              (<= (num-fanins aignet2) (u32-length levels)))
  :returns (mv (first litp) (second litp) (rest lit-listp))
  (b* ((first (lit-fix (car lits)))
       (second (lit-fix (cadr lits)))
       ((balance-config config))
       (level-ref1 (if config.search-higher-levels 0 second))
       ((mv pairing rest)
        ;; second passed in is just used for level comparison, so we do want rest, not rest-rest
        (mbe :logic
             (aignet-balance-find-xor-pairing-rec first config.search-limit level-ref1 (cdr lits) levels config.gatesimp aignet2 strash)
             :exec (if (<= first #x1fffffff) ;; bozo
                       (aignet-balance-find-xor-pairing-rec first config.search-limit level-ref1 (cdr lits) levels config.gatesimp aignet2 strash)
                     (ec-call (aignet-balance-find-xor-pairing-rec first config.search-limit level-ref1 (cdr lits) levels config.gatesimp aignet2 strash)))))
       ((when pairing) (mv first pairing rest))
       ((when (or (not config.search-second-lit)
                  (atom (cddr lits))))
        (mv first second (lit-list-fix (cddr lits))))
       (level-ref2 (if config.search-higher-levels 0 (caddr lits))) 
       ((mv pairing rest)
        (mbe :logic
             (aignet-balance-find-xor-pairing-rec second config.search-limit level-ref2 (cddr lits) levels config.gatesimp aignet2 strash)
             :exec (if (<= second #x1fffffff) ;; bozo
                       (aignet-balance-find-xor-pairing-rec second config.search-limit level-ref2 (cddr lits) levels config.gatesimp aignet2 strash)
                     (ec-call (aignet-balance-find-xor-pairing-rec second config.search-limit level-ref2 (cddr lits) levels config.gatesimp aignet2 strash)))))
       ((when pairing)
        (mv second pairing (cons first rest))))
    (mv first second (lit-list-fix (cddr lits))))
  ///
  (local (defthm move-pairing-over-lit-eval-insts
           (implies (syntaxp (not (and (consp lit) (eq (car lit) 'mv-nth))))
                    (equal (b-xor (lit-eval (mv-nth 0 mv-nth-lit)
                                            invals1 regvals1 aignet1)
                                  (b-xor (lit-eval lit invals regvals aignet)
                                         rest))
                           (b-xor (lit-eval lit invals regvals aignet)
                                  (b-xor (lit-eval (mv-nth 0 mv-nth-lit)
                                                   invals1 regvals1 aignet1)
                                         rest))))
           :hints(("Goal" :in-theory '(b-xor (acl2::zbp))))))
                         

  (defret aignet-balance-find-xor-pairing-correct
    (implies (and (consp lits) (consp (cdr lits)))
             (equal (aignet-eval-parity (list* first second rest) invals regvals aignet2)
                    (aignet-eval-parity lits invals regvals aignet2)))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (a b) (aignet-eval-parity (cons a b) invals regvals aignet2))
                            (aignet-eval-parity lits invals regvals aignet2)
                            (aignet-eval-parity (list (cadr lits)) invals regvals aignet2)
                            (aignet-eval-parity (cdr lits) invals regvals aignet2)
                            (aignet-eval-parity nil invals regvals aignet2)
                            (lit-list-fix lits))))
            (and stable-under-simplificationp
                 '(:in-theory (enable b-xor))))
    :otf-flg t)

  (local (defthm cdr-lit-list-fix
           (equal (cdr (lit-list-fix x))
                  (lit-list-fix (cdr x)))))

  (defret len-of-aignet-balance-find-xor-pairing
    (implies (and (consp lits) (consp (cdr lits)))
             (equal (len rest) (- (len lits) 2))))

  (defret aignet-lit-listp-of-aignet-balance-find-xor-pairing
    (implies (and (aignet-lit-listp lits aignet)
                  (consp lits) (consp (cdr lits)))
             (aignet-lit-listp rest aignet))
    :hints(("Goal" :in-theory (enable aignet-lit-listp))))

  (defret aignet-litp-of-aignet-balance-find-xor-pairing
    (implies (and (aignet-lit-listp lits aignet)
                  (consp lits) (consp (cdr lits)))
             (and (aignet-litp first aignet)
                  (aignet-litp second aignet)))))

(define aignet-balance-build-superxor-rec ((neg bitp)
                                           (lits lit-listp)
                                           (config balance-config-p)
                                           (levels)
                                           (aignet2)
                                           (strash))
  :returns (mv (result-lit litp)
               (new-levels)
               (new-aignet2)
               (new-strash))
  :guard (and (consp lits)
              (aignet-lit-listp lits aignet2)
              (<= (num-fanins aignet2) (u32-length levels)))
  :measure (len lits)
  :prepwork ((local (defthmd mk-lit-0
                      (equal (mk-lit 0 neg) (bfix neg))
                      :hints(("Goal" :in-theory (enable mk-lit))))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable mk-lit-0))))
  (b* (((when (atom (cdr lits)))
        (mv (lit-negate-cond (car lits) neg) levels aignet2 strash))
       ((mv lit1 lit2 rest)
        (aignet-balance-find-xor-pairing lits config levels aignet2 strash))
       ((balance-config config))
       ((mv new-lit strash aignet2) (aignet-hash-xor lit1 lit2 config.gatesimp strash aignet2))
       (levels (aignet-update-node-level (lit-id new-lit) levels aignet2))
       ((when (eql (lit-id new-lit) 0))
        ;; this way we don't insert constant nodes into the list
        (if (consp rest)
            (aignet-balance-build-superxor-rec (b-xor (lit-neg new-lit) neg) rest config levels aignet2 strash)
          (mv (mbe :logic (mk-lit 0 (b-xor (lit-neg new-lit) neg))
                   :exec (b-xor (lit-neg new-lit) neg))
              levels aignet2 strash)))
       (rest (levels-sort-insert new-lit rest levels)))
    (aignet-balance-build-superxor-rec neg rest config levels aignet2 strash))
  ///
  (local (defthm aignet-eval-parity-of-hash-xor
           (b* (((mv lit & new-aignet)
                 (aignet-hash-xor lit1 lit2 gatesimp strash aignet)))
             (implies (and (aignet-litp lit1 aignet)
                           (aignet-litp lit2 aignet))
                      (equal (aignet-eval-parity (cons lit rest) invals regvals new-aignet)
                             (aignet-eval-parity (cons lit1 (cons lit2 rest))
                                                      invals regvals new-aignet))))
           :hints(("Goal" :in-theory (enable aignet-eval-parity b-xor)
                   :do-not-induct t))))


  (local (defthm lit-eval-of-mk-lit-0
           (Equal (lit-eval (mk-lit 0 neg) invals regvals aignet)
                  (bfix neg))
           :hints(("Goal" :in-theory (enable lit-eval id-eval)))))

  (defret aignet-balance-build-superxor-rec-correct
    (implies (and (aignet-lit-listp lits aignet2)
                  (Consp lits))
             (equal (lit-eval result-lit invals regvals new-aignet2)
                    (b-xor neg
                           (aignet-eval-parity lits invals regvals aignet2))))
    :hints (("goal" :induct t
             :expand (<call>
                      (:free (b) (aignet-eval-parity (cons (car lits) b) invals regvals aignet2))
                      (aignet-eval-parity lits invals regvals aignet2)
                      ))
            (and stable-under-simplificationp
                 '(:use ((:instance aignet-eval-parity-of-hash-xor
                          (aignet aignet2)
                          (gatesimp (balance-config->gatesimp config))
                          (lit1 (mv-nth 0 (aignet-balance-find-xor-pairing
                                           lits config levels aignet2 strash)))
                          (lit2 (mv-nth 1 (aignet-balance-find-xor-pairing
                                           lits config levels aignet2 strash)))
                          (rest (mv-nth 2 (aignet-balance-find-xor-pairing
                                           lits config levels aignet2 strash)))))
                   :in-theory (e/d (aignet-eval-parity lit-eval)
                                   (aignet-eval-parity-of-hash-xor
                                    lit-eval-of-aignet-hash-xor))
                   :do-not-induct t))
            ))

  (defret aignet-litp-of-aignet-balance-build-superxor-rec
    (implies (aignet-lit-listp lits aignet2)
             (aignet-litp result-lit new-aignet2))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret levels-length-of-aignet-balance-build-superxor-rec
    (implies (and (<= (num-fanins aignet2) (len levels))
                  (aignet-lit-listp lits aignet2))
             (< (fanin-count new-aignet2) (len new-levels)))
    :hints (("goal" :induct <call> :expand (<call>)))
    :rule-classes :linear)

  (defret aignet-extension-p-of-aignet-balance-build-superxor-rec
    (aignet-extension-p new-aignet2 aignet2))

  (defret stype-counts-of-aignet-balance-build-superxor-rec
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2) (stype-count stype aignet2)))))

(define aignet-balance-build-superxor ((lits lit-listp)
                                       (config balance-config-p)
                                       (levels)
                                       (aignet2)
                                       (strash))
  :returns (mv (result-lit litp)
               (new-levels)
               (new-aignet2)
               (new-strash))
  :guard (and (aignet-lit-listp lits aignet2)
              (<= (num-fanins aignet2) (u32-length levels)))
  :guard-debug t
  :prepwork ((local (defthmd mk-lit-0
                      (equal (mk-lit 0 neg) (bfix neg))
                      :hints(("Goal" :in-theory (enable mk-lit))))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable mk-lit-0))))
  (b* ((lits (lit-list-fix lits))
       ((mv neg lits) (cancel-parity-lits (literal-sort lits) 0))
       ((when (atom lits))
        (mv (mbe :logic (mk-lit 0 neg) :exec neg)
            levels aignet2 strash))
       (lits (levels-sort lits levels)))
    (aignet-balance-build-superxor-rec neg lits config levels aignet2 strash))
  ///
  ;; (local (defthm aignet-lit-listp-lemma
  ;;          (implies (and (aignet-lit-listp lits aignet)
  ;;                        (lit-listp lits))
  ;;                   (and (aignet-lit-listp
  ;;                         (levels-sort-insertsort
  ;;                          (remove k (remove-duplicate-lits (literal-sort-insertsort lits)))
  ;;                          levels)
  ;;                         aignet)
  ;;                        (aignet-lit-listp
  ;;                         (remove k (remove-duplicate-lits (literal-sort-insertsort lits)))
  ;;                         aignet)))))

  ;; (local (defthm consp-of-remove-equal-lemma
  ;;          (implies (lit-listp lits)
  ;;                   (equal (consp (remove k (remove-duplicate-lits (literal-sort-insertsort lits))))
  ;;                          (consp (remove k lits))))))

  (local (defthm lit-eval-of-mk-lit-0
           (Equal (lit-eval (mk-lit 0 neg) invals regvals aignet)
                  (bfix neg))
           :hints(("Goal" :in-theory (enable lit-eval id-eval)))))

  (local (defthm consp-of-levels-sort-insertsort
           (implies (consp x)
                    (consp (levels-sort-insertsort x levels)))))

  (local (defthm aignet-lit-listp-of-levels-sort-insertsort
           (implies (aignet-lit-listp x aignet)
                    (aignet-lit-listp (levels-sort-insertsort x levels) aignet))))

  (local (defthmd lit-eval-when-equal-lit-negate
           (implies (equal (lit-fix x) (lit-negate y))
                    (equal (lit-eval y invals regvals aignet)
                           (b-not (lit-eval x invals regvals aignet))))
           :hints(("Goal" :expand ((:free (x) (lit-eval x invals regvals aignet)))))))

  (local (defthmd cancel-parity-lits-neg-when-all-canceled
           (b* (((mv neg rem) (cancel-parity-lits lits neg1)))
             (implies (not (consp rem))
                      (equal (aignet-eval-parity lits invals regvals aignet)
                             (b-xor neg1 neg))))
           :hints(("Goal" :in-theory (enable cancel-parity-lits aignet-eval-parity
                                             lit-eval-when-equal-lit-negate)))))

  (defret aignet-balance-build-superxor-correct
    (implies (aignet-lit-listp lits aignet2)
             (equal (lit-eval result-lit invals regvals new-aignet2)
                    (aignet-eval-parity lits invals regvals aignet2)))
    :hints (("goal" :use ((:instance cancel-parity-lits-neg-when-all-canceled
                           (lits (literal-sort (lit-list-fix lits)))
                           (neg1 0)
                           (aignet aignet2))))))

  (defret aignet-litp-of-aignet-balance-build-superxor
    (implies (aignet-lit-listp lits aignet2)
             (aignet-litp result-lit new-aignet2)))

  (defret levels-length-of-aignet-balance-build-superxor
    (implies (and (<= (num-fanins aignet2) (len levels))
                  (aignet-lit-listp lits aignet2))
             (< (fanin-count new-aignet2) (len new-levels)))
    :rule-classes :linear)

  (defret aignet-extension-p-of-aignet-balance-build-superxor
    (aignet-extension-p new-aignet2 aignet2))

  (defret stype-counts-of-aignet-balance-build-superxor
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2) (stype-count stype aignet2)))))





(defines aignet-balance-rec
  (define aignet-balance-rec ((node natp)
                              (config balance-config-p)
                              (aignet "input")
                              (mark "completed nodes")
                              (copy "mapping from input to output")
                              (refcounts "for input network")
                              (levels "for output network")
                              (aignet2 "output")
                              (strash "for output network"))
    :guard (and (< node (num-fanins aignet))
                (<= (num-fanins aignet) (lits-length copy))
                (non-exec (ec-call (aignet-copies-in-bounds copy aignet2)))
                (<= (num-fanins aignet) (bits-length mark))
                (<= (num-fanins aignet) (u32-length refcounts))
                (<= (num-fanins aignet2) (u32-length levels)))
    :returns (mv (copy-lit litp) new-mark new-copy new-levels new-aignet2 new-strash)
    :verify-guards nil
    :measure (acl2::two-nats-measure (nfix node) 0)
    (b* (((when (or (eql (get-bit node mark) 1)
                    (not (eql (id->type node aignet) (gate-type)))))
          (b* ((mark (set-bit node 1 mark)))
            (mv (get-lit node copy) mark copy levels aignet2 strash)))
         (xorp (eql (id->regp node aignet) 1))
         ((balance-config config))
         ((mv supergate &)
          (if xorp
              (lit-collect-superxor (make-lit node 0) t config.supergate-limit nil refcounts aignet)
            (lit-collect-supergate (make-lit node 0) t nil config.supergate-limit nil refcounts aignet)))
         ((mv copy-lits mark copy levels aignet2 strash)
          (aignet-balance-list-rec supergate config aignet mark copy refcounts levels aignet2 strash))
         ((mv result-lit levels aignet2 strash)
          (if xorp
              (aignet-balance-build-superxor copy-lits config levels aignet2 strash)
            (aignet-balance-build-supergate copy-lits config levels aignet2 strash)))
         (mark (set-bit node 1 mark))
         (copy (set-lit node result-lit copy)))
      (mv result-lit mark copy levels aignet2 strash)))

  (define aignet-balance-list-rec ((lits lit-listp)
                                   (config balance-config-p)
                                   (aignet "input")
                                   (mark "completed nodes")
                                   (copy "mapping from input to output")
                                   (refcounts "for input network")
                                   (levels "for output network")
                                   (aignet2 "output")
                                   (strash "for output network"))
    :guard (and (aignet-lit-listp lits aignet)
                (<= (num-fanins aignet) (lits-length copy))
                (non-exec (ec-call (aignet-copies-in-bounds copy aignet2)))
                (<= (num-fanins aignet) (bits-length mark))
                (<= (num-fanins aignet) (u32-length refcounts))
                (<= (num-fanins aignet2) (u32-length levels)))
    :returns (mv (copy-lits lit-listp) new-mark new-copy new-levels new-aignet2 new-strash)
    :measure (acl2::two-nats-measure (lits-max-id-val lits) (+ 1 (len lits)))
    (b* (((When (atom lits))
          (mv nil mark copy levels aignet2 strash))
         ((mv lit1 mark copy levels aignet2 strash)
          (aignet-balance-rec (lit-id (car lits)) config aignet mark copy refcounts levels aignet2 strash))
         ((mv rest-lits mark copy levels aignet2 strash)
          (aignet-balance-list-rec (cdr lits) config aignet mark copy refcounts levels aignet2 strash)))
      (mv (cons (lit-negate-cond lit1 (lit-neg (car lits))) rest-lits)
          mark copy levels aignet2 strash)))
  ///
  ;; (local (defthm aignet-litp-of-make-lit
  ;;          (implies (and (<= (nfix id) (fanin-count aignet))
  ;;                        (not (equal (ctype (stype (car (lookup-id id aignet)))) :output)))
  ;;                   (aignet-litp (make-lit id 0) aignet))
  ;;          :hints(("Goal" :in-theory (enable aignet-idp)))))

  (local (in-theory (disable aignet-balance-rec aignet-balance-list-rec)))

  (std::defret-mutual aignet-extension-p-of-aignet-balance-rec
    (defret aignet-extension-p-of-aignet-balance-rec
      (aignet-extension-p new-aignet2 aignet2)
      :hints ('(:expand (<call>)))
      :fn aignet-balance-rec)
    (defret aignet-extension-p-of-aignet-balance-list-rec
      (aignet-extension-p new-aignet2 aignet2)
      :hints ('(:expand (<call>)))
      :fn aignet-balance-list-rec))

  (std::defret-mutual aignet-litp-of-aignet-balance-rec
    (defret aignet-litp-of-aignet-balance-rec
      (implies (and (aignet-copies-in-bounds copy aignet2)
                    (< (nfix node) (num-fanins aignet)))
               (and (aignet-copies-in-bounds new-copy new-aignet2)
                    (aignet-litp copy-lit new-aignet2)))
      :hints ('(:expand (<call>)))
      :fn aignet-balance-rec)
    (defret aignet-litp-of-aignet-balance-list-rec
      (implies (and (aignet-copies-in-bounds copy aignet2)
                    (aignet-lit-listp lits aignet))
               (and (aignet-copies-in-bounds new-copy new-aignet2)
                    (aignet-lit-listp copy-lits new-aignet2)))
      :hints ('(:expand (<call>) :in-theory (enable aignet-idp)))
      :fn aignet-balance-list-rec))
  
  (std::defret-mutual levels-length-of-aignet-balance-rec
    (defret levels-length-of-aignet-balance-rec
      (implies (and (<= (num-fanins aignet2) (len levels))
                    (aignet-copies-in-bounds copy aignet2)
                    (< (nfix node) (num-fanins aignet)))
               (< (fanin-count new-aignet2) (len new-levels)))
      :hints ('(:expand (<call>)))
      :fn aignet-balance-rec
      :rule-classes :linear)
    (defret levels-length-of-aignet-balance-list-rec
      (implies (and (<= (num-fanins aignet2) (len levels))
                    (aignet-copies-in-bounds copy aignet2)
                    (aignet-lit-listp lits aignet))
               (< (fanin-count new-aignet2) (len new-levels)))
      :hints ('(:expand (<call>) :in-theory (enable aignet-idp)))
      :fn aignet-balance-list-rec
      :rule-classes :linear))

  (std::defret-mutual mark-length-of-aignet-balance-rec
    (defret mark-length-of-aignet-balance-rec
      (implies (and (<= (num-fanins aignet) (len mark))
                    (< (nfix node) (num-fanins aignet)))
               (equal (len new-mark) (len mark)))
      :hints ('(:expand (<call>)))
      :fn aignet-balance-rec)
    (defret mark-length-of-aignet-balance-list-rec
      (implies (and (<= (num-fanins aignet) (len mark))
                    (aignet-lit-listp lits aignet))
               (equal (len new-mark) (len mark)))
      :hints ('(:expand (<call>) :in-theory (enable aignet-idp)))
      :fn aignet-balance-list-rec))

  (std::defret-mutual copy-length-of-aignet-balance-rec
    (defret copy-length-of-aignet-balance-rec
      (implies (and (<= (num-fanins aignet) (len copy))
                    (< (nfix node) (num-fanins aignet)))
               (equal (len new-copy) (len copy)))
      :hints ('(:expand (<call>)))
      :fn aignet-balance-rec)
    (defret copy-length-of-aignet-balance-list-rec
      (implies (and (<= (num-fanins aignet) (len copy))
                    (aignet-lit-listp lits aignet))
               (equal (len new-copy) (len copy)))
      :hints ('(:expand (<call>) :in-theory (enable aignet-idp)))
      :fn aignet-balance-list-rec))

  (verify-guards aignet-balance-rec
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defun-sk marked-lit-copies-equiv (mark copy aignet aignet2 invals regvals)
    (forall (n)
            (implies (and (not (equal (id->type n aignet) (out-type)))
                          (or (equal 1 (nth n mark))
                              (not (equal (id->type n aignet) (gate-type)))))
                     (equal (lit-eval (nth-lit n copy) invals regvals aignet2)
                            (id-eval n invals regvals aignet))))
    :rewrite :direct)

  (in-theory (disable marked-lit-copies-equiv))

  (defthm marked-lit-copies-equiv-of-extension
    (implies (and (aignet-extension-binding)
                  (marked-lit-copies-equiv mark copy aignet orig invals regvals)
                  (aignet-copies-in-bounds copy orig))
             (marked-lit-copies-equiv mark copy aignet new invals regvals))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))
             

  (std::defret-mutual marks-remain-set-of-aignet-balance-rec
    (defret marks-remain-set-of-aignet-balance-rec
      (implies (equal (nth n mark) 1)
               (equal (nth n new-mark) 1))
      :hints ('(:expand (<call>)))
      :fn aignet-balance-rec)
    (defret marks-remain-set-of-aignet-balance-list-rec
      (implies (equal (nth n mark) 1)
               (equal (nth n new-mark) 1))
      :hints ('(:expand (<call>)))
      :fn aignet-balance-list-rec))


  (defret mark-set-of-aignet-balance-rec
    (equal (nth node new-mark) 1)
    :hints (("goal" :expand (<call>)))
    :fn aignet-balance-rec)

  ;; (defun lit-list-marks-set (x mark)
  ;;   (if (atom x)
  ;;       t
  ;;     (and (equal (nth (lit-id (car x)) mark) 1)
  ;;          (lit-list-marks-set (cdr x) mark))))

  ;; (defun lits-copy-each (x copy)
  ;;   (if (atom x)
  ;;       nil
  ;;     (cons (nth-lit (car x) copy)
  ;;           (lits-copy-each (cdr x) copy))))


  ;; (std::defret-mutual mark-set-of-aignet-balance-list-rec
  ;;   (defret mark-set-of-aignet-balance-list-rec
  ;;     (lit-list-marks-set lits new-mark)
  ;;     :hints ('(:expand (<call>)))
  ;;     :fn aignet-balance-list-rec)
  ;;   :skip-others t)

  ;; (std::defret-mutual copies-preserved-of-aignet-balance-rec
  ;;   (defret copies-preserved-of-aignet-balance-rec
  ;;     (implies (equal (nth n mark) 1)
  ;;              (equal (nth-lit n new-copy)
  ;;                     (nth-lit n copy)))
  ;;     :hints ('(:expand (<call>)))
  ;;     :fn aignet-balance-rec)
  ;;   (defret copies-preserved-of-aignet-balance-list-rec
  ;;     (implies (equal (nth n mark) 1)
  ;;              (equal (nth-lit n new-copy)
  ;;                     (nth-lit n copy)))
  ;;     :hints ('(:expand (<call>)))
  ;;     :fn aignet-balance-list-rec))

  ;; (std::defret-mutual copies-preserved-of-aignet-balance-rec
  ;;   (defret copies-preserved-of-aignet-balance-rec
  ;;     (implies (equal (nth n mark) 1)
  ;;              (equal (nth-lit n new-copy)
  ;;                     (nth-lit n copy)))
  ;;     :hints ('(:expand (<call>)))
  ;;     :fn aignet-balance-rec)
  ;;   (defret copies-preserved-of-aignet-balance-list-rec
  ;;     (implies (equal (nth n mark) 1)
  ;;              (equal (nth-lit n new-copy)
  ;;                     (nth-lit n copy)))
  ;;     :hints ('(:expand (<call>)))
  ;;     :fn aignet-balance-list-rec))

  ;; (std::defret-mutual lit-result-of-aignet-balance-rec
  ;;   (defret copies-preserved-of-aignet-balance-rec
  ;;     (equal copy-lit (nth-lit node new-copy))
  ;;     :hints ('(:expand (<call>)))
  ;;     :fn aignet-balance-rec)
  ;;   (defret copies-preserved-of-aignet-balance-list-rec
  ;;     (equal copy-lits (lits-copy-each lits new-copy))
  ;;     :hints ('(:expand (<call>)))
  ;;     :fn aignet-balance-list-rec))

  ;; (defthm aignet-eval-conjunction-under-marked-lit-copies-equiv
  ;;   (implies (and (marked-lit-copies-equiv mark copy aignet aignet2)
  ;;                 (lit-list-marks-set lits mark))
  ;;            (equal (aignet-eval-conjunction 

  (local (defthm aignet-eval-parity-of-nil
           (equal (aignet-eval-parity nil invals regvals aignet) 0)
           :hints(("Goal" :in-theory (enable aignet-eval-parity)))))
  

  (std::defret-mutual aignet-balance-rec-correct
    (defret aignet-balance-rec-correct
      (implies (and (marked-lit-copies-equiv mark copy aignet aignet2 invals regvals)
                    (aignet-copies-in-bounds copy aignet2)
                    (< (nfix node) (num-fanins aignet)))
               (and (marked-lit-copies-equiv new-mark new-copy aignet new-aignet2 invals regvals)
                    (implies (not (equal (id->type node aignet) (out-type)))
                             (equal (lit-eval copy-lit invals regvals new-aignet2)
                                    (id-eval node invals regvals aignet)))))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   (eq (caar (last clause)) 'marked-lit-copies-equiv)
                   `(:expand (,(car (last clause)))))
              (and stable-under-simplificationp
                   (let ((witness (acl2::find-call-lst
                                   'marked-lit-copies-equiv-witness
                                   clause)))
                     (and witness
                          `(:clause-processor
                            (acl2::simple-generalize-cp
                             clause '((,witness . some-node)))))))
              (and stable-under-simplificationp
                   '(:expand ((lit-eval (make-lit node 0) invals regvals aignet)))))
      :fn aignet-balance-rec)
    (defret aignet-balance-list-rec-correct
      (implies (and (marked-lit-copies-equiv mark copy aignet aignet2 invals regvals)
                    (aignet-copies-in-bounds copy aignet2)
                    (aignet-lit-listp lits aignet))
               (and (marked-lit-copies-equiv new-mark new-copy aignet new-aignet2 invals regvals)
                    (equal (aignet-eval-conjunction copy-lits invals regvals new-aignet2)
                           (aignet-eval-conjunction lits invals regvals aignet))
                    (equal (aignet-eval-parity copy-lits invals regvals new-aignet2)
                           (aignet-eval-parity lits invals regvals aignet))))
      :hints ('(:expand (<call>
                         (:free (a b aignet2) (aignet-eval-conjunction (cons a b) invals regvals aignet2))
                         (:free (aignet2) (aignet-eval-conjunction nil invals regvals aignet2))
                         (aignet-eval-conjunction lits invals regvals aignet)
                         (:free (a b aignet2) (aignet-eval-parity (cons a b) invals regvals aignet2))
                         (:free (aignet2) (aignet-eval-parity nil invals regvals aignet2))
                         (aignet-eval-parity lits invals regvals aignet)
                         (lit-eval (car lits) invals regvals aignet))
                :in-theory (enable aignet-idp)))
      :fn aignet-balance-list-rec))

  (std::defret-mutual stype-counts-of-aignet-balance-rec
    (defret stype-counts-of-aignet-balance-rec
      (implies (and (not (equal (stype-fix stype) (and-stype)))
                    (not (equal (stype-fix stype) (xor-stype))))
               (equal (stype-count stype new-aignet2) (stype-count stype aignet2)))
      :hints ('(:expand (<call>)))
      :fn aignet-balance-rec)
    (defret stype-counts-of-aignet-balance-list-rec
      (implies (and (not (equal (stype-fix stype) (and-stype)))
                    (not (equal (stype-fix stype) (xor-stype))))
               (equal (stype-count stype new-aignet2) (stype-count stype aignet2)))
      :hints ('(:expand (<call>)))
      :fn aignet-balance-list-rec))

  (fty::deffixequiv-mutual aignet-balance-rec))





(defun-sk aignet-output-fanins-marked (mark aignet)
  (forall n
          (implies (< (nfix n) (num-outs aignet))
                   (b* ((out-suffix (lookup-stype n :po aignet)))
                     (equal (nth (lit-id (fanin 0 out-suffix))
                                 mark)
                            1))))
  :rewrite :direct)

(defun-sk aignet-nxst-fanins-marked (mark aignet)
  (forall n
          (implies (< (nfix n) (num-regs aignet))
                   (b* ((nxst-lit (lookup-reg->nxst n aignet)))
                     (equal (nth (lit-id nxst-lit) mark)
                            1))))
  :rewrite :direct)

(defun-sk marked-lit-copies-equiv-all-evals (mark copy aignet aignet2)
  (forall (invals regvals)
          (marked-lit-copies-equiv mark copy aignet aignet2 invals regvals))
  :rewrite :direct)

(defthm marked-lit-copies-equiv-all-evals-rw
  (IMPLIES (AND (marked-lit-copies-equiv-all-evals mark copy aignet aignet2)
                (NOT (EQUAL (ID->TYPE N AIGNET) (OUT-TYPE)))
                (OR (EQUAL 1 (NTH N MARK))
                    (NOT (EQUAL (ID->TYPE N AIGNET)
                                (GATE-TYPE)))))
           (EQUAL (LIT-EVAL (NTH-LIT N COPY)
                            INVALS REGVALS AIGNET2)
                  (ID-EVAL N INVALS REGVALS AIGNET)))
  :hints (("goal" :use marked-lit-copies-equiv-all-evals-necc
           :in-theory (disable marked-lit-copies-equiv-all-evals-necc))))

(in-theory (disable aignet-output-fanins-marked
                    aignet-nxst-fanins-marked
                    marked-lit-copies-equiv-all-evals))

(local
 (defsection init-copy-comb-balance
   (local (in-theory (enable init-copy-comb)))
   (local (std::set-define-current-function init-copy-comb))

   (local (defthm lit-eval-when-const
            (implies (equal (stype (car (lookup-id n aignet))) :const)
                     (equal (lit-eval (make-lit n neg) invals regvals aignet)
                            (bfix neg)))
            :hints(("Goal" :expand ((lit-eval (make-lit n neg) invals regvals aignet)
                                    (id-eval n invals regvals aignet))))))

   (local (defthm nth-lit-of-nil
            (equal (nth-lit n nil) 0)
            :hints(("Goal" :in-theory (enable nth-lit nth)))))

   (defret marked-lit-copies-equiv-of-balance-init-copy
     (marked-lit-copies-equiv (resize-list nil n 0) new-copy aignet new-aignet2 invals regvals)
     :hints((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
            (and stable-under-simplificationp
                 (let ((witness (acl2::find-call-lst
                                 'marked-lit-copies-equiv-witness
                                 clause)))
                   `(:clause-processor
                     (acl2::simple-generalize-cp
                      clause '((,witness . some-node))))))
            (and stable-under-simplificationp
                 '(:expand ((:free (aignet n) (lit-eval (make-lit n 0) invals regvals aignet))
                            (:free (count stype aignet aignet2)
                             (id-eval (fanin-count (lookup-stype count stype aignet))
                                      invals regvals aignet2))
                            (id-eval some-node invals regvals aignet))))))

   (defret marked-lit-copies-equiv-all-evals-of-balance-init-copy
     (marked-lit-copies-equiv-all-evals (resize-list nil n 0) new-copy aignet new-aignet2)
     :hints (("goal" :in-theory (e/d (marked-lit-copies-equiv-all-evals)
                                     (init-copy-comb)))))))



(define aignet-balance-outs ((n natp)
                             (config balance-config-p)
                             (aignet "input")
                             (mark "completed nodes")
                             (copy "mapping from input to output")
                             (refcounts "for input network")
                             (levels "for output network")
                             (aignet2 "output")
                             (strash "for output network"))
  :guard (and (<= n (num-outs aignet))
              (<= (num-fanins aignet) (lits-length copy))
              (non-exec (ec-call (aignet-copies-in-bounds copy aignet2)))
              (<= (num-fanins aignet) (bits-length mark))
              (<= (num-fanins aignet) (u32-length refcounts))
              (<= (num-fanins aignet2) (u32-length levels)))
  :returns (mv new-mark new-copy new-levels new-aignet2 new-strash)
  :measure (nfix (- (num-outs aignet) (nfix n)))
  :verify-guards nil
  (b* (((when (mbe :logic (zp (- (num-outs aignet) (nfix n)))
                   :exec (eql n (num-outs aignet))))
        (mv mark copy levels aignet2 strash))
       (- (and (>= (balance-config->verbosity-level config) 1)
               (b* (((acl2::local-stobjs u32arr)
                     (mv blah u32arr))
                    (u32arr (resize-u32 (num-fanins aignet) u32arr))
                    ((mv supergate &)
                     (lit-collect-supergate (outnum->fanin n aignet)
                                            t nil
                                            (balance-config->supergate-limit config)
                                            nil u32arr aignet)))
                 (cw "Input supergate size: ~x0~%" (len supergate))
                 (cw "Gate numbers: ~x0~%" (count-gates-list supergate aignet))
                 (mv nil u32arr))))
       ((mv ?lit mark copy levels aignet2 strash)
        (aignet-balance-rec (lit-id (outnum->fanin n aignet))
                            config aignet mark copy refcounts levels aignet2 strash))
       (- (and (>= (balance-config->verbosity-level config) 1)
               (b* (((acl2::local-stobjs u32arr)
                     (mv blah u32arr))
                    (u32arr (resize-u32 (num-fanins aignet2) u32arr))
                    ((mv supergate &)
                     (lit-collect-supergate lit t nil
                                            (balance-config->supergate-limit config)
                                            nil u32arr aignet2)))
                 (cw "Output supergate size: ~x0~%" (len supergate))
                 (cw "Gate numbers: ~x0~%" (count-gates-list supergate aignet2))
                 (mv nil u32arr)))))
    (aignet-balance-outs (1+ (lnfix n)) config aignet mark copy refcounts levels aignet2 strash))
  ///
  (defret aignet-extension-p-of-aignet-balance-outs
    (aignet-extension-p new-aignet2 aignet2))

  (defret aignet-copies-in-bounds-of-aignet-balance-outs
    (implies (aignet-copies-in-bounds copy aignet2)
             (aignet-copies-in-bounds new-copy new-aignet2)))

  (defret levels-length-of-aignet-balance-outs
    (implies (and (<= (num-fanins aignet2) (len levels))
                  (aignet-copies-in-bounds copy aignet2))
             (< (fanin-count new-aignet2) (len new-levels)))
    :rule-classes :linear)

  (defret mark-length-of-aignet-balance-outs
    (implies (<= (num-fanins aignet) (len mark))
             (equal (len new-mark) (len mark))))

  (defret copy-length-of-aignet-balance-outs
    (implies (<= (num-fanins aignet) (len copy))
             (equal (len new-copy) (len copy))))

  (local (defthm less-than-max-fanin-when-aignet-idp
           (implies (aignet-litp x aignet)
                    (< (lit-id x) (+ 1 (fanin-count aignet))))
           :hints(("Goal" :in-theory (enable aignet-idp)))))

  (verify-guards aignet-balance-outs)
  

  (defret marks-remain-set-of-aignet-balance-outs
    (implies (equal (nth m mark) 1)
             (equal (nth m new-mark) 1)))

  (local (in-theory (enable* acl2::arith-equiv-forwarding)))

  (defret output-fanin-marked-of-aignet-balance-outs
    (implies (and (<= (nfix n) (nfix m))
                  (< (nfix m) (num-outs aignet)))
             (equal (nth (lit-id (fanin 0 (lookup-stype m :po aignet))) new-mark) 1)))

  (defret aignet-output-fanins-marked-of-aignet-balance-outs
    (implies (zp n)
             (aignet-output-fanins-marked new-mark aignet))
    :hints(("Goal" :expand ((aignet-output-fanins-marked new-mark aignet)))))


  (defret aignet-balance-outs-correct
    (implies (and (marked-lit-copies-equiv mark copy aignet aignet2 invals regvals)
                  (aignet-copies-in-bounds copy aignet2))
             (marked-lit-copies-equiv new-mark new-copy aignet new-aignet2 invals regvals)))

  (defret aignet-balance-outs-correct-all-evals
    (implies (and (marked-lit-copies-equiv-all-evals mark copy aignet aignet2)
                  (aignet-copies-in-bounds copy aignet2))
             (marked-lit-copies-equiv-all-evals new-mark new-copy aignet new-aignet2))
    :hints (("goal" :in-theory (disable aignet-balance-outs))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defret stype-counts-of-aignet-balance-outs
    (implies (And (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2) (stype-count stype aignet2)))))



(define aignet-balance-nxsts ((n natp)
                              (config balance-config-p)
                             (aignet "input")
                             (mark "completed nodes")
                             (copy "mapping from input to output")
                             (refcounts "for input network")
                             (levels "for output network")
                             (aignet2 "output")
                             (strash "for output network"))
  :guard (and (<= n (num-regs aignet))
              (<= (num-fanins aignet) (lits-length copy))
              (non-exec (ec-call (aignet-copies-in-bounds copy aignet2)))
              (<= (num-fanins aignet) (bits-length mark))
              (<= (num-fanins aignet) (u32-length refcounts))
              (<= (num-fanins aignet2) (u32-length levels)))
  :returns (mv new-mark new-copy new-levels new-aignet2 new-strash)
  :measure (nfix (- (num-regs aignet) (nfix n)))
  :verify-guards nil
  (b* (((when (mbe :logic (zp (- (num-regs aignet) (nfix n)))
                   :exec (eql n (num-regs aignet))))
        (mv mark copy levels aignet2 strash))
       ((mv ?lit mark copy levels aignet2 strash)
        (aignet-balance-rec (lit-id (regnum->nxst n aignet))
                            config aignet mark copy refcounts levels aignet2 strash)))
    (aignet-balance-nxsts (1+ (lnfix n)) config aignet mark copy refcounts levels aignet2 strash))
  ///
  (defret aignet-extension-p-of-aignet-balance-nxsts
    (aignet-extension-p new-aignet2 aignet2))

  (defret aignet-copies-in-bounds-of-aignet-balance-nxsts
    (implies (aignet-copies-in-bounds copy aignet2)
             (aignet-copies-in-bounds new-copy new-aignet2)))

  (defret levels-length-of-aignet-balance-nxsts
    (implies (and (<= (num-fanins aignet2) (len levels))
                  (aignet-copies-in-bounds copy aignet2))
             (< (fanin-count new-aignet2) (len new-levels)))
    :rule-classes :linear)

  (defret mark-length-of-aignet-balance-nxsts
    (implies (<= (num-fanins aignet) (len mark))
             (equal (len new-mark) (len mark))))

  (defret copy-length-of-aignet-balance-nxsts
    (implies (<= (num-fanins aignet) (len copy))
             (equal (len new-copy) (len copy))))

  (verify-guards aignet-balance-nxsts)
  

  (defret marks-remain-set-of-aignet-balance-nxsts
    (implies (equal (nth m mark) 1)
             (equal (nth m new-mark) 1)))

  (defret aignet-output-fanins-marked-preserved-of-aignet-balance-nxsts
    (implies (aignet-output-fanins-marked mark aignet)
             (aignet-output-fanins-marked new-mark aignet))
    :hints (("goal" :in-theory (disable aignet-balance-nxsts))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (local (in-theory (enable* acl2::arith-equiv-forwarding)))

  (defret nxst-fanin-marked-of-aignet-balance-nxsts
    (implies (and (<= (nfix n) (nfix m))
                  (< (nfix m) (num-regs aignet)))
             (equal (nth (lit-id (lookup-reg->nxst m aignet)) new-mark) 1)))

  (defret aignet-nxst-fanins-marked-of-aignet-balance-nxsts
    (implies (zp n)
             (aignet-nxst-fanins-marked new-mark aignet))
    :hints(("Goal" :expand ((aignet-nxst-fanins-marked new-mark aignet)))))


  (defret aignet-balance-nxsts-correct
    (implies (and (marked-lit-copies-equiv mark copy aignet aignet2 invals regvals)
                  (aignet-copies-in-bounds copy aignet2))
             (marked-lit-copies-equiv new-mark new-copy aignet new-aignet2 invals regvals)))

  (defret aignet-balance-nxsts-correct-all-evals
    (implies (and (marked-lit-copies-equiv-all-evals mark copy aignet aignet2)
                  (aignet-copies-in-bounds copy aignet2))
             (marked-lit-copies-equiv-all-evals new-mark new-copy aignet new-aignet2))
    :hints (("goal" :in-theory (disable aignet-balance-nxsts))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defret stype-counts-of-aignet-balance-nxsts
    (implies (And (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2) (stype-count stype aignet2)))))


(local
 (Defsection finish-copy-comb-balance
   (local (in-theory (enable finish-copy-comb)))
   (local (std::set-define-current-function finish-copy-comb))

   (local (defthm marked-lit-copies-equiv-implies-output-fanins-comb-equiv
            (implies (and (marked-lit-copies-equiv-all-evals mark copy aignet aignet2)
                          (aignet-output-fanins-marked mark aignet))
                     (output-fanins-comb-equiv aignet copy aignet2))
            :hints(("Goal" :in-theory (e/d (output-fanins-comb-equiv lit-copy lit-eval)
                                           (output-fanins-comb-equiv-necc))))))

   (local (defthm marked-lit-copies-equiv-implies-nxst-fanins-comb-equiv
            (implies (and (marked-lit-copies-equiv-all-evals mark copy aignet aignet2)
                          (aignet-nxst-fanins-marked mark aignet))
                     (nxst-fanins-comb-equiv aignet copy aignet2))
            :hints(("Goal" :in-theory (e/d (nxst-fanins-comb-equiv lit-copy lit-eval)
                                           (nxst-fanins-comb-equiv-necc))))))

   (defun finish-copy-comb-balance-bind-mark (aignet2)
     (case-match aignet2
       (('mv-nth ''3 call) `((mark . (mv-nth '0 ,call))))
       (& nil)))

   (defret finish-copy-comb-balance-comb-equivalent
     (implies (and (bind-free (finish-copy-comb-balance-bind-mark aignet2) (mark))
                   (marked-lit-copies-equiv-all-evals mark copy aignet aignet2)
                   (aignet-copies-in-bounds copy aignet2)
                   (aignet-nxst-fanins-marked mark aignet)
                   (aignet-output-fanins-marked mark aignet)
                   (equal (stype-count :po aignet2) 0)
                   (equal (stype-count :nxst aignet2) 0)
                   (equal (stype-count :reg aignet2)
                          (stype-count :reg aignet)))
              (comb-equiv new-aignet2 aignet))
     :hints(("Goal" :in-theory (e/d (comb-equiv) (finish-copy-comb)))))))

  

;; (define balance-finish-copy ((aignet)
;;                              (copy)
;;                              (aignet2)
;;                              mark) ;; to make reasoning easier
;;   (declare (ignore mark))
;;   :guard (and (<= (num-fanins aignet) (lits-length copy))
;;               (aignet-copies-ok (num-fanins aignet) copy aignet2)
;;               (<= (num-regs aignet) (num-regs aignet2)))
;;   :returns (new-aignet2)
;;   (finish-copy-comb aignet copy aignet2)
;;   ///
;;   (local (defthm not-nxst-or-po-by-ctype
;;            (implies (not (Equal (ctype stype) :output))
;;                     (and (not (equal (stype-fix stype) :nxst))
;;                          (not (equal (stype-fix stype) :po))))
;;            :hints(("Goal" :in-theory (enable ctype)))))

;;   (defret non-output-stype-count-of-balance-finish-copy
;;     (implies (not (equal (ctype stype) :output))
;;              (equal (stype-count stype new-aignet2)
;;                     (stype-count stype aignet2))))

;;   (defret num-outs-of-balance-finish-copy
;;     (equal (stype-count :po new-aignet2)
;;            (+ (stype-count :po aignet) (stype-count :po aignet2))))

;;   (local (in-theory (enable finish-copy-comb)))

;;   (local (defthm lookup-reg->nxst-stype
;;            (not (equal (stype (car (lookup-reg->nxst reg aignet))) :gate))
;;            :hints(("Goal" :in-theory (enable lookup-reg->nxst)))))
  

;;   (local (in-theory (enable lookup-stype-in-bounds)))


;;   (local (defthm fanin-count-of-aignet-copy-outs-from-fanins-iter
;;            (equal (fanin-count (aignet-copy-outs-from-fanins-iter n aignet copy aignet2))
;;                   (+ (nfix n) (fanin-count aignet2)))
;;            :hints(("Goal" :in-theory (enable aignet-copy-outs-from-fanins-iter)))))

;;   (local (defthm fanin-count-of-aignet-copy-outs-from-fanins
;;            (equal (fanin-count (aignet-copy-outs-from-fanins aignet copy aignet2))
;;                   (+ (num-outs aignet) (fanin-count aignet2)))
;;            :hints(("Goal" :in-theory (enable aignet-copy-outs-from-fanins)))))

;;   (local (in-theory (enable aignet-idp)))


;;   (local (defret balance-finish-copy-outs-comb-equiv
;;            (implies (and (marked-lit-copies-equiv-all-evals mark copy aignet aignet2)
;;                          (aignet-copies-in-bounds copy aignet2)
;;                          (aignet-output-fanins-marked mark aignet)
;;                          (equal (stype-count :po aignet2) 0))
;;                     (outs-comb-equiv new-aignet2 aignet))
;;            :hints(("Goal" :in-theory (e/d (outs-comb-equiv output-eval)))
;;                   (and stable-under-simplificationp
;;                        (let ((witness (acl2::find-call-lst
;;                                        'outs-comb-equiv-witness
;;                                        clause)))
;;                          `(:clause-processor
;;                            (acl2::simple-generalize-cp
;;                             clause '(((mv-nth '0 ,witness) . n)
;;                                      ((mv-nth '1 ,witness) . invals)
;;                                      ((mv-nth '2 ,witness) . regvals))))))
;;                   (and stable-under-simplificationp
;;                        '(:cases ((< (nfix n) (num-outs aignet)))
;;                          :expand ((:free (suff aignet)
;;                                    (id-eval (fanin-count suff) invals regvals aignet))
;;                                   (:free (suff aignet)
;;                                    (id-eval (+ 1 (nfix n) (fanin-count suff)) invals regvals aignet))
;;                                   (aignet-copy-outs-from-fanins-iter (+ 1 (nfix n)) aignet copy aignet2)
;;                                   (:free (x)
;;                                    (lit-eval (fanin 0 x)
;;                                              invals regvals aignet))))))))

  
;;   (local (defthm fanin-count-of-aignet-copy-nxsts-from-fanins-iter
;;            (equal (fanin-count (aignet-copy-nxsts-from-fanins-iter n aignet copy aignet2))
;;                   (+ (nfix n) (fanin-count aignet2)))
;;            :hints(("Goal" :in-theory (enable aignet-copy-nxsts-from-fanins-iter)))))

;;   (local (defthm fanin-count-of-aignet-copy-nxsts-from-fanins
;;            (equal (fanin-count (aignet-copy-nxsts-from-fanins aignet copy aignet2))
;;                   (+ (num-regs aignet) (fanin-count aignet2)))
;;            :hints(("Goal" :in-theory (enable aignet-copy-nxsts-from-fanins)))))

;;   (local (in-theory (enable aignet-idp)))

;;   (local (acl2::use-trivial-ancestors-check))

;;   (local (defret balance-finish-copy-nxsts-comb-equiv
;;            (implies (and (marked-lit-copies-equiv-all-evals mark copy aignet aignet2)
;;                          (aignet-copies-in-bounds copy aignet2)
;;                          (aignet-nxst-fanins-marked mark aignet)
;;                          (equal (stype-count :nxst aignet2) 0)
;;                          (equal (stype-count :reg aignet) (stype-count :reg aignet2)))
;;                     (nxsts-comb-equiv new-aignet2 aignet))
;;            :hints(("Goal" :in-theory (e/d (nxsts-comb-equiv nxst-eval)))
;;                   (and stable-under-simplificationp
;;                        (let ((witness (acl2::find-call-lst
;;                                        'nxsts-comb-equiv-witness
;;                                        clause)))
;;                          `(:clause-processor
;;                            (acl2::simple-generalize-cp
;;                             clause '(((mv-nth '0 ,witness) . n)
;;                                      ((mv-nth '1 ,witness) . invals)
;;                                      ((mv-nth '2 ,witness) . regvals))))))
;;                   (and stable-under-simplificationp
;;                        '(:cases ((< (nfix n) (num-regs aignet)))
;;                          :expand ((:free (suff aignet)
;;                                    (id-eval (fanin-count suff) invals regvals aignet))
;;                                   (:free (suff aignet)
;;                                    (id-eval (+ 1 (nfix n) suff) invals regvals aignet))
;;                                   (:free (Aignet2)
;;                                    (aignet-copy-nxsts-from-fanins-iter (+ 1 (nfix n)) aignet copy aignet2))
;;                                   (:free (x)
;;                                    (lit-eval (fanin-if-co x) invals regvals aignet))))))))
  


;;   (defret balance-finish-copy-comb-equivalent
;;     (implies (and (marked-lit-copies-equiv-all-evals mark copy aignet aignet2)
;;                   (aignet-copies-in-bounds copy aignet2)
;;                   (aignet-nxst-fanins-marked mark aignet)
;;                   (aignet-output-fanins-marked mark aignet)
;;                   (equal (stype-count :po aignet2) 0)
;;                   (equal (stype-count :nxst aignet2) 0)
;;                   (equal (stype-count :reg aignet2)
;;                          (stype-count :reg aignet)))
;;              (comb-equiv new-aignet2 aignet))
;;     :hints(("Goal" :in-theory (e/d (comb-equiv) (balance-finish-copy))))))
                            

(define balance-core (aignet
                      aignet2
                      (config balance-config-p))
  :returns (new-aignet2)
  :prepwork ((local (defthm natp-floor
                      (implies (and (natp x) (posp y)) (natp (floor x y)))
                      :hints(("Goal" :in-theory (enable floor)))
                      :rule-classes :type-prescription)))
  (b* (((local-stobjs mark copy refcounts levels strash)
        (mv mark copy refcounts levels aignet2 strash))
       ((mv copy aignet2) (init-copy-comb aignet copy aignet2))
       (refcounts (resize-u32 (num-fanins aignet) refcounts))
       (refcounts (aignet-count-refs refcounts aignet))
       (mark (resize-bits (num-fanins aignet) mark))
       (levels (resize-u32 (+ (num-fanins aignet2) (floor (num-gates aignet) 3)) levels))
       ((mv mark copy levels aignet2 strash)
        (aignet-balance-outs 0 config aignet mark copy refcounts levels aignet2 strash))
       ((mv mark copy levels aignet2 strash)
        (aignet-balance-nxsts 0 config aignet mark copy refcounts levels aignet2 strash))
       (aignet2 (finish-copy-comb aignet copy aignet2)))
    (mv mark copy refcounts levels aignet2 strash))
  ///
  (defret num-ins-of-balance-core
    (equal (stype-count :pi new-aignet2)
           (stype-count :pi aignet)))

  (defret num-regs-of-balance-core
    (equal (stype-count :reg new-aignet2)
           (stype-count :reg aignet)))

  (defret num-outs-of-balance-core
    (equal (stype-count :po new-aignet2)
           (stype-count :po aignet)))

  (defret balance-core-comb-equivalent
    (comb-equiv new-aignet2 aignet))

  (defthm normalize-input-of-balance-core
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal (balance-core aignet aignet2 config)
                    (balance-core aignet nil config)))))

(Define find-max-level ((n natp)
                        (max-idx natp)
                        (curr-max natp)
                        (levels))
  :guard (and (<= max-idx (u32-length levels))
              (<= n max-idx))
  :returns (max natp :rule-classes :type-prescription)
  :measure (nfix (- (nfix max-idx) (nfix n)))
  (b* (((when (mbe :logic (zp (- (nfix max-idx) (nfix n)))
                   :exec (eql max-idx n)))
        (lnfix curr-max))
       (next-max (max (lnfix curr-max) (get-u32 n levels))))
    (find-max-level (1+ (lnfix n)) max-idx next-max levels)))

(define print-aignet-levels ((aignet))
  (b* (((local-stobjs levels)
        (mv nothing levels))
       (levels (aignet-record-levels aignet levels))
       (max (find-max-level 0 (num-fanins aignet) 0 levels)))
    (mv (cw "Max level: ~x0~%" max) levels)))
       


(define balance ((aignet  "Input aignet")
                 (aignet2 "New aignet -- will be emptied")
                 (config balance-config-p))
  :guard-debug t
  :returns new-aignet2
  :parents (aignet-comb-transforms)
  :short "Apply DAG-aware AND tree balancing to the network."
  :long "<p>Note: This implementation is heavily based on the one in
ABC, developed and maintained at Berkeley by Alan Mishchenko.</p>

<p>Settings for the transform can be tweaked using the @('config') input, which
is a @(see balance-config) object.</p>"
  (b* (((acl2::local-stobjs aignet-tmp)
        (mv aignet2 aignet-tmp))
       (- (cw "Balance input: ") (print-aignet-levels aignet))
       (aignet-tmp (balance-core aignet aignet-tmp config))
       (aignet2 (aignet-prune-comb aignet-tmp aignet2 (balance-config->gatesimp config)))
       (- (cw "Balance output: ") (print-aignet-levels aignet)))
    (mv aignet2 aignet-tmp))
  ///
  (defret num-ins-of-balance
    (equal (stype-count :pi new-aignet2)
           (stype-count :pi aignet)))

  (defret num-regs-of-balance
    (equal (stype-count :reg new-aignet2)
           (stype-count :reg aignet)))

  (defret num-outs-of-balance
    (equal (stype-count :po new-aignet2)
           (stype-count :po aignet)))

  (defret balance-comb-equivalent
    (comb-equiv new-aignet2 aignet))

  (defthm normalize-input-of-balance
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal (balance aignet aignet2 config)
                    (balance aignet nil config)))))

(define balance! ((aignet  "Input aignet -- will be replaced with transformation result")
                  (config balance-config-p))
  :guard-debug t
  :returns new-aignet
  :parents (balance)
  :short "Like @(see observability-fix), but overwrites the original network instead of returning a new one."
  (b* (((acl2::local-stobjs aignet-tmp)
        (mv aignet aignet-tmp))
       (- (cw "Balance input: ") (print-aignet-levels aignet))
       (aignet-tmp (balance-core aignet aignet-tmp config))
       (aignet (aignet-prune-comb aignet-tmp aignet (balance-config->gatesimp config)))
       (- (cw "Balance output: ") (print-aignet-levels aignet)))
    (mv aignet aignet-tmp))
  ///
  (defret num-ins-of-balance!
    (equal (stype-count :pi new-aignet)
           (stype-count :pi aignet)))

  (defret num-regs-of-balance!
    (equal (stype-count :reg new-aignet)
           (stype-count :reg aignet)))

  (defret num-outs-of-balance!
    (equal (stype-count :po new-aignet)
           (stype-count :po aignet)))

  (defret balance!-comb-equivalent
    (comb-equiv new-aignet aignet)))




