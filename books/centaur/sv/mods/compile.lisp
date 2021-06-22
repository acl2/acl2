; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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

(in-package "SV")
(include-book "moddb")
(include-book "alias-norm")
(include-book "../svex/compose")
(include-book "centaur/misc/hons-extra" :dir :system)
(include-book "centaur/vl/util/cwtime" :dir :system)
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/osets/under-set-equiv" :dir :system))
(local (in-theory (disable nfix natp)))

(defxdoc svex-compilation
  :parents (sv)
  :short "Turning a hierarchical SVEX design into a finite state machine."
  :long " <p>The function @(see svex-design-compile) extracts a finite state
machine representation from a hierarchical SVEX design.  See also @(see
defsvtv), @(see defsvtv$), and @(see defcycle), which all perform this process
and subsequently perform some amount of unrolling of the resulting finite state
machine in order to produce either a pipeline representation (@(see defsvtv)
and @(see defsvtv$)) or a cycle FSM (@(see defcycle)).</p>

<p>We follow these steps to turn an svex module hierarchy into a finite-state
machine representation:</p>
<ul>
<li>Enumerate wires.  We walk over each module and count the wires contained in
it and all its submodules.  We store this information in a module database (see
@(see moddb)), which allows us to both look up a hierarchical names and get
their wire indices or vice versa.</li>
<li>Translate the module hierarchy's assignments and aliases by replacing wire
names with indices (see @(see modalist-named->indexed)).</li>
<li>Flatten the assignments, aliases, and stateholding elements
 (see @(see svex-mod->flatten)).</li>
<li>Use the flattened aliases to compute a canonical alias table, mapping every
wire to a canonical representation (see @(see canonicalize-alias-pairs)).</li>
<li>Canonicalize the wires in the flattened assignment list and
stateholding elements using the alias table (see @(see assigns-subst)).</li>
<li>Convert the lists of assignments and stateholding elements, which may
have arbitrary LHS expressions as the left-hand sides, into a list of
assignments to variables.  This involves segmenting each assignment into
separate assignments to its individual LHS components (see @(see assigns->netassigns)),
and then for wires that have multiple assignments, resolving these together to
obtain a single RHS (see @(see netassigns->resolves)).</li>
<li>Compose assignments together to obtain the full 0-delay formulas for each
canonical wire and full update functions for each state bit; that is, formulas
in terms of primary inputs and previous states (see @(see
svex-assigns-compose)).</li>
</ul>
")

(defxdoc compile.lisp :parents (svex-compilation))
(local (xdoc::set-default-parents compile.lisp))

(local (in-theory (disable nth update-nth
                           sv::moddb-mod-inst-wireoffset-recursive
                           nfix natp)))
(local (std::add-default-post-define-hook :fix))

(defthm modname-get-index-of-top-mod-bound
  (and (moddb-modname-get-index topmod (module->db topmod modalist moddb))
       (integerp (moddb-modname-get-index topmod (module->db topmod modalist moddb)))
       (< (moddb-modname-get-index topmod (module->db topmod modalist moddb))
          (nfix (nth *moddb->nmods* (module->db topmod modalist moddb))))
       (< (nfix (moddb-modname-get-index topmod (module->db topmod modalist moddb)))
          (nfix (nth *moddb->nmods* (module->db topmod modalist moddb)))))
  :hints #!sv
  (("goal" :use ((:instance new-modname-of-module->db
                  (modname topmod)))
    :in-theory (disable new-modname-of-module->db))))

(defthm svex-alist-p-of-take
  (implies (and (<= (nfix n) (len x))
                (svex-alist-p x))
           (svex-alist-p (take n x)))
  :hints(("Goal" :in-theory (enable svex-alist-p))))

(defthm svex-alist-p-of-nthcdr
  (implies (svex-alist-p x)
           (svex-alist-p (nthcdr n x)))
  :hints(("Goal" :in-theory (enable svex-alist-p))))


;; ;; this thm doesn't belong here; eventually we should prove that svex-assigns-compose
;; ;; preserves boundedness but that involves tracking variables through rewriting so seems harder
;; (defthm-svex-compose-flag
;;   (defthm svex-compose-boundedp
;;     (implies (and (svex-boundedp x bound)
;;                   (svex-alist-boundedp a bound))
;;              (svex-boundedp (svex-compose x a) bound))
;;     :hints ('(:expand ((Svex-compose x a)
;;                        (svex-boundedp x bound)
;;                        (:free (f a) (svex-boundedp (svex-call f a) bound)))
;;               :in-theory (enable svex-lookup)))
;;     :flag svex-compose)
;;   (defthm svexlist-compose-boundedp
;;     (implies (and (svexlist-boundedp x bound)
;;                   (svex-alist-boundedp a bound))
;;              (svexlist-boundedp (svexlist-compose x a) bound))
;;     :hints ('(:expand ((svexlist-compose x a)
;;                        (svexlist-boundedp nil bound)
;;                        (:free (f a) (svexlist-boundedp (cons f a) bound)))))
;;     :flag svexlist-compose))


(define delay-svar->delays ((x svar-p))
  :returns (delays svar-map-p)
  :measure (svar->delay x)
  (b* (((svar x) (svar-fix x))
       ((when (eql 0 x.delay)) nil)
       (next-x (change-svar x :delay (1- x.delay)))
       (pair (cons x next-x)))
    (cons pair (delay-svar->delays next-x)))
  ///
  (more-returns
   (delays :name vars-of-delay-svar->delays
           (implies (svar-addr-p x)
                    (svarlist-addr-p (svar-map-vars delays)))
           :hints(("Goal" :in-theory (enable svar-map-vars
                                             svar-addr-p))))))


(define delay-svarlist->delays ((x svarlist-p))
  :returns (delays svar-map-p)
  (b* (((when (atom x)) nil)
       (rest (delay-svarlist->delays (cdr x)))
       (delays1 (delay-svar->delays (car x))))
    (append-without-guard delays1 rest))
  ///

  (more-returns
   (delays :name vars-of-delay-svarlist->delays
           (implies (svarlist-addr-p x)
                    (svarlist-addr-p (svar-map-vars delays))))))

(define svarlist-collect-delays ((x svarlist-p))
  :returns (delayvars svarlist-p)
  (if (atom x)
      nil
    (if (zp (svar->delay (car x)))
        (svarlist-collect-delays (cdr x))
      (cons (svar-fix (car x)) (svarlist-collect-delays (cdr x)))))
  ///
  (more-returns
   (delayvars :name vars-of-svarlist-collect-delays
              (implies (not (double-rewrite (member v (svarlist-fix x))))
                       (not (member v delayvars)))))

  (local (defthm member-of-svarlist-collect-delays
           (iff (member v (svarlist-collect-delays x))
                (and (svar-p v)
                     (posp (svar->delay v))
                     (member v (svarlist-fix x))))))


  ;; (encapsulate nil
  ;;   (local
  ;;    (progn
  ;;      (defun svarlist-member-witness (v x)
  ;;        (if (atom x)
  ;;            nil
  ;;          (if (equal v (svar-fix (car x)))
  ;;              (car x)
  ;;            (svarlist-member-witness v (cdr x)))))

  ;;      (defthm member-svarlist-fix-by-witness-2
  ;;        (implies (and (set-equiv x x2)
  ;;                      (member w x2)
  ;;                      (equal v (svar-fix w)))
  ;;                 (member v (svarlist-fix x))))

  ;;      (defthm member-svarlist-fix-by-witness
  ;;        (implies (and (member w x)
  ;;                      (equal v (svar-fix w)))
  ;;                 (member v (svarlist-fix x))))

  ;;      (defthm not-member-of-svarlist-fix-by-witness
  ;;        (implies (acl2::rewriting-negative-literal `(member-equal ,v (svarlist-fix$inline ,x)))
  ;;                 (iff (member v (svarlist-fix x))
  ;;                      (and (equal v (svar-fix (svarlist-member-witness v x)))
  ;;                           (member (svarlist-member-witness v x) x))))
  ;;        :hints(("Goal" :in-theory (enable svarlist-fix)
  ;;                :induct (svarlist-fix x))))))

  ;;   (defcong set-equiv set-equiv (svarlist-fix x) 1
  ;;     :hints (("goal" :in-theory (enable acl2::set-unequal-witness-rw)))))

  ;; (defcong set-equiv set-equiv (svarlist-collect-delays x) 1
  ;;     :hints (("goal" :in-theory (enable acl2::set-unequal-witness-rw))))
  )


;; NOTE: Consider replacing all this with a routine that computes a replacement
;; table for the indexed names by traversing the moddb.  This could be modeled
;; after functions such as svex-mod->flat-aliases.  Benefits: Worst-case linear
;; in the size of the design * number of levels of hierarchy; but possible
;; downsides: generates names for non-canonical wires.


(define svar-indexed->named ((var svar-p) (scope modscope-p) (moddb moddb-ok))
  :guard (and (modscope-okp scope moddb)
              (svar-boundedp var (modscope-local-bound scope moddb)))
  :guard-hints (("goal" :in-theory (enable modscope-local-bound
                                           svar-boundedp)))
  :returns (newvar (and (svar-p newvar)
                        (svar-addr-p newvar)))
  (b* ((idx (svar-index var))
       (name (moddb-wireidx->path idx (modscope->modidx scope) moddb))
       (addr (make-address :path name)))
    (address->svar addr)))

(define svarlist-indexed->named ((vars svarlist-p) (scope modscope-p) (moddb moddb-ok))
  :guard (and (modscope-okp scope moddb)
              (svarlist-boundedp vars (modscope-local-bound scope moddb)))
  :guard-hints (("goal" :in-theory (enable svarlist-p))
                (and stable-under-simplificationp
                     '(:in-theory (enable svar-p))))
  :returns (newvars (and (svarlist-p newvars)
                         (svarlist-addr-p newvars)))
  :prepwork ((local (in-theory (enable svarlist-fix))))
  (if (atom vars)
      nil
    (cons (svar-indexed->named (car vars) scope moddb)
          (svarlist-indexed->named (cdr vars) scope moddb)))
  ///
  (defthm len-of-svarlist-indexed->named
    (equal (len (svarlist-indexed->named vars scope moddb))
           (len vars))))

(define maybe-svar-p (x)
  (or (not x)
      (svar-p x))
  ///
  (defthm maybe-svar-p-when-svar-p
    (implies (svar-p x)
             (maybe-svar-p x)))

  (define maybe-svar-fix ((x maybe-svar-p))
    :returns (xx maybe-svar-p)
    :inline t
    :hooks nil
    (mbe :logic (and x (svar-fix x))
         :exec x)
    ///
    (defthm maybe-svar-fix-when-maybe-svar-p
      (implies (maybe-svar-p x)
               (equal (maybe-svar-fix x) x)))

    (deffixtype maybe-svar :pred maybe-svar-p :fix maybe-svar-fix
      :equiv maybe-svar-equiv :define t :forward t)

    (defrefinement maybe-svar-equiv svar-equiv)

    (defthm svar-p-of-maybe-svar-fix
      (implies (maybe-svar-fix x)
               (svar-p (maybe-svar-fix x))))))

(defprod indname-result
  ((varname svar-p)
   (decl wire-p))
  :layout :fulltree)

(fty::defoption maybe-indname-result indname-result)

(acl2::def-1d-arr indnamememo
  :slotname indname
  :pred maybe-indname-result-p
  :fix maybe-indname-result-fix$inline
  :type-decl (satisfies maybe-indname-result-p)
  :pkg-sym sv::svex
  :default-val nil)

(define svar-indexed->named-memo ((x svar-p) (scope modscope-p) (moddb moddb-ok) indnamememo)
  :guard (and (modscope-okp scope moddb)
              (svar-boundedp x (modscope-local-bound scope moddb)))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable svar-boundedp modscope-local-bound))))
  :returns (mv (xx (and (svar-p xx)
                        (svar-addr-p xx)))
               (indnamememo1 (equal (len indnamememo1)
                                    (len indnamememo))))
  (b* ((idx (lnfix (svar-index x)))
       (in-bounds (< idx (indnames-length indnamememo)))
       (look (and in-bounds
                  (get-indname idx indnamememo)))
       ((when (and look (svar-addr-p (indname-result->varname look))))
        (mv (indname-result->varname look) indnamememo))
       ((mv name wire) (moddb-wireidx->path/decl idx (modscope->modidx scope) moddb))
       (res (address->svar (make-address :path name)))
       (indnamememo (if in-bounds
                        (set-indname idx (make-indname-result :varname res :decl wire) indnamememo)
                      indnamememo)))
    (mv res indnamememo)))


(local (in-theory (disable lhs-vars-when-consp)))

(define lhs-indexed->named ((x lhs-p) (scope modscope-p) (moddb moddb-ok) indnamememo)
  :guard (and (modscope-okp scope moddb)
              (svarlist-boundedp (lhs-vars x) (modscope-local-bound scope moddb)))
  :verify-guards nil
  :returns (mv (xx (and (lhs-p xx)
                        (svarlist-addr-p (lhs-vars xx)))
                   :hints(("Goal" :in-theory (enable lhs-vars-of-decomp-redef
                                                     lhatom-vars))))
               (indnamememo1 (equal (len indnamememo1)
                                    (len indnamememo))))
  :measure (len x)
  (b* (((mv first rest) (lhs-decomp x))
       ((unless first) (mv nil indnamememo))
       ((lhrange first) first)
       ((mv repl indnamememo)
        (lhatom-case first.atom
          :z (mv first indnamememo)
          :var (b* (((mv name indnamememo)
                     (svar-indexed->named-memo first.atom.name scope moddb indnamememo)))
                 (mv (lhrange first.w (lhatom-var name first.atom.rsh)) indnamememo))))
       ((mv rest indnamememo)
        (lhs-indexed->named rest scope moddb indnamememo)))
    (mv (lhs-cons repl rest) indnamememo))
  ///
  (verify-guards lhs-indexed->named
    :hints(("Goal" :in-theory (enable lhatom-vars)))))

(local (include-book "arithmetic/top-with-meta" :dir :system))


(define aliases-boundedp-aux ((n natp) (aliases) (bound natp))
  :measure (nfix (- (aliass-length aliases) (nfix n)))
  :guard (<= (lnfix n) (aliass-length aliases))
  (b* (((when (mbe :logic (zp (- (aliass-length aliases) (nfix n)))
                   :exec (eql (aliass-length aliases) n)))
        t))
    (and (svarlist-boundedp (lhs-vars (get-alias n aliases)) bound)
         (aliases-boundedp-aux (1+ (lnfix n)) aliases bound)))
  ///
  (defthm aliases-boundedp-aux-of-update-less
    (implies (< (nfix m) (nfix n))
             (equal (aliases-boundedp-aux n (update-nth m val aliases) bound)
                    (aliases-boundedp-aux n aliases bound))))

  (defthm aliases-boundedp-aux-when-normordered
    (implies (and (aliases-normorderedp aliases)
                  (<= (len aliases) (nfix bound)))
             (aliases-boundedp-aux n aliases bound))
    :hints (("goal" :induct (aliases-boundedp-aux n aliases bound))
            (and stable-under-simplificationp
                 '(:use ((:instance lhs-vars-normorderedp-implies-svarlist-boundedp
                          (x (nth n aliases)) (bound (nfix n)) (offset 0)))
                   :in-theory (e/d (svarlist-boundedp-of-greater)
                                   (lhs-vars-normorderedp-implies-svarlist-boundedp))
                   :do-not-induct t)))))





(define aliases-indexed->named-aux ((n natp) (aliases) (scope modscope-p) (moddb moddb-ok) indnamememo)
  :guard (and (<= (lnfix n) (aliass-length aliases))
              (modscope-okp scope moddb)
              (aliases-boundedp-aux n aliases (modscope-local-bound scope moddb)))
  :guard-hints (("goal" :expand ((aliases-boundedp-aux n aliases (modscope-local-bound scope moddb)))))
  :returns (mv (aliases1 (equal (len aliases1) (len aliases)))
               (indnamememo1 (equal (len indnamememo1) (len indnamememo))))
  :measure (nfix (- (aliass-length aliases) (nfix n)))
  :guard-debug t
  (b* ((aliases (aliases-fix aliases))
       ((when (mbe :logic (zp (- (aliass-length aliases) (nfix n)))
                   :exec (eql (aliass-length aliases) n)))
        (mv aliases indnamememo))
       (lhs (get-alias n aliases))
       ((mv lhs1 indnamememo) (lhs-indexed->named lhs scope moddb indnamememo))
       (aliases (set-alias n lhs1 aliases)))
    (aliases-indexed->named-aux (1+ (lnfix n)) aliases scope moddb indnamememo))
  ///
  (local
   (defthm lemma
     (implies (<= (len aliases) (nfix m))
              (not (consp (nth m aliases))))
     :hints (("goal" :in-theory (enable nth len nfix)))))

  (defthm aliases-indexed->named-preserves-lesser-indices
    (implies (< (nfix m) (nfix n))
             (equal (nth m (mv-nth 0 (aliases-indexed->named-aux
                                      n aliases scope moddb indnamememo)))
                    (lhs-fix (nth m aliases)))))

  (defthm vars-of-aliases-indexed->named-aux
    (implies (and (<= (nfix n) (nfix m))
                  (< (nfix m) (len aliases)))
             (svarlist-addr-p
              (lhs-vars (nth m (mv-nth 0 (aliases-indexed->named-aux
                                          n aliases scope moddb indnamememo))))))))


(fty::defmap var-decl-map :key-type svar :val-type wire :true-listp t)

(define indnamememo-to-var-decl-map ((n natp) indnamememo (acc var-decl-map-p))
  :returns (map var-decl-map-p)
  :guard (<= n (indnames-length indnamememo))
  :measure (nfix (- (indnames-length indnamememo) (nfix n)))
  (b* (((when (mbe :logic (zp (- (indnames-length indnamememo) (nfix n)))
                   :exec (eql n (indnames-length indnamememo))))
        (var-decl-map-fix acc))
       (entry (get-indname n indnamememo))
       (acc (if entry
                (b* (((indname-result entry)))
                  (hons-acons entry.varname entry.decl (var-decl-map-fix acc)))
              (var-decl-map-fix acc))))
    (indnamememo-to-var-decl-map (1+ (lnfix n)) indnamememo acc)))


(define aliases-indexed->named (aliases (scope modscope-p) (moddb moddb-ok))
  :returns (mv (new-aliases (equal (len new-aliases) (len aliases)))
               (varmap var-decl-map-p))
  :guard (and (modscope-okp scope moddb)
              (<= (aliass-length aliases) (modscope-local-bound scope moddb))
              (aliases-normorderedp aliases))
  :verbosep t
  (b* (((acl2::local-stobjs indnamememo)
        (mv aliases varmap indnamememo))
       (indnamememo (resize-indnames (aliass-length aliases) indnamememo))
       ((mv aliases indnamememo)
        (aliases-indexed->named-aux 0 aliases scope moddb indnamememo))
       (varmap (indnamememo-to-var-decl-map 0 indnamememo nil)))
    (mv aliases varmap indnamememo))
  ///
  (defret vars-of-aliases-indexed->named
    (implies (< (nfix m) (len aliases))
             (svarlist-addr-p (lhs-vars (nth m new-aliases)))))


  (local (defun ind (n)
           (if (zp n)
               n
             (ind (1- n)))))
  (local
   (defret aliases-vars-aux-of-aliases-indexed->named
     (implies (<= (nfix n) (len aliases))
              (svarlist-addr-p (aliases-vars-aux n new-aliases)))
     :hints(("Goal" :in-theory (e/d (aliases-vars-aux)
                                    (aliases-indexed->named)) :induct (ind n)))))

  (defret aliases-vars-of-aliases-indexed->named
    (svarlist-addr-p (aliases-vars new-aliases))
    :hints(("Goal" :in-theory (e/d (aliases-vars)
                                   (aliases-indexed->named))))))



;; when keeping aliases indexed rather than named
(define svar-register-indnamememo ((x svar-p) (scope modscope-p) (moddb moddb-ok) indnamememo)
  :guard (and (modscope-okp scope moddb)
              (svar-boundedp x (modscope-local-bound scope moddb)))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable svar-boundedp modscope-local-bound))))
  :returns (indnamememo1 (equal (len indnamememo1)
                                (len indnamememo)))
  (b* ((idx (lnfix (svar-index x)))
       (in-bounds (< idx (indnames-length indnamememo)))
       (look (and in-bounds
                  (get-indname idx indnamememo)))
       ((when look)
        indnamememo)
       ((mv ?name wire) (moddb-wireidx->path/decl idx (modscope->modidx scope) moddb)))
    (if in-bounds
        (set-indname idx (make-indname-result :varname x :decl wire) indnamememo)
      indnamememo)))

(define lhs-register-indnamememo ((x lhs-p) (scope modscope-p) (moddb moddb-ok) indnamememo)
  :guard (and (modscope-okp scope moddb)
              (svarlist-boundedp (lhs-vars x) (modscope-local-bound scope moddb)))
  :verify-guards nil
  :returns (indnamememo1 (equal (len indnamememo1)
                                (len indnamememo)))
  :measure (len x)
  (b* (((mv first rest) (lhs-decomp x))
       ((unless first) indnamememo)
       ((lhrange first) first)
       (indnamememo
        (lhatom-case first.atom
          :z indnamememo
          :var (svar-register-indnamememo first.atom.name scope moddb indnamememo))))
    (lhs-register-indnamememo rest scope moddb indnamememo))
  ///
  (verify-guards lhs-register-indnamememo
    :hints(("Goal" :in-theory (enable lhatom-vars)))))



(define aliases-to-var-decl-map-aux ((n natp) (aliases) (scope modscope-p) (moddb moddb-ok) indnamememo)
  :guard (and (<= (lnfix n) (aliass-length aliases))
              (modscope-okp scope moddb)
              (aliases-boundedp-aux n aliases (modscope-local-bound scope moddb)))
  :guard-hints (("goal" :expand ((aliases-boundedp-aux n aliases (modscope-local-bound scope moddb)))))
  :returns (indnamememo1 (equal (len indnamememo1) (len indnamememo)))
  :measure (nfix (- (aliass-length aliases) (nfix n)))
  :guard-debug t
  (b* (((when (mbe :logic (zp (- (aliass-length aliases) (nfix n)))
                   :exec (eql (aliass-length aliases) n)))
        indnamememo)
       (lhs (get-alias n aliases))
       (indnamememo (lhs-register-indnamememo lhs scope moddb indnamememo)))
    (aliases-to-var-decl-map-aux (1+ (lnfix n)) aliases scope moddb indnamememo)))


(define aliases-to-var-decl-map (aliases (scope modscope-p) (moddb moddb-ok))
  :returns (varmap var-decl-map-p)
  :guard (and (modscope-okp scope moddb)
              (<= (aliass-length aliases) (modscope-local-bound scope moddb))
              (aliases-normorderedp aliases))
  :verbosep t
  (b* (((acl2::local-stobjs indnamememo)
        (mv varmap indnamememo))
       (indnamememo (resize-indnames (aliass-length aliases) indnamememo))
       (indnamememo
        (aliases-to-var-decl-map-aux 0 aliases scope moddb indnamememo))
       (varmap (indnamememo-to-var-decl-map 0 indnamememo nil)))
    (mv varmap indnamememo)))


;; (defines svex-indexed->named
;;   :Verify-guards nil
;;   ;; Don't want to memoize this since it will slow down moddb operations
;;   (define svex-indexed->named ((x svex-p) (scope modscope-p) (moddb moddb-ok))
;;     :guard (< (lnfix modidx) (lnfix (moddb->nmods moddb)))
;;     :measure (svex-count x)
;;     :returns (xx svex-p)
;;     (svex-case x
;;       :quote (svex-fix x)
;;       :var (svex-var (svar-indexed->named x.name modidx moddb))
;;       :call (svex-call x.fn (svexlist-indexed->named x.args modidx moddb))))
;;   (define svexlist-indexed->named ((x svexlist-p) (scope modscope-p) (moddb moddb-ok))
;;     :guard (< (lnfix modidx) (lnfix (moddb->nmods moddb)))
;;     :measure (svexlist-count x)
;;     :returns (xx svexlist-p)
;;     (if (atom x)
;;         nil
;;       (cons (svex-indexed->named (car x) modidx moddb)
;;             (svexlist-indexed->named (cdr x) modidx moddb))))
;;   ///
;;   (verify-guards svex-indexed->named))


(define svex-override-vars ((x svex-override-p))
  :returns (vars svarlist-p)
  (b* (((svex-override x)))
    (append (svex-vars x.test)
            (svex-vars x.val)))
  ///
  (defthm vars-of-svex-override->test
    (implies (not (member v (svex-override-vars x)))
             (not (member v (svex-vars (svex-override->test x))))))
  (defthm vars-of-svex-override->val
    (implies (not (member v (svex-override-vars x)))
             (not (member v (svex-vars (svex-override->val x))))))

  (defthm vars-of-svex-override
    (implies (and (not (member v (svex-vars test)))
                  (not (member v (svex-vars val))))
             (not (member v (svex-override-vars (svex-override wire test val)))))))

(define svex-overridelist-vars ((x svex-overridelist-p))
  :returns (vars svarlist-p)
  (if (atom x)
      nil
    (append (svex-override-vars (car x))
            (svex-overridelist-vars (cdr x)))))


(define svex-overridelist-keys ((x svex-overridelist-p))
  :returns (vars svarlist-p)
  (if (atom x)
      nil
    (append (svex-vars (svex-override->wire (car x)))
            (svex-overridelist-keys (cdr x)))))



(define svex-override-lhrange ((x lhrange-p)
                               (override-test svex-p)
                               (offset natp)
                               (override-val svex-p)
                               (assigns svex-alist-p))
  :returns (assigns1 svex-alist-p)
  (b* (((lhrange x) x)
       ((when (eq (lhatom-kind x.atom) :z))
        (svex-alist-fix assigns))
       ((lhatom-var x.atom) x.atom)
       (expr (or (svex-fastlookup x.atom.name assigns)
                 (svex-quote (4vec-z))))
       ;; Set the new assignment: outside of bits rsh:rsh+width, same as before;
       ;; in bits rsh:rsh+width, it's override-test ? (rsh offset override-val) : (rsh rsh expr),
       (last (svex-rsh  (+ x.atom.rsh x.w) expr))
       (mid  (svex-call '?* (list (svex-zerox 1 override-test)
                                 (svex-rsh offset override-val)
                                 (svex-rsh x.atom.rsh expr))))
       (newexpr (svex-concat x.atom.rsh
                             expr
                             (svex-concat x.w mid last))))
    (hons-acons x.atom.name newexpr (svex-alist-fix assigns)))
  ///
  (more-returns
   (assigns1 :name vars-of-svex-override-lhrange
             (implies (and (not (member v (svex-alist-vars assigns)))
                           (not (member v (svex-vars override-test)))
                           (not (member v (svex-vars override-val))))
                      (not (member v (svex-alist-vars assigns1))))
             :hints(("Goal" :in-theory (enable svex-alist-vars)))))
  (more-returns
   (assigns1 :name lookup-of-svex-override-lhrange
             (implies (and (not (member v (lhatom-vars (lhrange->atom x))))
                           (not (svex-lookup v assigns))
                           (svar-p v))
                      (not (svex-lookup v assigns1)))
             :hints(("Goal" :in-theory (enable svex-alist-vars svex-lookup lhatom-vars))))))

(define svex-override-lhs ((x lhs-p)
                           (override-test svex-p)
                           (offset natp)
                           (override-val svex-p)
                           (assigns svex-alist-p))
  :measure (len x)
  :returns (assigns1 svex-alist-p)
  :verify-guards nil
  (b* (((mv first rest) (lhs-decomp x))
       ((unless first) (svex-alist-fix assigns))
       ((lhrange first) first)
       (assigns (svex-override-lhs rest override-test (+ (lnfix offset) first.w)
                                   override-val assigns)))
    (svex-override-lhrange first override-test offset override-val assigns))
  ///
  (verify-guards svex-override-lhs)

  (more-returns
   (assigns1 :name vars-of-svex-override-lhs
             (implies (and (not (member v (svex-alist-vars assigns)))
                           (not (member v (svex-vars override-test)))
                           (not (member v (svex-vars override-val))))
                      (not (member v (svex-alist-vars assigns1))))))

  (more-returns
   (assigns1 :name lookup-of-svex-override-lhs
             (implies (and (not (member v (lhs-vars x)))
                           (not (svex-lookup v assigns))
                           (svar-p v))
                      (not (svex-lookup v assigns1)))
             :hints(("Goal" :in-theory (enable lhs-vars-of-decomp-redef))))))

(define svex-apply-overrides ((x lhs-overridelist-p)
                              (assigns svex-alist-p))
  :returns (assigns1 svex-alist-p)
  (b* (((when (atom x))
        (svex-alist-fix assigns))
       (assigns (svex-apply-overrides (cdr x) assigns))
       ((lhs-override xf) (car x)))
    (svex-override-lhs xf.lhs xf.test 0 xf.val assigns))
  ///

  (more-returns
   (assigns1 :name vars-of-svex-apply-overrides
             (implies (and (not (member v (lhs-overridelist-vars x)))
                           (not (member v (svex-alist-vars assigns))))
                      (not (member v (svex-alist-vars assigns1))))
             :hints(("Goal" :in-theory (enable lhs-overridelist-vars
                                               lhs-override-vars)))))

  (more-returns
   (assigns1 :name lookup-of-svex-apply-overrides
             (implies (and (not (member v (lhs-overridelist-keys x)))
                           (not (svex-lookup v assigns))
                           (svar-p v))
                      (not (svex-lookup v assigns1)))
             :hints(("Goal" :in-theory (enable lhs-overridelist-keys))))))


(define assigns-to-overrides-nrev ((x assigns-p)
                                   nrev)
  :measure (len (assigns-fix x))
  (b* ((x (assigns-fix x))
       ((when (atom x)) (acl2::nrev-fix nrev))
       ((cons lhs (driver rhs)) (car x))
       (ans (make-lhs-override :lhs lhs :test 1 :val rhs.value))
       (nrev (acl2::nrev-push ans nrev)))
    (assigns-to-overrides-nrev (cdr x) nrev)))


(define assigns-to-overrides ((x assigns-p))
  :returns (override lhs-overridelist-p)
  :measure (len (assigns-fix x))
  :verify-guards nil
  (mbe :logic (b* ((x (assigns-fix x))
                   ((when (atom x)) nil)
                   ((cons lhs (driver rhs)) (car x))
                   (ans (make-lhs-override :lhs lhs :test 1 :val rhs.value)))
                (cons ans (assigns-to-overrides (cdr x))))
       :exec (if (atom x)
                 nil
               (acl2::with-local-nrev
                 (assigns-to-overrides-nrev x acl2::nrev))))
  ///
  (local (defthm assigns-to-overrides-nrev-elim
           (equal (assigns-to-overrides-nrev x nrev)
                  (append nrev (assigns-to-overrides x)))
           :hints(("Goal" :in-theory (enable assigns-to-overrides-nrev)))))

  (verify-guards assigns-to-overrides)

  (defret vars-of-assigns-to-overrides
    (implies (not (member v (assigns-vars x)))
             (and (not (member v (lhs-overridelist-vars override)))
                  (not (member v (lhs-overridelist-keys override)))))
    :hints(("Goal" :in-theory (enable lhs-overridelist-vars
                                      assigns-vars
                                      lhs-overridelist-keys
                                      lhs-override-vars)))))


;; (define svex-overrides-boundedp ((x svex-overridelist-p) (bound natp))
;;   (if (atom x)
;;       t
;;     (and (svex-boundedp (svex-override->wire (car x)) bound)
;;          (svex-overrides-boundedp (cdr x) bound))))

;; (define svex->normed-lhs ((x svex-p)
;;                           (aliases))
;;   :guard (and (svarlist-boundedp (svex-vars x) (aliass-length aliases))
;;               (lhssvex-unbounded-p x))
;;   :verify-guards nil
;;   :returns (lhs lhs-p)
;;   :measure (svex-count x)
;;   (svex-case x
;;     :var (get-alias (svar-index x.name) aliases)
;;     :quote nil
;;     :call
;;     (case x.fn
;;       (concat (b* (((list w lo hi) x.args)
;;                    (width (2vec->val (svex-quote->val w)))
;;                    (lo-lhs (svex->normed-lhs lo aliases))
;;                    (hi-lhs (svex->normed-lhs hi aliases)))
;;                 (lhs-concat (lnfix width) lo-lhs hi-lhs)))
;;       (rsh (b* (((list sh xx) x.args)
;;                 (shamt (2vec->val (svex-quote->val sh)))
;;                 (sub-lhs (svex->normed-lhs xx aliases)))
;;              (lhs-rsh (lnfix shamt) sub-lhs)))))
;;   ///
;;   (local (defthm equal-of-len
;;            (implies (syntaxp (quotep n))
;;                     (equal (equal (len x) n)
;;                            (if (zp n)
;;                                (and (eql n 0)
;;                                     (atom x))
;;                              (and (consp x)
;;                                   (equal (len (cdr x)) (1- n))))))))
;;   (verify-guards svex->normed-lhs
;;     :hints (("goal" :expand ((svex-vars x)
;;                              (lhssvex-unbounded-p x))
;;              :in-theory (enable svar-boundedp svexlist-vars))))

;;   (defthm vars-of-svex->normed-lhs
;;     (implies (not (member v (aliases-vars aliases)))
;;              (not (member v (lhs-vars (svex->normed-lhs x aliases)))))))


;; (define svex-overrides-alias-norm ((x svex-overridelist-p) aliases)
;;   :guard (svarlist-boundedp (svex-overridelist-keys x) (aliass-length aliases))
;;   :prepwork ((local (in-theory (enable svex-overridelist-keys
;;                                        svex-overridelist-vars
;;                                        lhs-overridelist-vars))))
;;   :returns (mv err (newx lhs-overridelist-p))
;;   (b* (((when (atom x)) (mv nil nil))
;;        ((svex-override xf) (car x))
;;        ((unless (lhssvex-unbounded-p xf.wire))
;;         (mv (msg "Error: Expression to be overridden can't be expressed as a concatenation of part-selects: ~x0~%" xf.wire)
;;             nil))
;;        (lhs (svex->normed-lhs xf.wire aliases))
;;        (first (make-lhs-override :lhs lhs
;;                                  :test xf.test
;;                                  :val xf.val))
;;        ((mv err rest) (svex-overrides-alias-norm (cdr x) aliases))
;;        ((when err) (mv err nil)))
;;     (mv nil (cons first rest)))
;;   ///
;;   (more-returns
;;    (newx :name vars-of-svex-overrides-alias-norm
;;          (implies (not (member v (svex-overridelist-vars x)))
;;                   (not (member v (lhs-overridelist-vars newx))))
;;          :hints(("Goal" :in-theory (enable lhs-overridelist-vars
;;                                            svex-overridelist-vars)))))

;;   (more-returns
;;    (newx :name keys-of-svex-overrides-alias-norm
;;          (implies (not (member v (aliases-vars aliases)))
;;                   (not (member v (lhs-overridelist-keys newx))))
;;          :hints(("Goal" :in-theory (enable lhs-overridelist-keys))))))


(define cap-length ((n natp) x)
  (if (< (lnfix n) (len x))
      (take n (list-fix x))
    x))


(define svex-design-flatten ((x design-p)
                             &key
                             ((moddb "overwritten") 'moddb)
                             ((aliases "overwritten") 'aliases))
  :returns (mv err
               (flat-assigns assigns-p)
               (flat-fixups assigns-p)
               (flat-constraints constraintlist-p)
               ;; (flat-delays svar-map-p)
               (new-moddb (and (moddb-basics-ok new-moddb)
                               (moddb-mods-ok new-moddb)))
               (new-aliases (implies (not err)
                                     (aliases-normorderedp new-aliases))))
  :guard (svarlist-addr-p (modalist-vars (design->modalist x)))
  :verify-guards nil
  :prepwork ((local (in-theory (e/d (modscope->top modscope->modidx modscope-okp
                                                   modscope-top-bound modscope-okp)
                                    ((moddb-clear))))))

  (b* ((moddb (moddb-clear moddb))
       (aliases (resize-lhss 0 aliases))
       ((design x) x)
       (modalist x.modalist)
       (topmod x.top)
       ((with-fast modalist))
       ((unless (cwtime (modhier-loopfree-p topmod modalist)
                        :mintime 1))
        (mv
         (msg "Module ~s0 has an instance loop!~%" topmod)
         nil nil nil moddb aliases))

       ;; Create a moddb structure from the module hierarchy.
       ;; This involves enumerating the modules, instances, and wires.
       (moddb (cwtime (module->db topmod modalist moddb)
                      :mintime 1))
       (modidx (moddb-modname-get-index topmod moddb))

       ;; Clear and size the aliases
       ((stobj-get totalwires)
        ((elab-mod (moddb->modsi modidx moddb)))
        (elab-mod->totalwires elab-mod))
       ;; (- (cw "Total wires: ~x0~%" totalwires))
       (aliases (resize-lhss totalwires aliases))

       ;; ((unless modidx)
       ;;  (raise "Module ~s0 not in database after translation~%" topmod)
       ;;  (mv nil nil modalist good bad moddb aliases))

       ;; Now translate the modalist by replacing all variables (nets/HIDs)
       ;; with their moddb indices.
       ((mv err modalist) (cwtime (modalist-named->indexed modalist moddb :quiet t)
                                  :mintime 1))
       ((when err)
        (mv (msg "Error indexing wire names: ~@0~%" err)
            nil nil nil moddb aliases))

       ((with-fast modalist))

       (scope (make-modscope-top :modidx modidx))

       ;; Gather the full flattened lists of aliases and assignments from the module DB.
       ((mv varfails modfails flat-aliases flat-assigns flat-fixups flat-constraints)
        (cwtime (svex-mod->flatten scope modalist moddb)
                :mintime 1))
       ((when modfails)
        (mv (msg "Module names referenced but not found: ~x0~%" (cap-length 20 modfails))
            nil nil nil moddb aliases))
       ((when varfails)
        (mv (msg "Variable names malformed/unresolved: ~x0~%" (cap-length 20 varfails))
            nil nil nil moddb aliases))

       ;; Compute a normal form for each variable by running a
       ;; union/find-like algorithm on the list of alias pairs.  This
       ;; populates aliases, which maps each wire's index to its canonical form.
       (aliases (cwtime (svex-mod->initial-aliases modidx 0 moddb aliases)
                        :mintime 1))
       (aliases (cwtime (canonicalize-alias-pairs flat-aliases aliases)
                        :mintime 1)))
    (mv nil flat-assigns flat-fixups flat-constraints moddb aliases))
  ///

  (verify-guards svex-design-flatten-fn)

  (defret alias-length-of-svex-design-flatten
    (implies (not err)
             (equal (len new-aliases)
                    (moddb-mod-totalwires
                     (moddb-modname-get-index (design->top x) new-moddb)
                     new-moddb))))

  (defret modidx-of-svex-design-flatten
    (implies (not err)
             (moddb-modname-get-index (design->top x) new-moddb))
  :rule-classes (:rewrite
                 (:type-prescription :corollary
                  (implies (not err)
                           (natp (moddb-modname-get-index (design->top x) new-moddb))))))

  (defret assigns-boundedp-of-svex-design-flatten
    (b* ((bound (moddb-mod-totalwires
                 (moddb-modname-get-index (design->top x) new-moddb)
                 new-moddb)))
      (and (svarlist-boundedp (assigns-vars flat-assigns) bound)
           (svarlist-boundedp (constraintlist-vars flat-constraints) bound)
           (svarlist-boundedp (assigns-vars flat-fixups) bound)
           ;; (svarlist-boundedp (svar-map-vars res-delays) (len aliases))
           )))

  (defretd normalize-stobjs-of-<fn>
    (implies (syntaxp (not (and (equal aliases ''nil)
                                (equal moddb ''nil))))
             (equal <call>
                    (let ((moddb nil) (aliases nil)) <call>)))))


(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (acl2::use-trivial-ancestors-check))


(local
 (defthm svarlist-addr-p-of-lhsarr-to-svexarr
   (implies (and (svarlist-addr-p (aliases-vars aliases))
                 (equal (len init) (len aliases)))
            (svarlist-addr-p (svexarr-vars (lhsarr-to-svexarr 0 aliases init))))
   :hints (("goal" :do-not-induct t
            :in-theory (disable vars-of-get-svex
                                ACL2::NATP-WHEN-GTE-0)))))

(local (defthm svex-alist-p-of-fast-alist-fork
         (implies (and (svex-alist-p x)
                       (svex-alist-p y))
                  (svex-alist-p (fast-alist-fork x y)))))

(define assigns-compose ((x assigns-p)
                         (alist svex-alist-p))
  :returns (new-x sv::assigns-p)
  :measure (len (sv::assigns-fix x))
  (b* ((x (sv::assigns-fix x))
       ((when (atom x)) nil)
       ((cons key (driver dr)) (car x)))
    (cons (cons key (change-driver dr :value (svex-compose dr.value alist)))
          (assigns-compose (cdr x) alist)))
  ///
  (defret vars-of-assigns-compose
    (implies (and (not (member v (assigns-vars x)))
                  (not (member v (svex-alist-vars alist))))
             (not (member v (assigns-vars new-x))))
    :hints(("Goal" :in-theory (enable assigns-vars)))))


(define svex-alist-truncate-by-var-decls ((x svex-alist-p)
                                          (var-decls var-decl-map-p)
                                          (acc svex-alist-p))
  :returns (new-x svex-alist-p)
  (b* (((when (atom x)) (svex-alist-fix acc))
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (svex-alist-truncate-by-var-decls (cdr x) var-decls acc))
       ((cons var val) (car x))
       (wire (cdr (hons-get var (var-decl-map-fix var-decls))))
       ((unless wire)
        (svex-alist-truncate-by-var-decls (cdr x) var-decls acc))
       ((wire wire))
       (acc (cons (cons var (svex-concat wire.width val 0)) (svex-alist-fix acc))))
    (svex-alist-truncate-by-var-decls (cdr x) var-decls acc))
  ///
  (defret vars-of-<fn>
    (implies (and (svarlist-addr-p (svex-alist-vars x))
                  (svarlist-addr-p (svex-alist-vars acc)))
             (svarlist-addr-p (svex-alist-vars new-x)))
    :hints(("Goal" :in-theory (enable svex-alist-vars))))

  (local (in-theory (enable svex-alist-fix))))

(define svex-normalize-assigns ((assigns assigns-p)
                                (fixups assigns-p)
                                (constraints constraintlist-p)
                                (var-decls var-decl-map-p)
                                (aliases))
  :guard (and ;; (svarlist-boundedp (svar-map-vars delays) (aliass-length aliases))
          (svarlist-boundedp (assigns-vars assigns) (aliass-length aliases))
          (svarlist-boundedp (assigns-vars fixups) (aliass-length aliases))
          (svarlist-boundedp (constraintlist-vars constraints) (aliass-length aliases))
          ;; (svarlist-addr-p (aliases-vars aliases))
          )
  :verify-guards nil
  :returns (mv (res-assigns svex-alist-p)
               (res-delays svar-map-p)
               (res-constraints constraintlist-p))
  :prepwork ((local (defthm cdr-last-of-svex-alist
                      (implies (svex-alist-p x)
                               (not (cdr (last x)))))))
  (b* (
       ;; The alias table contains LHSes, which are a different data
       ;; structure than SVEXes but can be translated to them.  We populate
       ;; svexarr with the direct translations of the canonical aliases.
       ((acl2::local-stobjs svexarr)
        (mv res-assigns res-delays res-constraints svexarr))
       (svexarr (resize-svexs (aliass-length aliases) svexarr))
       (svexarr (cwtime (lhsarr-to-svexarr 0 aliases svexarr)))


       ;; Canonicalize the assigns list by substituting variables for their canonical forms.
       (norm-assigns (cwtime (assigns-subst assigns aliases svexarr)))
       (norm-fixups (cwtime (assigns-subst fixups aliases svexarr)))
       (norm-constraints (cwtime (constraintlist-subst-from-svexarr constraints aliases svexarr)))
       ;; (norm-delays  (cwtime (svar-map-subst delays aliases svexarr)))

       ;; (- (sneaky-save 'norm-assigns norm-assigns))
       ;; Translate, e.g.,
       ;; assign { a[5:3], b[4:1] } = c
       ;; to:
       ;; assign a = { z, c[6:4], 3'bz }
       ;; assign b = { z, c[3:0], 1'bz }
       ;; that is, simplify the assignments so that we have only assignments to whole wires.
       (net-assigns (cwtime (assigns->netassigns norm-assigns)))
       ;; (net-delays (cwtime (assigns->netassigns norm-delays)))

       ;; (- (sneaky-save 'net-assigns net-assigns))

       ;; Resolve together multiple assignments to the same wire.
       (res-assigns (make-fast-alist (cwtime (netassigns->resolves net-assigns))))

       ;; compose norm-fixups with res-assigns
       (final-fixups (assigns-compose norm-fixups res-assigns))

       (final-assigns1 (fast-alist-free
                        (fast-alist-clean
                         (svex-apply-overrides (assigns-to-overrides final-fixups) res-assigns))))

       (final-assigns (svex-alist-truncate-by-var-decls final-assigns1 var-decls nil))
       ;; Collect all variables referenced and add delays as needed.
       (delayvars (svarlist-collect-delays (svexlist-collect-vars (svex-alist-vals res-assigns))))
       (res-delays (delay-svarlist->delays delayvars)))
    (mv final-assigns res-delays norm-constraints svexarr))
  ///
  (deffixequiv svex-normalize-assigns)

  (defthm svexlist-vars-of-svex-alist-vals
    (equal (svexlist-vars (svex-alist-vals x))
           (svex-alist-vars x))
    :hints(("Goal" :in-theory (enable svex-alist-vals svex-alist-vars svexlist-vars))))

  (verify-guards svex-normalize-assigns
    :guard-debug t
    :hints (("goal" :do-not-induct t
             :in-theory (disable member-equal))))

  (defret vars-of-svex-normalize-assigns
    (implies (svarlist-addr-p (aliases-vars aliases))
             (svarlist-addr-p (svex-alist-vars res-assigns))))

  (defret vars-of-svex-normalize-assigns-delays
    (implies (svarlist-addr-p (aliases-vars aliases))
             (svarlist-addr-p (svar-map-vars res-delays))))

  (defret vars-of-svex-normalize-assigns-constraints
    (implies (svarlist-addr-p (aliases-vars aliases))
             (svarlist-addr-p (constraintlist-vars res-constraints)))))

(define svar-map-compose ((x svar-map-p) (al svex-alist-p))
  :returns (xx svex-alist-p)
  :measure (len (svar-map-fix x))
  (b* ((x (svar-map-fix x))
       ((when (atom x)) nil)
       ((cons key val) (car x))
       (expr (svex-lookup val al)))
    (cons (cons key (or expr (make-svex-var :name val)))
          (svar-map-compose (cdr x) al))))

(define svex-compose-delays ((x svar-map-p)
                             (updates svex-alist-p)
                             (masks svex-mask-alist-p))
  :short "Compose delays with updates."
  :long "<p>X is the delay map, that is, an alist mapping (delay-1) svars
to (delay-0) svars.  Updates maps svars to their update functions.  Masks is
the mask alist for the updates.  Usually, the undelayed variable is present in
the updates, so we just say that is the update function.  If it isn't present,
though, then it should be treated as basically a PI.  But it still needs to be
properly masked.  So for the moment, we look up the delayed variable in the
mask alist and mask the RHS by that care mask.  This isn't the greatest
solution because don't-care bits won't match their expected values, so we
should address this again later.</p>"
  :returns (xx svex-alist-p)
  :measure (len (svar-map-fix x))
  (b* ((x (svar-map-fix x))
       ((when (atom x)) nil)
       ((cons key val) (car x))
       (expr (svex-fastlookup val updates))
       (expr (or expr
                 ;; Bozo -- convert this to a zero-extend when possible?
                 (make-svex-call
                  :fn 'bit?
                  :args (list (svex-quote (2vec (sparseint-val (svex-mask-lookup (make-svex-var :name key) masks))))
                              ;; care
                              (make-svex-var :name val)
                              ;; don't-care
                              (svex-quote (2vec 0)))))))
    (cons (cons key expr)
          (svex-compose-delays (cdr x) updates masks))))




(define svex-compose-assigns/delays ((assigns svex-alist-p)
                                     (delays svar-map-p)
                                     (constraints constraintlist-p)
                                     &key
                                     (rewrite 't)
                                     (verbosep 'nil))
  :returns (mv (updates svex-alist-p)
               (nextstates svex-alist-p)
               (full-constraints constraintlist-p))
  (b* ((updates (cwtime (svex-assigns-compose assigns :rewrite rewrite) :mintime 1))
       (masks (svexlist-mask-alist (svex-alist-vals updates)))
       ((with-fast updates))
       (next-states (cwtime (svex-compose-delays delays updates masks) :mintime 1))
       (full-constraints (cwtime (constraintlist-compose constraints updates) :mintime 1))
       (- (clear-memoize-table 'svex-compose))
       ((unless rewrite)
        (mv updates next-states full-constraints))
       (rewritten (svex-alist-rewrite-fixpoint (append updates next-states)
                                               :verbosep verbosep
                                               :count 2))
       (updates-len (len updates))
       (updates (take updates-len rewritten))
       (next-states (nthcdr updates-len rewritten)))
    (clear-memoize-table 'svex-compose)
    (mv updates next-states full-constraints)))


;; (defsection addr-p-when-normordered
;;   (local (defthm lhatom-addr-p-when-normordered
;;            (implies (lhatom-normorderedp bound offset atom)
;;                     (svarlist-addr-p (lhatom-vars atom)))
;;            :hints(("Goal" :in-theory (enable lhatom-vars lhatom-normorderedp)))))

;;   (local (Defthm lhs-addr-p-when-normordered
;;            (implies (lhs-vars-normorderedp bound offset lhs)
;;                     (svarlist-addr-p (lhs-vars lhs)))
;;            :hints(("Goal" :in-theory (enable lhs-vars-normorderedp lhs-vars)))))

;;   (local (defthm aliases-addr-p-when-normordered-aux
;;            (implies (aliases-normorderedp aliases)
;;                     (svarlist-addr-p (aliases-vars-aux n aliases)))
;;            :hints(("Goal" :in-theory (enable aliases-vars-aux)
;;                    :induct (aliases-vars-aux n aliases))
;;                   (and stable-under-simplificationp
;;                        '(:use ((:instance lhs-addr-p-when-normordered
;;                                 (bound (1- n)) (offset 0) (lhs (nth (1- n) aliases))))
;;                          :in-theory (disable lhs-addr-p-when-normordered))))))

;;   (defthm aliases-addr-p-when-normordered
;;     (implies (aliases-normorderedp aliases)
;;              (svarlist-addr-p (aliases-vars aliases)))
;;     :hints(("Goal" :in-theory (enable aliases-vars)))))

(define svex-design-flatten-and-normalize ((x design-p)
                                           &key
                                           (indexedp 'nil)
                                           ((moddb "overwritten") 'moddb)
                                           ((aliases "overwritten") 'aliases))

  :parents (svex-compilation)
  :short "Flatten a hierarchical SV design and apply alias normalization to it."
  :long "<p>This does all of the steps of @(see svex-design-compile) except for
         the final composition of local assignments into global 0-delay update
         functions.</p>"
  :returns (mv err
               (flat-assigns svex-alist-p)
               (flat-delays svar-map-p)
               (flat-constraints constraintlist-p)
               (new-moddb (and (moddb-basics-ok new-moddb)
                               (moddb-mods-ok new-moddb)))
               (new-aliases))
  :guard (modalist-addr-p (design->modalist x))
  :verify-guards nil
  (b* (((mv err assigns fixups constraints moddb aliases)
        (svex-design-flatten x))
       ((when err)
        (mv err nil nil nil moddb aliases))
       (modidx (moddb-modname-get-index (design->top x) moddb))
       ((mv aliases var-decl-map)
        (if indexedp
            (b* ((map (cwtime
                       (aliases-to-var-decl-map aliases
                                                (make-modscope-top :modidx modidx)
                                                moddb)
                       :mintime 1)))
              (mv aliases map))
          (cwtime (aliases-indexed->named aliases
                                          (make-modscope-top :modidx modidx)
                                          moddb)
                  :mintime 1)))
       ((mv res-assigns res-delays res-constraints)
        (svex-normalize-assigns assigns fixups constraints var-decl-map aliases)))
    (mv nil res-assigns res-delays res-constraints moddb aliases))
  ///
  (verify-guards svex-design-flatten-and-normalize-fn
    :hints(("Goal" :in-theory (enable modscope-okp
                                      modscope->modidx
                                      modscope-local-bound))))

  (defret alias-length-of-svex-design-flatten-and-normalize
    (implies (not err)
             (equal (len new-aliases)
                    (moddb-mod-totalwires
                     (moddb-modname-get-index (design->top x) new-moddb)
                     new-moddb))))

  (defret modidx-of-svex-design-flatten-and-normalize
    (implies (not err)
             (moddb-modname-get-index (design->top x) new-moddb))
    :rule-classes (:rewrite
                   (:type-prescription :corollary
                    (implies (not err)
                             (natp (moddb-modname-get-index (design->top x) new-moddb))))))

  (defret vars-of-svex-design-flatten-and-normalize
    (implies (and (modalist-addr-p (design->modalist x))
                  (not indexedp))
             (svarlist-addr-p (svex-alist-vars flat-assigns))))

  (defret vars-of-svex-design-flatten-and-normalize-delays
    (implies (and (modalist-addr-p (design->modalist x))
                  (not indexedp))
             (svarlist-addr-p (svar-map-vars flat-delays))))

  (defret vars-of-svex-design-flatten-and-normalize-constraints
    (implies (and (modalist-addr-p (design->modalist x))
                  (not indexedp))
             (svarlist-addr-p (constraintlist-vars flat-constraints))))

  (defretd normalize-stobjs-of-<fn>
    (implies (syntaxp (not (and (equal aliases ''nil)
                                (equal moddb ''nil))))
             (equal <call>
                    (let ((moddb nil) (aliases nil)) <call>)))
    :hints(("Goal" :in-theory (enable normalize-stobjs-of-svex-design-flatten)))))


(define svex-design-compile ((x design-p)
                             &key
                             (indexedp 'nil)
                             ((moddb "overwritten") 'moddb)
                             ((aliases "overwritten") 'aliases)
                             (rewrite 't)
                             (verbosep 'nil))
  :parents (svex-compilation)
  :short "Compile a hierarchical SVEX design into a finite state machine."
  :returns (mv err
               (composed-updates svex-alist-p)
               (state-updates svex-alist-p)
               (composed-constraints constraintlist-p)
               (flat-assigns svex-alist-p)
               (flat-delays svar-map-p)
               (flat-constraints constraintlist-p)
               (new-moddb (and (moddb-basics-ok new-moddb)
                             (moddb-mods-ok new-moddb)))
               (new-aliases))
  :guard (modalist-addr-p (design->modalist x))
  :verify-guards nil
    (b* (((mv err res-assigns res-delays res-constraints moddb aliases)
          (svex-design-flatten-and-normalize x :indexedp indexedp))
         ((mv updates nextstates full-constraints)
          (svex-compose-assigns/delays res-assigns res-delays res-constraints
                                       :rewrite rewrite
                                       :verbosep verbosep)))
      (mv err updates nextstates full-constraints res-assigns res-delays res-constraints moddb aliases))
    ///
    (verify-guards svex-design-compile-fn
      :hints(("Goal" :in-theory (enable modscope-okp
                                        modscope->modidx
                                        modscope-local-bound))))

    (defret alias-length-of-svex-design-compile
      (implies (not err)
               (equal (len new-aliases)
                      (moddb-mod-totalwires
                       (moddb-modname-get-index (design->top x) new-moddb)
                       new-moddb))))

    (defret modidx-of-svex-design-compile
      (implies (not err)
               (moddb-modname-get-index (design->top x) new-moddb))
      :rule-classes (:rewrite
                     (:type-prescription :corollary
                      (implies (not err)
                               (natp (moddb-modname-get-index (design->top x) new-moddb)))))))
