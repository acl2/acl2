
; Multiplier verification

; Copyright (C) 2022 Intel Corporation
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
; Original author: Mertcan Temel <mert.temel@intel.com>

(in-package "RP")

(include-book "../fnc-defs")
(include-book "centaur/svl/top" :dir :system)
(include-book "centaur/sv/svex/lists" :dir :system)
(include-book "centaur/misc/sneaky-load" :dir :system)
(include-book "centaur/fgl/portcullis" :dir :system)

(include-book "heuristics")
(include-book "adder-patterns")
(include-book "macros")
(include-book "misc")
(include-book "quick-search")
(include-book "careful-search-from-counterpart")
(include-book "locally-simplify-for-fa-c")
(include-book "vector-adders")
(include-book "postprocess")

(local
 (include-book "centaur/bitops/ihs-extensions" :dir :system))

(local
 (include-book "ihs/logops-lemmas" :dir :system))

(local
 (rp::fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5
  :disabled t))

(local
 (defthm svexlist-p-of-remove-duplicates
   (implies (sv::Svexlist-p x)
            (sv::Svexlist-p (remove-duplicates-equal x)))))

(local
 (in-theory (disable acl2::merge-sort-lexorder
                     acl2::merge-lexorder)))

(local
 (in-theory (e/d (acl2::maybe-integerp
                  sv::svex-kind)
                 ((:e tau-system)))))


(rp::Def-rp-rule 4vec-p-of-FA/ha-S/c-CHAIN
  (and (sv::4vec-p (rp::fa-s-chain x y z))
       (sv::4vec-p (rp::fa-c-chain m x y z))
       (sv::4vec-p (rp::ha-s-chain y z))
       (sv::4vec-p (rp::ha-c-chain y z))
       (sv::4vec-p (rp::ha+1-c-chain y z))
       (sv::4vec-p (RP::HA+1-S-CHAIN m y z)))
  :hints (("Goal"
           :in-theory (e/d (rp::ha+1-c-chain
                            RP::HA+1-S-CHAIN
                            rp::ha-c-chain
                            rp::ha-s-chain
                            rp::fa-c-chain
                            rp::fa-s-chain) ()))))

(defines svex-has-bitxor-0
  (define svex-has-bitxor-0 ((x sv::svex-p))
    :measure (sv::svex-count x)
    (sv::Svex-case
     x
     :var nil
     :quote nil
     :call (case-match x
             (('sv::bitxor 0 &) t)
             (('sv::bitxor & 0) t)
             (& (svexlist-has-bitxor-0 x.args)))))
  (define svexlist-has-bitxor-0 ((lst sv::svexlist-p))
    :measure (sv::svexlist-count lst)
    (if (atom lst)
        nil
      (or (svex-has-bitxor-0 (car lst))
          (svexlist-has-bitxor-0 (cdr lst)))))
  ///
  (memoize 'svex-has-bitxor-0))

(local
 ;; some more lemmas first.
 (defsection 4vec-lemmas

   (defthm 4vec-concat$-to-logapp
     (implies (and (natp size)
                   (integerp x)
                   (integerp y))
              (equal (svl::4vec-concat$ size x y)
                     (logapp size x y)))
     :hints (("goal"
              :in-theory (e/d (svl::4vec-concat$
                               svl::logapp-to-4vec-concat)
                              ()))))

   (defthm sv::4vec-bitops-to-logops
     (and (implies (and (integerp x)
                        (integerp y))
                   (and (equal (sv::4vec-bitxor x y)
                               (logxor x y))
                        (equal (sv::4vec-bitand x y)
                               (logand x y))
                        (equal (sv::4vec-bitor x y)
                               (logior x y))))
          (implies (integerp x)
                   (equal (sv::4vec-bitnot x)
                          (lognot x))))
     :hints (("goal"
              :do-not-induct t
              :in-theory (e/d* (sv::4vec
                                sv::4vec-bitand
                                sv::3vec-bitand
                                sv::3vec-bitor
                                sv::4vec-bitor
                                sv::3vec-bitnot
                                sv::4vec-bitnot
                                bitops::ihsext-inductions
                                bitops::ihsext-recursive-redefs
                                sv::4vec-bitxor
                                sv::4vec->lower
                                sv::4vec->upper
                                sv::4vec-rsh
                                sv::4vec-shift-core
                                svl::bits
                                sv::4vec-part-select
                                sv::4vec-concat)
                               (floor
                                svl::equal-of-4vec-concat-with-size=1
                                logand)))))

   (defthm sv::svexlist-eval$-when-consp
     (implies (consp lst)
              (equal (sv::svexlist-eval$ lst env)
                     (cons (sv::svex-eval$ (car lst) env)
                           (sv::svexlist-eval$ (cdr lst) env)))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod find-f/h-adders-state
  ((pp-id-cleaned :default nil)
   (reduce-bit-negations :default nil)
   (track-column? integerp :default -1)

   (only-quick-search :default nil)
   (skip-vector-adder :default nil)
   (skip-light-simplify :default nil)
   )
  :layout :fulltree
  ;;:hons t
  )

(with-output
  :off :all
  :gag-mode :goals
  :on (error summary)
  (define find-f/h-adders-in-svex-alist ((svex-alist sv::svex-alist-p)
                                         (limit natp)
                                         &key
                                         ((adder-type symbolp) 'adder-type)
                                         ((env) 'env)
                                         ((context rp-term-listp) 'context)
                                         ((config svl::svex-reduce-config-p) 'config)
                                         ((tstate find-f/h-adders-state-p)
                                          'tstate))

    :prepwork
    ((defconst *find-f/h-adders-in-svex-alist-limit*
       50)
     (local
      (in-theory (disable fast-alist-clean))))
    :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p svex-alist))
    :measure (nfix limit)
    (b* (;; gather some basics
         ((find-f/h-adders-state tstate) tstate)
         (adder-str (If (eq adder-type 'ha) "half-adder" "full-adder"))
         (pass-num (+ 1 (- limit) *find-f/h-adders-in-svex-alist-limit*))
         (track-column? (posp tstate.track-column?))
         (try-continue-without-track-column? (and*-exec track-column?
                                                        (< tstate.track-column?
                                                           (1+ *find-f/h-adders-in-svex-alist-limit*))))
         (tstate (change-find-f/h-adders-state tstate
                                               :track-column? (1- tstate.track-column?)))

         ((when (zp limit))
          (progn$
           (cw "----
WARNING: Iteration limit of ~p0 is reached. Will not parse again for ~s1 patterns. Either there is an unexpected infinite loop, or the iteration limit may need to be increased.
----~%"
               *find-f/h-adders-in-svex-alist-limit* adder-str)
           svex-alist))
         (first-pass? (= pass-num 1))
         (- (and first-pass?
                 (cw "--- Searching for ~s0 patterns now. ~%" adder-str)))
         (- (cw "-- Pass #~p0:~%" pass-num))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; maybe clean up a bit before moving on. Simplification might have messed up with argument orders.
         (svex-alist (if (or* (> pass-num 1) (eq adder-str 'ha))
                         (b* (;;(svex-alist (global-zero-fa-c-chain-extra-arg-alist svex-alist))
                              (svex-alist (fix-order-of-fa/ha-chain-args-alist svex-alist)))
                           svex-alist)
                       svex-alist))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; Perform quick search.
         ;;(-    (clear-memoize-table     'adder-pattern-match))    ;;    maybe
         ;;unnecessary. taking it out becuase large booth encodings will have a
         ;;lot of rep
         ((mv pattern-alist &)
          (gather-adder-patterns-in-svex-alist svex-alist))
         (new-svex-alist (replace-adder-patterns-in-svex-alist svex-alist))
         (pattern-alist (fast-alist-clean pattern-alist))
         (replaced-pattern-cnt (count-newly-found-adders-in-pattern-alist pattern-alist))
         (- (cw "- Quick search found and replaced ~p0 ~s1 patterns. ~%" replaced-pattern-cnt adder-str))

         (- (and (equal replaced-pattern-cnt 0)
                 (not (equal svex-alist new-svex-alist))
                 (cw "-> Even though statistics showed 0 new pattern match, ~
                 some missed patterns have actually been replaced.  ~%")))

         ((when tstate.only-quick-search)
          (progn$ (fast-alist-free pattern-alist)
                  (if (equal svex-alist new-svex-alist)
                      new-svex-alist
                    (find-f/h-adders-in-svex-alist new-svex-alist (1- limit)))))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; Only for the first pass of FA, also do an vector adder search.
         ;; This is not necessary but can  help with performance by reducing pass
         ;; count.
         ((mv new-svex-alist2 tstate)
          (b* (((when tstate.skip-vector-adder)
                (mv new-svex-alist tstate))
               ((Unless (and first-pass? (eq adder-type 'fa)))
                (mv new-svex-alist tstate))

               (- (cw "- Looking and rewriting for vector adder patterns... ~%"))
               (new-svex-alist2 (ppx-simplify-alist new-svex-alist))
               (vector-adder-changed (not (equal new-svex-alist2 new-svex-alist)))
               (- (if vector-adder-changed
                      (cw "-> Success! Rewriting for vector adder made some changes. Let's make another pass. ~%")
                    (cw "-> No change from vector adder simplification. ~%")))
               (tstate (change-find-f/h-adders-state tstate
                                                     :skip-vector-adder t)))
            (mv new-svex-alist2 tstate)))
         ((unless (equal svex-alist new-svex-alist2))
          (progn$ (fast-alist-free pattern-alist)
                  (find-f/h-adders-in-svex-alist new-svex-alist2 (1- limit))))

         ;; TODO: to prevent  consing, can do some preliminary check  here for if
         ;; there exists xor chains OR maybe fa-* functions under or gates.

         ;; TODO:  HERE I  can look  for bitxors  with at  least 3  elements to
         ;; decide if any fa-s/ha-s might be mising before consing below..

         (- (cw "- Now will look  more carefully if we ~
 missed any ~s0-s pattern that  has a found counterpart ~s0-c pattern...~%"
                adder-str))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; Carefully looking for fa/ha-s patterns:

         (exploded-args-and-args-alist (process-fa/ha-c-chain-pattern-args pattern-alist 'exploded-args-and-args-alist))
         ((mv new-svex-alist &)
          (careful-search-from-counterpart-svex-alist svex-alist exploded-args-and-args-alist))
         (- (fast-alist-free exploded-args-and-args-alist))
         ((Unless (equal new-svex-alist svex-alist))
          (progn$ (cw "-> Success! Some missed ~s0-s patterns are found and their shape is ~
       updated. This will reveal more ~s0 patterns during quick search. So will ~
       now do another pass. There might be an overlap in the statistics below. ~%"
                      adder-str)
                  (fast-alist-free pattern-alist)
                  (find-f/h-adders-in-svex-alist new-svex-alist (1- limit))))
         (- (cw "-> Careful search did not reveal any new ~s0-s. ~%" adder-str))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; Carefully looking for ha-c, ha+1-c patterns:
         (careful-look-for-ha-c (equal adder-type 'ha))
         (- (fast-alist-free pattern-alist))
         (new-svex-alist
          (and careful-look-for-ha-c
               (b* ((- (cw "- Now will look  more carefully if we missed any ha-c/ha+1-c pattern that  has a found counterpart ha-s/ha+1-s patterns...~%"
                           adder-str))
                    (exploded-args-and-args-alist (process-fa/ha-c-chain-pattern-args
                                                   pattern-alist
                                                   'exploded-args-and-args-alist
                                                   :adder-type 'ha-c))
                    ((mv svex-alist &)
                     (careful-search-from-counterpart-svex-alist svex-alist exploded-args-and-args-alist
                                                                 :adder-type 'ha-c))
                    (- (fast-alist-free exploded-args-and-args-alist))

                    (exploded-args-and-args-alist (process-fa/ha-c-chain-pattern-args
                                                   pattern-alist
                                                   'exploded-args-and-args-alist
                                                   :adder-type 'ha+1-c))
                    ((mv svex-alist &)
                     (careful-search-from-counterpart-svex-alist svex-alist exploded-args-and-args-alist
                                                                 :adder-type 'ha+1-c))
                    (- (fast-alist-free exploded-args-and-args-alist)))
                 svex-alist)))
         ((Unless (or (not careful-look-for-ha-c)
                      (hons-equal new-svex-alist svex-alist)))
          (progn$ (cw "-> Success! Some missed ~s0-c patterns are found and their shape is ~
       updated. This will reveal more ~s0 patterns during quick search. So will ~
       now do another pass. There might be an overlap in the statistics below. ~%"
                      adder-str)
                  (find-f/h-adders-in-svex-alist new-svex-alist (1- limit))))
         (- (and careful-look-for-ha-c
                 (cw "-> Careful search did not reveal any new ~s0-c. ~%" adder-str)))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; Vector adder simplification
         ((mv svex-alist tstate exit?)
          (b* (((when tstate.skip-vector-adder)
                (mv svex-alist tstate nil))
               (- (cw "- Looking and rewriting for vector adder patterns... ~%"))
               (new-svex-alist (ppx-simplify-alist svex-alist))
               (vector-adder-changed (not (equal new-svex-alist svex-alist)))
               (- (if vector-adder-changed
                      (cw "-> Success! Rewriting for vector adder made some changes. Let's make another pass. ~%")
                    (cw "-> No change from vector adder simplification. ~%")))
               (tstate (change-find-f/h-adders-state tstate
                                                     :skip-vector-adder t)))
            (mv new-svex-alist tstate vector-adder-changed)))
         ((when exit?)
          (find-f/h-adders-in-svex-alist svex-alist (1- limit)))

         ((when (and*-exec (equal adder-type 'ha)
                           (not tstate.skip-light-simplify)))
          (b* ((- (cw "- Let's run a light-weight bitand/xor/or simplification.~%"))
               (new-svex-alist (svl::light-svex-alist-simplify-bitand/or/xor svex-alist))
               ;; so that light simplify is run only once..
               (tstate (change-find-f/h-adders-state tstate
                                                     :skip-light-simplify t))
               ((when (not (equal new-svex-alist svex-alist)))
                (progn$ (cw "-> Light-weight simplification made some changes. Let's make another pass. ~%")
                        (find-f/h-adders-in-svex-alist new-svex-alist (1- limit))))
               (- (cw "-> No change from light-weight simplification. ~%"))

               ((when try-continue-without-track-column?)
                (b* ((- (cw "~%-- Going to try again with less restrictions... ~%"))
                     (tstate (change-find-f/h-adders-state tstate
                                                           :track-column? 0)))
                  (find-f/h-adders-in-svex-alist svex-alist (1- limit)))))
            svex-alist))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; Do not move forward unless fa
         ((unless (equal adder-type 'fa))
          (b* (((Unless try-continue-without-track-column?) svex-alist)
               (- (cw "--- Going to try again without tracking the  column number... ~%"))
               (tstate (change-find-f/h-adders-state tstate
                                                     :track-column? 0)))
            (find-f/h-adders-in-svex-alist svex-alist (1- limit))))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; Local simplification to reveal fa-c patterns
         (- (cw "- Let's see if local bitxor/or/and simplification can reveal more fa-c patterns... ~%"))
         (config (svl::change-svex-reduce-config ;; make sure config is set correctly.
                  config :skip-bitor/and/xor-repeated nil))

         ;;(- (design_res-broken svex-alist "before simplify-to-find-fa-c-patterns-alist"))

         (new-svex-alist (simplify-to-find-fa-c-patterns-alist svex-alist :strength 0))

         ;;(- (design_res-broken new-svex-alist "after simplify-to-find-fa-c-patterns-alist"))

         ((Unless (hons-equal new-svex-alist svex-alist))
          (progn$ (cw "-> Success! some fa-c patterns are revealed. Let's make another pass.~%")
                  (find-f/h-adders-in-svex-alist new-svex-alist (1- limit))))

         (- (and
             (aggressive-find-adders-in-svex)
             (cw "- Nothing. Let's increase local simplification strength from 0 to 1 and try again. ~%")))
         (new-svex-alist (if (aggressive-find-adders-in-svex)
                             (simplify-to-find-fa-c-patterns-alist svex-alist :strength 1)
                           svex-alist))
         ((Unless (hons-equal new-svex-alist svex-alist))
          (progn$ (cw "-> Success! some fa-c patterns are revealed. Let's make another pass.~%")
                  (find-f/h-adders-in-svex-alist new-svex-alist (1- limit))))

         (- (and
             (aggressive-find-adders-in-svex)
             (cw "- Nothing. Let's increase local simplification strength from 1 to 4 and try again. ~%")))
         (new-svex-alist (if (aggressive-find-adders-in-svex)
                             (simplify-to-find-fa-c-patterns-alist svex-alist :strength 4)
                           svex-alist))
         ((Unless (hons-equal new-svex-alist svex-alist))
          (progn$ (cw "-> Success! some fa-c patterns are revealed. Let's make another pass.~%")
                  (find-f/h-adders-in-svex-alist new-svex-alist (1- limit))))

         (- (cw "-> Nothing found from local simplifications. ~%"))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; Push in negations
         (- (and tstate.reduce-bit-negations
                 (cw "- Will try to see if we can shrink the svexes by reducing negations~%")))
         (new-svex-alist (if tstate.reduce-bit-negations
                             (svl::svex-alist-reduce-bit-negations svex-alist)
                           svex-alist))
         ((Unless (hons-equal new-svex-alist svex-alist))
          (progn$ (cw "-> Some negation chains are reduced. ~%")
                  (find-f/h-adders-in-svex-alist new-svex-alist (1- limit))))
         (- (and tstate.reduce-bit-negations
                 (cw "-> No change from negation compresions~%")))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; ;; RW  corner cases
         ;; (- (cw "- Will try to see if we can rewrite some known patterns~%"))
         ;; (new-svex-alist (rw-adder-corner-cases-alist svex-alist))
         ;; ((Unless (hons-equal new-svex-alist svex-alist))
         ;;  (progn$ (cw "-> Some known patterns are cleaned. ~%")
         ;;          (find-f/h-adders-in-svex-alist new-svex-alist (1- limit))))
         ;; (- (cw "-> No change from known pattern rw. ~%"))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; Clean out IDs that possible came from wrapping PP with IDs stage.
         ((unless (or (not (aggressive-find-adders-in-svex))
                      tstate.pp-id-cleaned))
          (b*  ((tstate (change-find-f/h-adders-state tstate
                                                      :pp-id-cleaned t))
                (- (cw "- Let's run a light-weight bitand/xor/or simplification.~%"))
                (svex-alist (svl::light-svex-alist-simplify-bitand/or/xor svex-alist))
                (- (cw "- Let's extract from IDs and make another pass. ~%"))
                (svex-alist (extract-svex-from-id-alist svex-alist))
                )
            (find-f/h-adders-in-svex-alist svex-alist (1- limit))))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; Global simplification unless disabled.
         ((unless (find-adders-global-bitand/or/xor-simplification-enabled))
          (progn$ (cw "- Skipping global simplification because it is disabled at this stage with (enable-find-adders-global-bitand/or/xor-simplification nil). Ending the search.~%")
                  svex-alist))
         (- (cw "- Let's try global bitxor/and/or simplification. ~%"))
         (new-svex-alist (svl::light-svex-alist-simplify-bitand/or/xor svex-alist ))
         ((when (hons-equal new-svex-alist svex-alist))
          (progn$ (cw "-> Global bitxor/and/or simplification did not change anything. Ending the search.~%")
                  svex-alist))
         (- (cw "-> Global bitxor/and/or simplification made some changes. Let's make another pass. ~%"))

         ;; careful-search-from-counterpart-svex-alist  may  cause  new  simplify-able
         ;; patterns to  occur. but not sure  if something less general  would be
         ;; useful here. TODO: investigate.
         #|(new-svex-alist (svl::svex-alist-simplify-bitand/or/xor  new-svex-alist
         :config config))|#

         )
      (find-f/h-adders-in-svex-alist new-svex-alist (1- limit)))
    ///
    (defret <fn>-is-correct
      (implies (and (sv::svex-alist-p svex-alist)
                    (rp::rp-term-listp context)
                    (rp::valid-sc env-term a)
                    (rp::eval-and-all context a)
                    (rp::falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (force (warrants-for-adder-pattern-match))

                    (or (equal adder-type 'ha)
                        (equal adder-type 'fa))
                    )
               (equal (sv::svex-alist-eval$ res (rp-evlt env-term a))
                      (sv::svex-alist-eval$ svex-alist (rp-evlt env-term a))))
      :hints (("Goal"
               ;;:do-not-induct t
               :expand (;;(find-f/h-adders-in-svex-alist svex-alist limit)
                        (exploded-args-and-args-alist-inv nil (rp-evlt env-term a)))
               :in-theory (e/d ()
                               (valid-sc
                                valid-sc-subterms
                                rp-trans
                                rp-term-listp
                                rp-trans-lst
                                eval-and-all
                                falist-consistent-aux
                                ex-from-rp)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; SET UP THE META FUNCTION..
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(make-event
 `(define svex-reduce-w/-env-config-1 ()
    :returns (config svl::svex-reduce-config-p)
    (svl::make-svex-reduce-config
     :width-extns ',(strip-cars (table-alist 'svl::width-of-svex-extns (w state)))
     :integerp-extns ',(strip-cars (table-alist 'svl::integerp-of-svex-extns (w state)))
     :keep-missing-env-vars (keep-missing-env-vars-in-svex))
    ///
    (defret <fn>-correct
      (and (implies (warrants-for-adder-pattern-match)
                    (and (svl::width-of-svex-extn-correct$-lst
                          (svl::svex-reduce-config->width-extns config))
                         (svl::integerp-of-svex-extn-correct$-lst
                          (svl::svex-reduce-config->integerp-extns config)))))
      :hints (("Goal"
               :do-not-induct t
               :use (,@(loop$ for x in (strip-cdrs (table-alist 'svl::width-of-svex-extns (w state)))
                              collect
                              `(:instance ,x))
                     ,@(loop$ for x in (strip-cdrs (table-alist 'svl::integerp-of-svex-extns (w state)))
                              collect
                              `(:instance ,x)))
               :in-theory (e/d (svl::width-of-svex-extn-correct$-lst)
                               (svl::integerp-of-svex-extn-correct$
                                svl::width-of-svex-extn-correct$)
                               ))))
    (in-theory (disable (:e svex-reduce-w/-env-config-1)))))

(local
 (in-theory (enable subsetp-equal)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Subtle: create some aux lemmas/functions to make this a meta-rule for RP-Rewriter.
(progn
  (def-formula-checks-default-evl
    rp-evl
    (list* 'apply$ 'badge-userfn 'apply$-userfn
           (strip-cars rp::*small-evl-fncs*)))

  (with-output
    :off :all :on (error comment)
    :gag-mode nil
    (rp::def-formula-checks
      find-adders-in-svex-formula-checks-small
      (int-vector-adder-lst-w/carry binary-or binary-? binary-not binary-xor binary-and s-spec c-spec)
      :warranted-fns
      (ha-c-chain
       ha-s-chain
       fa-c-chain
       fa-s-chain
       full-adder
       half-adder
       int-vector-adder
       ha+1-c-chain
       ha+1-s-chain)))

  (defun find-adders-in-svex-formula-checks (state)
    (declare (xargs :stobjs (state)))
    (and (find-adders-in-svex-formula-checks-small state)
         (svl::svex-ev-wog-formula-checks state) ;; using this here to save
         ;; certification time instead of adding all those svex-eval functions.
         )))

(local
 (defthm find-adders-in-svex-formula-checks-implies-svex-reduce-formula-checks
   (implies (find-adders-in-svex-formula-checks state)
            (svl::svex-reduce-formula-checks state))
   :hints (("Goal"
            :in-theory (e/d (find-adders-in-svex-formula-checks
                             svl::svex-reduce-formula-checks
                             svl::svex-ev-wog-formula-checks)
                            ())))))

(make-event
 (b* ((w '((apply$-warrant-ha-c-chain)
           (apply$-warrant-fa-c-chain)
           (apply$-warrant-ha+1-c-chain)
           (apply$-warrant-ha+1-s-chain)
           (apply$-warrant-ha-s-chain)
           (apply$-warrant-fa-s-chain)
           (apply$-warrant-full-adder)
           (apply$-warrant-half-adder)
           (apply$-warrant-int-vector-adder))))
   `(define check-context-for-adder-warrants ((context rp-term-listp))
      :returns valid
      (subsetp-equal ',w context)
      ///
      (local
       (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))
      (local
       (defthm member-equal-and-eval-and-all
         (implies (and (eval-and-all context a)
                       (member-equal x context))
                  (and (rp-evlt x a)
                       (implies (force (not (include-fnc x 'list)))
                                (rp-evl x a))))
         :rule-classes (:rewrite)))
      (local
       (in-theory (disable eval-and-all)))
      (defret <fn>-is-correct
        (implies (and (eval-and-all context acl2::unbound-free-env)
                      (rp-evl-meta-extract-global-facts)
                      (find-adders-in-svex-formula-checks state)
                      valid)
                 (and ,@w))
        :hints (("Goal"
                 :do-not-induct t
                 :in-theory (e/d () ())))))))

(define vescmul-clear-memoize-tables ()
  (progn$ (clear-memoize-table 's-order)
          (clear-memoize-table 'svl::width-of-svex-fn)
          (clear-memoize-table 'svl::integerp-of-svex-fn)
          (clear-memoize-table 'svl::svex-reduce-w/-env-fn)
          (clear-memoize-table 'svl::svex-reduce-w/-env-masked-fn)
          (clear-memoize-table 'adder-pattern-match)
          (clear-memoize-table 'clear-adder-fnc-from-unfloat)
          (clear-memoize-table 'replace-adder-patterns-in-svex)
          ;; (clear-memoize-table 'fix-order-of-fa/ha-s-args)
          (clear-memoize-table 'svl::bitand/or/xor-cancel-repeated)
          (clear-memoize-table 'simplify-to-find-fa-c-patterns-fn)
          (clear-memoize-table 'wrap-pp-with-id-aux)
          (clear-memoize-table 'add-ha-c-for-shifted)
          (clear-memoize-table 'extract-svex-from-id)
          (clear-memoize-table 'global-zero-fa-c-chain-extra-arg)
          (clear-memoize-table 'fix-order-of-fa/ha-chain-args-fn)
          (clear-memoize-table 'ppx-simplify-fn)
          (clear-memoize-table 'remove-ha-under-gates)
          (clear-memoize-table 'remove-unpaired-fa-s-aux-fn)
          (clear-memoize-table 'merge-fa-s-c-chains)
          (clear-memoize-table 'add-ha-c-for-shifted-search)))

(with-output
  :off :all
  :gag-mode :goals
  :on (error summary)
  (define rewrite-adders-in-svex-alist ((term)
                                        (context rp-term-listp))
    :returns (mv res-term res-dont-rw)
    :guard-hints (("goal"
                   :case-split-limitations (0 1)
                   :in-theory (e/d ()
                                   (default-cdr
                                     default-car
                                     ex-from-rp
                                     (:type-prescription rp-term-listp)
                                     (:type-prescription acl2::binary-or*)))))
    :guard-debug t
    (time$
     (case-match term
       (('sv::svex-alist-eval ('quote svex-alist) env-orig)
        (b* ((- (vescmul-clear-memoize-tables))

             (env (rp::ex-from-rp env-orig))
             ((mv falistp env) (case-match env
                                 (('falist ('quote x) &) (mv t x))
                                 (& (mv nil env))))
             ((unless falistp)
              (if (and (consp env) (equal (car env) 'cons))
                  (progn$
                   (cw "Note: the environment of svex-eval-alist is not a fast-alist. Making it a fast-alist now.~%")
                   (mv `(sv::svex-alist-eval ',svex-alist (make-fast-alist ,env-orig))
                       `(nil t (nil t))))
                (mv term nil)))

             ((Unless (sv::svex-alist-p svex-alist)) ;; for guards
              (mv term (raise "given sv::svex-alist does not have sv::svex-alist: ~p0." svex-alist)))
             ((Unless (sv::svex-alist-no-foreign-op-p svex-alist)) ;; to convert svex-eval to eval$
              (mv term (raise "given sv::svex-alist has foreign operands: ~p0" svex-alist)))
             ((Unless (check-context-for-adder-warrants context)) ;; check for existence of warrants.
              (mv term (raise "Some necessary warrants were not found in the context: ~p0" context)))

             (config (svex-reduce-w/-env-config-1))

             (- (cw "Starting: svl::svex-alist-reduce-w/-env. ~%"))
             ;; (- (time-tracker :rewrite-adders-in-svex :end))
             ;; (- (time-tracker :rewrite-adders-in-svex :init
             ;;                  :times '(1 2 3 4 5)
             ;;                  :interval 5
             ;;                  ))
             ;; (- (time-tracker :rewrite-adders-in-svex :start!))
             (config (svl::change-svex-reduce-config
                      config :skip-bitor/and/xor-repeated t))
             (svex-alist
              (time$
               (b* ((svex-alist (svl::svexalist-convert-bitnot-to-bitxor svex-alist))
                    (svex-alist (svl::svex-alist-reduce-w/-env svex-alist :env env :config config)))
                 svex-alist)
               :msg "---- svl::svex-alist-reduce-w/-env took ~st seconds (real-time), or ~sc seconds ~
  (cpu-time), and ~sa bytes allocated.~%~%"))

             (- (acl2::sneaky-save 'orig-svex-alist svex-alist))
             ;;  (- (time-tracker :rewrite-adders-in-svex :stop))
             ;;             (- (time-tracker :rewrite-adders-in-svex :print?
             ;;                              :min-time 0
             ;;                              :msg "The total runtime of svl::svex-alist-reduce-w/-env ~
             ;; was ~st seconds."))

             (config (svl::change-svex-reduce-config
                      config
                      :skip-bitor/and/xor-repeated nil
                      :keep-missing-env-vars nil))

             (- (cw "Starting: rp::rewrite-adders-in-svex-alist. ~%"))
             (- (time-tracker :rewrite-adders-in-svex :end))
             (- (time-tracker :rewrite-adders-in-svex :init
                              :times '(1 2 3 4 5)
                              :interval 5
                              ))
             (- (time-tracker :rewrite-adders-in-svex :start!))

             (- (if (aggressive-find-adders-in-svex)
                    (cw "Aggressive mode is enabled. Disabling may reduce the time spent during adder pattern search. To disable run:~%(rp::enable-aggressive-find-adders-in-svex nil) ~%~%")
                  (cw "Warning: Aggressive mode is disabled. Enabling may help a failing proof go through. To enable run:~%(rp::enable-aggressive-find-adders-in-svex t) ~%")))

             (svex-alist (wrap-pp-with-id-alist svex-alist))
             (tstate (make-find-f/h-adders-state))

             (svex-alist (find-f/h-adders-in-svex-alist svex-alist
                                                        *find-f/h-adders-in-svex-alist-limit*
                                                        :adder-type 'fa))

             ;;(- (design_res-broken svex-alist "after-fa"))

             #|(- (cwe "resulting svexl-alist after full-adders ~p0 ~%"
             (svl::svex-alist-to-svexl-alist svex-alist)))|#

             (- (acl2::sneaky-save 'after-fa svex-alist))
             (- (cw "~%Access the svexl-alist after full-adder search:
(b* (((mv res state) (acl2::sneaky-load 'rp::after-fa state)))
   (mv state (svl::svex-alist-to-svexl-alist res))) ~%"))

             (- (time-tracker :rewrite-adders-in-svex :stop))
             (- (time-tracker :rewrite-adders-in-svex :print?
                              :min-time 0
                              :msg "Search for full adder patterns took ~st secs.~%~%"))

             (- (time-tracker :rewrite-adders-in-svex :end))
             (- (time-tracker :rewrite-adders-in-svex :init
                              :times '(1 2 3 4 5)
                              :interval 5
                              ))
             (- (time-tracker :rewrite-adders-in-svex :start!))

             ;;(svex-alist (svl::light-svex-alist-simplify-bitand/or/xor svex-alist))

             (svex-alist (find-f/h-adders-in-svex-alist svex-alist
                                                        *find-f/h-adders-in-svex-alist-limit*
                                                        :adder-type 'ha
                                                        :tstate (change-find-f/h-adders-state
                                                                 tstate
                                                                 :track-column?
                                                                 ;; it  will try
                                                                 ;; again in the
                                                                 ;; end  without
                                                                 ;; track-column?
                                                                 ;; if  it makes
                                                                 ;; 4+    parses
                                                                 ;; first.
                                                                 40 ;(+ 4 *find-f/h-adders-in-svex-alist-limit*)
                                                                 )))
             (- (acl2::sneaky-save 'after-round1 svex-alist))
             (- (cw "~%Access the svexl-alist after full-adder and half-adder search:
(b* (((mv res state) (acl2::sneaky-load 'rp::after-round1 state)))
   (mv state (svl::svex-alist-to-svexl-alist res))) ~%"))

             (- (time-tracker :rewrite-adders-in-svex :stop))
             (- (time-tracker :rewrite-adders-in-svex :print?
                              :min-time 0
                              :msg "Search for half adder patterns took ~st secs.~%~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
             ;; Final leg
             (- (time-tracker :rewrite-adders-in-svex :end))
             (- (time-tracker :rewrite-adders-in-svex :init
                              :times '(1 2 3 4 5)
                              :interval 5
                              ))
             (- (time-tracker :rewrite-adders-in-svex :start!))

             (- (cw "~%"))
             (- (cw "Now will perform global simplification, remove potentialy misidentified half-adders, perform another round of full-adder/half-adder detection, and finalize the search. ~%~%"))

             ;; (- (cw "--- Let's try to reduce number of negations~%"))
             ;; (new-svex-alist (svl::svex-alist-reduce-bit-negations svex-alist))
             ;; (- (if (hons-equal new-svex-alist svex-alist)
             ;;        (cw "-> Nothing is changed after negation reduction attempt. ~%")
             ;;      (cw "-> Could clean some number negations. ~%")))
             ;; (svex-alist new-svex-alist)

             ;; I have  seen a case (32X32_UBP_AR_VCSkA)  where simplifying before
             ;; removing ha-pairs helps.
             (svex-alist (svl::svex-alist-simplify-bitand/or/xor svex-alist :nodes-to-skip-alist nil))
             ;;(svex-alist (svl::light-svex-alist-simplify-bitand/or/xor svex-alist))
             (svex-alist (fix-order-of-fa/ha-chain-args-alist svex-alist))

             ;; this should trigger a second round because of :track-column? limitation..
             (new-svex-alist (search-and-add-ha-c-for-shifted svex-alist))

             ;;(- (design_res-broken svex-alist "before remove-ha-pairs-under-gates-alist"))

             (new-svex-alist (remove-unpaired-fa-s-alist new-svex-alist))
             ;; remove half-adders under gates..
             (new-svex-alist (remove-ha-pairs-under-gates-alist new-svex-alist))
             ;; try maybe global simplification here to clear out more clutter. Maybe this is unnecessary

             ;;(- (design_res-broken svex-alist "after remove-ha-pairs-under-gates-alist"))

             (disable-search (and*-exec (not (aggressive-find-adders-in-svex))
                                        (equal new-svex-alist svex-alist)
                                        (not (adders-under-gates?-alist new-svex-alist))))
             (- (and disable-search
                     (cw "- Agressive mode is disabled and removing adders did not change anything -> ending the search.~%")))
             (svex-alist new-svex-alist)

             ;; There's  something  off  somewhere  that calling  this  twice  was
             ;; necessary to properly clean stuff.  May have to do with inside-out
             ;; vs. outside-in simplificaiton
             (svl::nodes-to-skip-alist nil)
             (svex-alist (if disable-search svex-alist (svl::svex-alist-simplify-bitand/or/xor-outside-in svex-alist)))
             (svex-alist (if disable-search svex-alist (svl::svex-alist-simplify-bitand/or/xor svex-alist)))
             ;;(svex-alist (if disable-search svex-alist (svl::light-svex-alist-simplify-bitand/or/xor svex-alist)))
             (svex-alist (if disable-search svex-alist (fix-order-of-fa/ha-chain-args-alist svex-alist)))

             #|(- (cwe "resulting svexl-alist after removing half-adders and global simplification ~p0 ~%"
             (svl::svex-alist-to-svexl-alist svex-alist)))|#

             (tstate (change-find-f/h-adders-state tstate
                                                   :pp-id-cleaned t
                                                   :reduce-bit-negations t))
             (svex-alist (if disable-search svex-alist
                           (find-f/h-adders-in-svex-alist svex-alist
                                                          *find-f/h-adders-in-svex-alist-limit*
                                                          :adder-type 'fa
                                                          :tstate (change-find-f/h-adders-state
                                                                   tstate
                                                                   :skip-vector-adder t))))
             ((mv svex-alist not-changed?)
              (if disable-search (mv svex-alist t)
                (b* ((- (cw "---~%"))
                     (new-svex-alist (find-f/h-adders-in-svex-alist svex-alist
                                                                    *find-f/h-adders-in-svex-alist-limit*
                                                                    :adder-type 'ha
                                                                    :tstate (change-find-f/h-adders-state
                                                                             tstate
                                                                             :track-column? 20
                                                                             :skip-light-simplify t
                                                                             :skip-vector-adder t))))
                  (mv new-svex-alist (equal svex-alist new-svex-alist)))))

             ((mv svex-alist not-changed?)
              (if (or* disable-search not-changed?) (mv svex-alist t)
                (b* ((- (cw "---- ~%--- Previous half-adder search (1) made some changes. Let's look for full-adders again.~%"))
                     ;; (new-svex-alist (svl::svex-alist-simplify-bitand/or/xor svex-alist))
                     ;; (new-svex-alist (remove-ha-pairs-under-gates-alist new-svex-alist))
                     (new-svex-alist svex-alist)
                     (new-svex-alist2 (find-f/h-adders-in-svex-alist new-svex-alist
                                                                     *find-f/h-adders-in-svex-alist-limit*
                                                                     :adder-type 'fa
                                                                     :tstate (change-find-f/h-adders-state
                                                                              tstate
                                                                              ;;:skip-vector-adder t
                                                                              :only-quick-search t)))
                     ((when (equal new-svex-alist new-svex-alist2))
                      (mv svex-alist t)))
                  (mv new-svex-alist2 nil))))

             ((mv svex-alist not-changed?)
              (if (or* disable-search not-changed?) (mv svex-alist t)
                (b* ((- (cw "---- ~%--- Previous full-adder search (2) made some changes. Let's look for half-adders again.~%"))
                     (new-svex-alist (find-f/h-adders-in-svex-alist svex-alist
                                                                    *find-f/h-adders-in-svex-alist-limit*
                                                                    :adder-type 'ha
                                                                    :tstate (change-find-f/h-adders-state
                                                                             tstate
                                                                             :track-column? 10
                                                                             :skip-light-simplify t
                                                                             :skip-vector-adder t))))
                  (mv new-svex-alist (equal svex-alist new-svex-alist)))))

             ((mv svex-alist ?not-changed?)
              (if (or* disable-search not-changed?) (mv svex-alist t)
                (b* ((- (cw "---- ~%--- Previous half-adder search (3) made some changes. Let's look for full-adders again.~%"))
                     (new-svex-alist (find-f/h-adders-in-svex-alist svex-alist
                                                                    *find-f/h-adders-in-svex-alist-limit*
                                                                    :adder-type 'fa)))
                  (mv new-svex-alist (equal svex-alist new-svex-alist)))))

             ((mv svex-alist ?not-changed?)
              (if (or* disable-search not-changed?) (mv svex-alist t)
                (b* ((- (cw "---- ~%--- Previous full-adder search (4) made some changes. Let's look for half-adders again.~%"))
                     (new-svex-alist (find-f/h-adders-in-svex-alist svex-alist
                                                                    *find-f/h-adders-in-svex-alist-limit*
                                                                    :adder-type 'ha
                                                                    :tstate (change-find-f/h-adders-state
                                                                             tstate
                                                                             :track-column? 5
                                                                             :skip-vector-adder t))))
                  (mv new-svex-alist (equal svex-alist new-svex-alist)))))

             (- (acl2::sneaky-save 'after-round2 svex-alist))
             (- (cw "~%Access the svexl-alist after the second round of full-adder and half-adder search:
(b* (((mv res state) (acl2::sneaky-load 'rp::after-round2 state)))
   (mv state (svl::svex-alist-to-svexl-alist res))) ~%"))

             (svex-alist (if disable-search svex-alist
                           (svl::svex-alist-simplify-bitand/or/xor svex-alist)))
             ;; prob unnecessary

             (svex-alist (if disable-search svex-alist
                           (remove-ha-pairs-under-gates-alist svex-alist :wrap-with-id t)))
             (svex-alist (if disable-search svex-alist
                           (remove-unpaired-fa-s-alist svex-alist)))
             ;; (svex-alist (if disable-search svex-alist
             ;;               (svl::svex-alist-simplify-bitand/or/xor svex-alist))) ;; prob unnecessary

             ;; to be enabled manually to make s-c-spec-meta work faster. but left
             ;; disabled by default because debugging becomes difficult with this.
             (svex-alist (if (merge-fa-chains)
                             (merge-fa-s-c-chains-alist svex-alist)
                           svex-alist))

             ;; clean up partsels around plus'es and convert them to the int-vector-adder function.
             (svex-alist (remove-partsels-around-plus-alist svex-alist))

             (- (time-tracker :rewrite-adders-in-svex :stop))
             (- (time-tracker :rewrite-adders-in-svex :print?
                              :min-time 0
                              :msg "Final round of searching for adders took ~st secs.~%~%"))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

             (- (cw "Finished: rp::rewrite-adders-in-svex-alist.~%"))

             (- (cw "Starting: svl::svex-alist-to-svexl-alist ~%"))
             (svexl-alist (svl::svex-alist-to-svexl-alist svex-alist))
             (- (let ((x (svl::svexl-alist->node-array svexl-alist))) ;; for guards
                  (cw "Finished: svl::svex-alist-to-svexl-alist. Resulting svexl-alist has ~p0 nodes.~%~%" (len x))))

             (- (missed-adder-warning svexl-alist))

             ;;(- (cwe "resulting svexl-alist: ~p0 ~%" svexl-alist))
             (- (acl2::sneaky-save 'after-all svexl-alist))
             (- (cw "Access the resulting svexl-alist:~%(acl2::sneaky-load 'rp::after-all state)~%"))

             (- (clear-memoize-table 'replace-adder-patterns-in-svex))

             (& (hons-clear t))
             )
          (mv `(svl::svexl-alist-eval$ ',svexl-alist ,env-orig)
              `(nil t t))))
       (& (mv term nil)))
     :mintime 1/8
     :msg "~%---- Preprocessing SVEXes and Finding adders took ~st seconds (real-time), or ~sc seconds ~
  (cpu-time), and ~sa bytes allocated.~%~%")
    ///

    (local
     (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

    (local
     (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

    (local
     (defthm is-rp-of-others
       (implies (not (equal (car term) 'rp))
                (not (is-rp term)))
       :hints (("Goal"
                :in-theory (e/d (is-rp) ())))))

    (local
     (defthm is-equals-of-others
       (implies (not (equal (car term) 'equals))
                (not (is-equals term )))
       :hints (("Goal"
                :in-theory (e/d (is-equals) ())))))

    (local
     (defthm is-if-of-others
       (implies (not (equal (car term) 'if))
                (not (is-if term)))
       :hints (("Goal"
                :in-theory (e/d (is-if) ())))))

    (local
     (create-regular-eval-lemma sv::svex-alist-eval 2  find-adders-in-svex-formula-checks))

    (local
     (create-regular-eval-lemma svl::svexl-alist-eval$ 2 find-adders-in-svex-formula-checks))

    (local
     (create-regular-eval-lemma make-fast-alist 1 find-adders-in-svex-formula-checks))

    (local
     (defthm rp-evlt-of-quoted
       (equal (rp-evlt (list 'quote x) a)
              x)))

    (local
     (defthmd rp-evlt-of-ex-from-rp-reverse
       (implies (syntaxp (equal term 'term))
                (equal (rp-evlt (caddr term) a)
                       (rp-evlt (ex-from-rp (caddr term)) a)))))

    (local
     (defthm dummy-lemma-
       (implies (consp (ex-from-rp term))
                (consp term))
       :rule-classes :forward-chaining))

    (local
     (defthm dummy-lemma-2
       (implies (equal (car (ex-from-rp term)) 'falist)
                (not (equal (car term) 'quote)))
       :rule-classes :forward-chaining))

    (local
     (defthm dummy-lemma-3
       (implies (and (rp-termp x)
                     (case-match x
                       (('falist ('quote &) &) t)))
                (falist-consistent-aux (cadr (cadr x))
                                       (caddr x)))
       :hints (("goal"
                :expand ((rp-termp x))
                :in-theory (e/d (rp-termp falist-consistent)
                                ())))))

    (local
     (defthm rp-evlt-of-falist
       (implies (and (rp-termp x)
                     (equal (car x) 'falist))
                (equal (rp-evlt x a)
                       (rp-evlt (caddr x) a)))
       :hints (("goal"
                :expand ((rp-termp x))
                :in-theory (e/d (rp-termp falist-consistent)
                                ())))))

    (defret <fn>-is-correct
      (and (implies (and (rp::rp-term-listp context)
                         (rp-termp term)
                         (valid-sc term a)
                         (rp::eval-and-all context a)
                         (rp-evl-meta-extract-global-facts)
                         (find-adders-in-svex-formula-checks state))
                    (and (equal (rp-evlt res-term a)
                                (rp-evlt term a))
                         (valid-sc res-term a)))
           (implies (and (rp::rp-term-listp context)
                         (rp-termp term))
                    (rp-termp res-term)))
      :fn rewrite-adders-in-svex-alist
      :hints (("goal"
               :case-split-limitations (1 2)
               :expand ((rp-termp term)
                        (:free (fn args)
                               (valid-sc (cons fn args) a))
                        (rp-term-listp (cdr term))
                        (rp-term-listp (cddr term)))
               :in-theory (e/d* (or*
                                 rp-term-listp
                                 rp-evlt-of-ex-from-rp-reverse
                                 regular-eval-lemmas-with-ex-from-rp
                                 regular-eval-lemmas
                                 ;;is-rp
                                 ;;falist-consistent
                                 ;;is-if
                                 svl::svexl-alist-eval$-correct-reverse)
                                (rp-evlt-of-ex-from-rp
                                 rp-trans-is-term-when-list-is-absent
                                 ex-from-rp
                                 is-rp
                                 rp-evl-of-variable
                                 rp-trans
                                 ;;rp::rp-term-listp
                                 rp::falist-consistent-aux
                                 rp::eval-and-all
                                 valid-sc)))))

    (profile 'rewrite-adders-in-svex-alist)))

(rp::add-meta-rule
 :meta-fnc rewrite-adders-in-svex-alist
 :trig-fnc sv::svex-alist-eval
 :formula-checks find-adders-in-svex-formula-checks
 :valid-syntaxp t
 :returns (mv term dont-rw)
 :disabled t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection apply$-of-adder-fncs-meta

  (define apply$-of-adder-fncs-meta-aux (args-term)
    :returns (mv (res-args rp-term-listp :hyp (rp-termp args-term))
                 all-bitp
                 valid)
    (case-match args-term
      (('cons x rest)
       (b* ((x-has-bitp (or (has-bitp-rp x)
                            (binary-fnc-p x)
                            (and (quotep x)
                                 (consp (cdr x))
                                 (bitp (unquote x)))))
            ((mv rest bitp valid)
             (apply$-of-adder-fncs-meta-aux rest)))
         (mv (cons x rest)
             (and x-has-bitp bitp)
             valid)))
      (('quote (x . rest))
       (b* ((x-has-bitp (bitp x))
            ((mv rest bitp valid)
             (apply$-of-adder-fncs-meta-aux (list 'quote rest))))
         (mv (cons `',x rest)
             (and x-has-bitp bitp)
             valid)))
      (''nil
       (mv nil t t))
      (& (mv nil nil nil)))
    ///
    (defretd <fn>-is-correct
      (implies valid
               (equal (rp-evlt args-term a)
                      (rp-evlt-lst res-args a))))
    (defret <fn>-is-valid-sc
      (implies (and valid
                    (valid-sc args-term a))
               (valid-sc-subterms res-args a))
      :hints (("goal"
               :in-theory (e/d (is-rp is-if is-equals) ()))))

    (defret true-listp-of-<fn>
      (true-listp res-args))

    (local
     (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

    (local
     (defthm has-bitp-rp-implies
       (implies (and (has-bitp-rp term)
                     (valid-sc term a))
                (and (bitp (rp-evlt term a))))
       :hints (("goal"

                :in-theory (e/d (valid-sc-single-step
                                 has-bitp-rp
                                 is-rp)
                                (bitp))))))
    (local
     (with-output
       :off :all
       :on (error)
       (progn
         (create-regular-eval-lemma binary-or 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma binary-and 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma binary-xor 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma binary-not 1 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma binary-? 3 find-adders-in-svex-formula-checks)
         )))

    (local
     (defthm binary-fnc-p-implies
       (implies (and (binary-fnc-p term)
                     (rp-evl-meta-extract-global-facts)
                     (find-adders-in-svex-formula-checks state))
                (and (bitp (rp-evlt term a))))
       :hints (("goal"

                :in-theory (e/d* (regular-eval-lemmas
                                  binary-fnc-p)
                                 (bitp))))))

    (defret <fn>-is-all-bitp
      (implies (and all-bitp
                    valid
                    (valid-sc args-term a)
                    (rp-evl-meta-extract-global-facts)
                    (find-adders-in-svex-formula-checks state))
               (and (bit-listp (rp-evlt args-term a))
                    (bit-listp (rp-evlt-lst res-args a))))
      :rule-classes (:rewrite :forward-chaining)
      :hints (("goal"
               :in-theory (e/d (bit-listp
                                is-rp
                                is-if
                                is-equals)
                               ())))))

  ;; (apply$-of-adder-fncs-meta-aux `(cons (rp 'bitp x) (cons '1 (cons (rp 'bitp y) '(1)))))
  ;; = (((rp 'bitp x) '1 (rp 'bitp y) '1) t t)

  (define apply$-of-adder-fncs-meta (term
                                     (context true-listp))
    :returns (mv (res rp-termp :hyp (rp-termp term)
                      :hints (("goal"
                               :expand ((:free (rest) (is-rp (cons 'rp rest))))
                               :use ((:instance rp-term-listp-of-apply$-of-adder-fncs-meta-aux.res-args
                                                (args-term (cadr (caddr term)))))
                               :in-theory (e/d (rp-term-listp)
                                               (rp-term-listp-of-apply$-of-adder-fncs-meta-aux.res-args)))))
                 dont-rw)
    (case-match term
      (('apply$ ('quote fnc) ('svl::4veclist-fix-wog args))
       (b* (((unless (member-equal fnc *adder-fncs*))
             (mv term nil))
            (warrant `(,(intern-in-package-of-symbol
                         (str::cat "APPLY$-WARRANT-" (symbol-name fnc))
                         fnc)))
            ((unless (member-equal warrant context))
             (mv term (raise "a necessary warrant is not found in the context: ~p0 ~%" warrant)))
            ((mv args-lst all-bitp valid)
             (apply$-of-adder-fncs-meta-aux args))
            ((unless valid)
             (mv term (raise "apply$-of-adder-fncs-meta-aux did not return valid. args: ~p0 ~%" args)))

            ((when (and* all-bitp
                         (or* (eq fnc 'ha-c-chain)
                              (eq fnc 'ha-s-chain))
                         (svl::equal-len args-lst 2)))
             (case fnc
               (ha-s-chain
                (mv `(rp 'bitp (equals (s-spec (cons ,(car args-lst)
                                                     (cons ,(cadr args-lst)
                                                           'nil)))
                                       (binary-xor ,(car args-lst)
                                                   ,(cadr args-lst))))
                    `(rp 'bitp (equals (s-spec (cons t (cons t 'nil)))
                                       (binary-xor t t)))))
               (ha-c-chain
                (mv `(rp 'bitp (equals (c-spec (cons ,(car args-lst)
                                                     (cons ,(cadr args-lst)
                                                           'nil)))
                                       (binary-and ,(car args-lst)
                                                   ,(cadr args-lst))))
                    `(rp 'bitp (equals (c-spec (cons t (cons t 'nil)))
                                       (binary-and t t)))))
               (t (mv term nil)))))
         (cond
          ((and* (eq fnc 'fa-c-chain)
                 (svl::equal-len args-lst 4))
           (mv `(,fnc (svl::4vec-fix-wog ,(first args-lst))
                      ,(second args-lst)
                      ,(third args-lst)
                      ,(fourth args-lst))
               `(nil (nil t) t t t)))
          ((and* (eq fnc 'ha+1-s-chain)
                 (svl::equal-len args-lst 3))
           (mv `(,fnc (svl::4vec-fix-wog ,(first args-lst))
                      ,(second args-lst)
                      ,(third args-lst))
               `(nil (nil t) t t)))
          ((and* (or (eq fnc 'fa-s-chain)
                     (eq fnc 'full-adder))
                 (svl::equal-len args-lst 3))
           (mv `(,fnc ,(first args-lst)
                      ,(second args-lst)
                      ,(third args-lst))
               `(nil t t t)))
          ((and* (svl::equal-len args-lst 2)
                 (or (eq fnc 'ha-c-chain)
                     (eq fnc 'ha+1-c-chain)
                     (eq fnc 'ha-s-chain)
                     (eq fnc 'half-adder)
                     (eq fnc 'int-vector-adder)))
           (mv `(,fnc ,(first args-lst)
                      ,(second args-lst))
               `(nil t t t)))
          (t (mv term nil)))))
      (& (mv term nil)))

    ///

    (local
     (with-output
       :off :all
       :on (error)
       (progn
         (create-regular-eval-lemma rp 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma c-spec 1 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma bitp 1 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma equals 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma cons 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma s-spec 1 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma ha-s-chain 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma binary-xor 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma binary-and 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma ha+1-s-chain 3 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma fa-s-chain 3 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma full-adder 3 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma half-adder 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma int-vector-adder 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma ha+1-c-chain 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma fa-c-chain 4 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma ha-c-chain 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma apply$ 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma svl::4veclist-fix-wog 1 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma svl::4vec-fix-wog 1 find-adders-in-svex-formula-checks))))

    (local
     (defthm rp-evlt-of-quoted
       (implies (and (equal (car x) 'quote))
                (equal (rp-evlt x a)
                       (cadr x)))))

    (local
     (defthm 4vec-bitxor-or-dont-care
       (and (equal (sv::4vec-bitxor '(-1 . 0) x)
                   '(-1 . 0))
            (equal (sv::4vec-bitxor x '(-1 . 0))
                   '(-1 . 0)))
       :hints (("goal"
                :in-theory (e/d (sv::4vec-bitxor) ())))))

    #|(local
    (defthm 4vec-bitand-or-dont-care
    (and (equal (sv::4vec-bitand '(-1 . 0) x)
    '(-1 . 0))
    (equal (sv::4vec-bitand x '(-1 . 0))
    '(-1 . 0)))
    :hints (("goal"
    :in-theory (e/d (sv::4vec-bitand) ())))))|#

    ;; (local
    ;;  (defthm rp-evlt-lst-of-cdr
    ;;    (equal (rp-evlt-lst (cdr x) a)
    ;;           (cdr (rp-evlt-lst x a)))))

    (local
     (defthm rp-evlt-lst-when-atom-and-cddr
       (implies (consp (cdr x))
                (equal (car (rp-evlt-lst (cddr x) a))
                       (rp-evlt (caddr x) a)))))

    (local
     (defthm rp-evlt-lst-when-atom-and-cdr
       (implies (consp x)
                (equal (car (rp-evlt-lst (cdr x) a))
                       (rp-evlt (cadr x) a)))))

    (local
     (defthm consp-of-rp-evlt-lst
       (equal (consp (rp-evlt-lst lst a))
              (consp lst))
       :hints (("goal"
                :induct (len lst)
                :in-theory (e/d (rp-trans-lst) ())))))

    (local
     (defthm HA+1-C-CHAIN-of-4vec-fix
       (and (equal (HA+1-C-CHAIN (sv::4vec-fix x) y)
                   (HA+1-C-CHAIN x y))
            (equal (HA+1-C-CHAIN x (sv::4vec-fix y))
                   (HA+1-C-CHAIN x y)))
       :hints (("Goal"
                :in-theory (e/d (HA+1-C-CHAIN) ())))))

    (local
     (defthm HA-C-CHAIN-of-4vec-fix
       (and (equal (HA-C-CHAIN (sv::4vec-fix x) y)
                   (HA-C-CHAIN x y))
            (equal (HA-C-CHAIN x (sv::4vec-fix y))
                   (HA-C-CHAIN x y)))
       :hints (("Goal"
                :in-theory (e/d (HA-C-CHAIN) ())))))

    (local
     (defthm FA-C-CHAIN-of-4vec-fix
       (and (equal (fa-c-chain m (sv::4vec-fix x) y z)
                   (fa-c-chain m x y z))
            (equal (fa-c-chain m x (sv::4vec-fix y) z)
                   (fa-c-chain m x y z))
            (equal (fa-c-chain m x y (sv::4vec-fix z))
                   (fa-c-chain m x y z)))
       :hints (("Goal"
                :in-theory (e/d (fa-c-chain) ())))))

    (local
     (defthm FA-s-CHAIN-of-4vec-fix
       (and (equal (fa-s-chain (sv::4vec-fix x) y z)
                   (fa-s-chain x y z))
            (equal (fa-s-chain x (sv::4vec-fix y) z)
                   (fa-s-chain x y z))
            (equal (fa-s-chain x y (sv::4vec-fix z))
                   (fa-s-chain x y z)))
       :hints (("Goal"
                :in-theory (e/d (fa-s-chain) ())))))

    (local
     (defthm full-adder-of-4vec-fix
       (and (equal (full-adder (sv::4vec-fix x) y z)
                   (full-adder x y z))
            (equal (full-adder x (sv::4vec-fix y) z)
                   (full-adder x y z))
            (equal (full-adder x y (sv::4vec-fix z))
                   (full-adder x y z)))
       :hints (("Goal"
                :in-theory (e/d (full-adder) ())))))

    (local
     (defthm half-adder-of-4vec-fix
       (and (equal (half-adder (sv::4vec-fix x) y)
                   (half-adder x y))
            (equal (half-adder x (sv::4vec-fix y))
                   (half-adder x y)))
       :hints (("Goal"
                :in-theory (e/d (half-adder) ())))))

    (local
     (defthm int-vector-adder-of-4vec-fix
       (and (equal (int-vector-adder (sv::4vec-fix x) y)
                   (int-vector-adder x y))
            (equal (int-vector-adder x (sv::4vec-fix y))
                   (int-vector-adder x y)))
       :hints (("Goal"
                :in-theory (e/d (sv::4vec-fix
                                 SV::4VEC
                                 ifix
                                 int-vector-adder)
                                ())))))

    (local
     (defthm ha+1-s-CHAIN-of-4vec-fix
       (and (equal (ha+1-s-chain m (sv::4vec-fix x) y)
                   (ha+1-s-chain m x y))
            (equal (ha+1-s-chain m x (sv::4vec-fix y))
                   (ha+1-s-chain m x y)))
       :hints (("Goal"
                :in-theory (e/d (ha+1-s-chain) ())))))

    (local
     (defthm ha-s-CHAIN-of-4vec-fix
       (and (equal (ha-s-chain (sv::4vec-fix x) y)
                   (ha-s-chain x y))
            (equal (ha-s-chain x (sv::4vec-fix y))
                   (ha-s-chain x y)))
       :hints (("Goal"
                :in-theory (e/d (ha-s-chain) ())))))

    (local
     (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

    (local
     (defthm member-equal-and-eval-and-all
       (implies (and (eval-and-all context a)
                     (member-equal x context))
                (and (rp-evlt x a)
                     (implies (force (not (include-fnc x 'list)))
                              (rp-evl x a))))
       :rule-classes (:rewrite)))

    (local
     (defthm valid-sc-of-car-when-valid-sc-subterms
       (implies (and (consp lst)
                     (valid-sc-subterms lst a))
                (valid-sc (car lst) a))))

    (local
     (defthm VALID-SC-SUBTERMS-of-cdr
       (implies (VALID-SC-SUBTERMS lst a)
                (VALID-SC-SUBTERMS (cdr lst) a))))

    (local
     (defthmd s-spec-when-bit-listp
       (implies (and (svl::equal-len x 2)
                     (bit-listp (rp-evlt-lst x a)))
                (equal (s-spec (list (rp-evlt (car x) a)
                                     (rp-evlt (cadr x) a)))
                       (binary-xor (rp-evlt (car x) a)
                                   (rp-evlt (cadr x) a))))
       :hints (("Goal"
                :do-not-induct t
                :in-theory (e/d (BIT-LISTP bitp) ())))))

    (local
     (defthmd ha-c-chain-when-bit-listp
       (implies (and (svl::equal-len x 2)
                     (bit-listp (rp-evlt-lst x a)))
                (equal (HA-C-CHAIN (rp-evlt (car x) a)
                                   (rp-evlt (cadr x) a))
                       (binary-and (rp-evlt (car x) a)
                                   (rp-evlt (cadr x) a))))
       :hints (("Goal"
                :do-not-induct t
                :in-theory (e/d (BIT-LISTP bitp) ())))))

    (local
     (defthmd ha-s-chain-when-bit-listp
       (implies (and (svl::equal-len x 2)
                     (bit-listp (rp-evlt-lst x a)))
                (equal (HA-s-CHAIN (rp-evlt (car x) a)
                                   (rp-evlt (cadr x) a))
                       (binary-xor (rp-evlt (car x) a)
                                   (rp-evlt (cadr x) a))))
       :hints (("Goal"
                :do-not-induct t
                :in-theory (e/d (BIT-LISTP bitp) ())))))

    (local
     (defthmd c-spec-when-bit-listp
       (implies (and (svl::equal-len x 2)
                     (bit-listp (rp-evlt-lst x a)))
                (equal (c-spec (list (rp-evlt (car x) a)
                                     (rp-evlt (cadr x) a)))
                       (binary-and (rp-evlt (car x) a)
                                   (rp-evlt (cadr x) a))))
       :hints (("Goal"
                :do-not-induct t
                :in-theory (e/d (BIT-LISTP bitp) ())))))

    (defret <fn>-is-valid-sc
      (and (implies (and (rp::rp-term-listp context)
                         (rp-termp term)
                         (valid-sc term a)
                         (rp-evl-meta-extract-global-facts)
                         (find-adders-in-svex-formula-checks state))
                    (valid-sc res a)))
      :fn apply$-of-adder-fncs-meta
      :hints (("Goal"
               :do-not-induct t
               :expand ((:free (x y a)
                               (eval-and-all (cons x y) a))
                        (:free (x y a)
                               (CONTEXT-FROM-RP (cons 'rp y) a))
                        (:free (x y a)
                               (ex-from-rp (cons 'rp y)))
                        (:free (x y a)
                               (ex-from-rp (cons 'equals y)))
                        (:free (x y a)
                               (CONTEXT-FROM-RP (cons 'equals y) a)))
               :in-theory (e/d* (s-spec-when-bit-listp
                                 c-spec-when-bit-listp
                                 apply$-of-adder-fncs-meta-aux-is-all-bitp
                                 ;;CONTEXT-FROM-RP
                                 regular-eval-lemmas
                                 regular-eval-lemmas-with-ex-from-rp
                                 is-rp is-if is-equals)
                                ((:REWRITE DEFAULT-CDR)
                                 (:REWRITE
                                  RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT)
                                 (:REWRITE
                                  ACL2::SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP)
                                 (:REWRITE VALID-SC-CADR)
                                 (:DEFINITION EX-FROM-RP)
                                 (:DEFINITION MEMBER-EQUAL)
                                 (:REWRITE NTH-0-CONS)
                                 (:REWRITE NTH-ADD1)
                                 len
                                 RP-EVLT-LST-OF-CONS
                                 bit-listp
                                 (:rewrite str::coerce-to-list-removal)
                                 (:rewrite str::coerce-to-string-removal)
                                 (:DEFINITION STR::FAST-STRING-APPEND)
                                 ;;(:DEFINITION RP-TRANS-LST)
                                 (:DEFINITION STRING-APPEND)
                                 ;;rp-trans-lst
                                 rp-trans
                                 rp-termp
                                 eval-and-all
                                 svl::4veclist-fix-wog-is-4veclist-fix
                                 rp-trans)))
              (and stable-under-simplificationp
                   '(:use ((:instance apply$-of-adder-fncs-meta-aux-is-all-bitp
                                      (args-term (cadr (caddr term)))
                                      ))))
              ))

    (defret <fn>-is-correct
      (and (implies (and (rp::rp-term-listp context)
                         (rp-termp term)
                         (valid-sc term ACL2::UNBOUND-FREE-ENV)
                         (rp::eval-and-all context ACL2::UNBOUND-FREE-ENV)
                         (rp-evl-meta-extract-global-facts)
                         (find-adders-in-svex-formula-checks state))
                    (and (equal (rp-evlt res ACL2::UNBOUND-FREE-ENV)
                                (rp-evlt term ACL2::UNBOUND-FREE-ENV))
                         #|(valid-sc res a)|#)))
      :fn apply$-of-adder-fncs-meta
      :hints (("Goal"
               :expand ((:free (x y)
                               (svl::4veclist-fix-wog (cons x y)))
                        (:free (a)
                               (svl::4veclist-fix-wog
                                (rp-evlt-lst
                                 (cddr (mv-nth 0
                                               (apply$-of-adder-fncs-meta-aux (cadr (caddr term)))))
                                 a)))
                        (:free (a)(svl::4veclist-fix-wog
                                   (rp-evlt-lst
                                    (cdr (mv-nth 0
                                                 (apply$-of-adder-fncs-meta-aux (cadr (caddr term)))))
                                    a)))
                        (:free (a)(svl::4veclist-fix-wog
                                   (cdr
                                    (rp-evlt-lst
                                     (cddr (mv-nth 0
                                                   (apply$-of-adder-fncs-meta-aux (cadr (caddr term)))))
                                     a))))
                        (:free (a)
                               (svl::4veclist-fix-wog
                                (rp-evlt-lst
                                 (cdddr (mv-nth 0
                                                (apply$-of-adder-fncs-meta-aux (cadr (caddr term)))))
                                 a))))
               :in-theory (e/d* (s-spec-when-bit-listp
                                 c-spec-when-bit-listp
                                 ha-s-chain-when-bit-listp
                                 ha-c-chain-when-bit-listp
                                 apply$-of-adder-fncs-meta-aux-is-correct
                                 ;;FA-S-CHAIN
                                 ;;HA+1-C-CHAIN
                                 ;;fA-c-CHAIN
                                 regular-eval-lemmas
                                 regular-eval-lemmas-with-ex-from-rp)
                                (rp-evlt-lst-of-cons
                                 (:rewrite str::coerce-to-list-removal)
                                 (:rewrite str::coerce-to-string-removal)
                                 (:definition str::fast-string-append)
                                 ;;(:definition rp-trans-lst)
                                 (:definition string-append)
                                 (:definition valid-sc)
                                 (:definition valid-sc-subterms)
                                 ;;rp-trans-lst

                                 rp-termp
                                 eval-and-all
                                 svl::4veclist-fix-wog-is-4veclist-fix
                                 rp-trans)))
              (and stable-under-simplificationp
                   '(:use ((:instance apply$-of-adder-fncs-meta-aux-is-all-bitp
                                      (args-term (cadr (caddr term)))
                                      (a acl2::unbound-free-env)))))))

    (rp::disable-rules '(svl::4veclist-fix-wog
                         sv::4veclist-fix
                         svl::4veclist-fix-wog-is-4veclist-fix))

    (profile 'apply$-of-adder-fncs-meta)
    )

  (rp::add-meta-rule
   :meta-fnc apply$-of-adder-fncs-meta
   :trig-fnc apply$
   :formula-checks find-adders-in-svex-formula-checks
   :valid-syntaxp t
   :returns (mv term dont-rw)))
