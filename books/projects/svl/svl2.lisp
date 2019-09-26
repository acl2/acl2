; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2019 Centaur Technology
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
; Original author: Mertcan Temel <mert@utexas.edu>

(in-package "SVL")

(include-book "svl2-flatten")
(include-book "svl")

(progn
  (define svl2-get-module-rank ((modname sv::modname-p)
                                (modules svl2-module-alist-p))
    :returns (res natp)
    (b* ((module (assoc-equal modname modules)))
      (if module
          (nfix (svl2-module->rank (cdr module)))
        0)))

  (define svl2-get-max-occ-rank ((occs svl2-occ-alist-p)
                                 (modules svl2-module-alist-p))
    :returns (res natp)
    (cond ((atom occs)
           0)
          ((equal (svl2-occ-kind (cdar occs)) ':assign)
           (svl2-get-max-occ-rank (cdr occs)
                                  modules))
          (t (max (svl2-get-module-rank (svl2-occ-module->name (cdar occs)) modules)
                  (svl2-get-max-occ-rank (cdr occs) modules)))))

  (define svl2-well-ranked-module ((modname sv::modname-p)
                                   (modules svl2-module-alist-p))
    (and (assoc-equal modname modules) 
         (> (svl2-get-module-rank modname modules)
            (svl2-get-max-occ-rank (svl2-module->occs
                                    (cdr (assoc-equal modname modules)))
                                   modules)))))

(define svl2-start-env ((wires wire-list-p)
                        (vals sv::4veclist-p))
  :returns (res sv::svex-env-p
                :hyp (and (wire-list-p wires)
                          (sv::4veclist-p vals)))
  (if (or (atom wires)
          (atom vals))
      nil
    (hons-acons
     (wire-name (car wires))
     (b* ((wire (car wires)))
       (case-match wire
         ((& size . start)
          (4vec-part-select start size (car vals)))
         (& (car vals))))
     (svl2-start-env (cdr wires) (cdr vals)))))

(define entry-4vec-fix (entry)
  :guard (or (consp entry)
             (not entry))
  :enabled t
  (if entry
      (cdr entry)
    (sv::4vec-x)))

(define entry-svl-env-fix (entry)
  :guard (or (consp entry)
             (not entry))
  :enabled t
  (if entry
      (cdr entry)
    (make-svl-env)))

(define svl2-retrieve-values ((wires wire-list-p)
                              (env-wires sv::svex-env-p))
  :returns (res sv::4veclist-p :hyp (and (wire-list-p wires)
                                         (sv::svex-env-p env-wires)))
  (if (atom wires)
      nil
    (b* ((wire (car wires))
         (value (hons-get (wire-name wire) env-wires)))
      (cons (case-match wire
              ((& w . s)
               (4vec-part-select s w (entry-4vec-fix value)))
              (& (entry-4vec-fix value)))
            (svl2-retrieve-values (cdr wires)
                                  env-wires)))))

#|(define save-lhs-to-env-wires ((val sv::4vec-p)
                               (lhs sv::lhs-p)
                               (env-wires sv::svex-env-p))
  :returns (res sv::svex-env-p
                :hyp (and (sv::4vec-p val)
                          (sv::lhs-p lhs)
                          (sv::svex-env-p env-wires)))
  :verify-guards nil
  (if (atom lhs)
      env-wires
    (b* (((sv::lhrange range) (car lhs))
         (env-wires (save-lhs-to-env-wires (4vec-rsh range.w val)
                                           (cdr lhs)
                                           env-wires))
         ((when (equal (sv::lhatom-kind range.atom) ':z))
          env-wires)
         (old-val (Hons-get (sv::lhatom-var->name range.atom) env-wires)))
      (hons-acons (sv::lhatom-var->name range.atom)
                  (if old-val
                      (sbits (sv::lhatom-var->rsh range.atom)
                             range.w
                             val
                             (cdr old-val))
                    (sbits (sv::lhatom-var->rsh range.atom)
                           range.w
                           val
                           (sv::4vec-x)))
                  env-wires)))
  ///
  (verify-guards save-lhs-to-env-wires))||#





(define svl2-save-mod-outputs ((vals sv::4veclist-p)
                               (wire-list-list wire-list-listp)
                               (env-wires sv::svex-env-p))
  :returns (res sv::svex-env-p
                :hyp (and (sv::4veclist-p vals)
                          (wire-list-listp wire-list-list)
                          (sv::svex-env-p env-wires )))
  (if (or (atom vals)
          (atom wire-list-list))
      env-wires
    (b* ((cur-wire-list (car wire-list-list))
         (cur-val (car vals))
         (env-wires (save-wires-to-env-wires cur-val
                                             cur-wire-list
                                             env-wires)))
      (svl2-save-mod-outputs (cdr vals)
                             (cdr wire-list-list)
                             env-wires))))

(memoize 'svl2-module-alist-p)
(memoize 'svl2-well-ranked-module)

(acl2::defines
 svl2-run-cycle
 (define svl2-run-cycle ((modname sv::modname-p)
                         (inputs sv::4veclist-p)
                         (delayed-env svl-env-p)
                         (modules svl2-module-alist-p))
   :verify-guards nil

   ;; :guard (and (assoc-equal modname modules)
   ;;             (svl2-well-ranked-module modname modules))

   :measure (acl2::nat-list-measure
             (list (svl2-get-module-rank modname modules)
                   (cons-count (sv::modname-fix modname))))
   :hints (("Goal"
            :in-theory (e/d (rp::measure-lemmas
                             SVL2-GET-MAX-OCC-RANK
                             SVL2-MODULE->OCCS
                             SV::MODNAME-FIX
                             SVL2-WELL-RANKED-MODULE
                             svl2-occ-module->name) ())))

   :returns (mv (out-vals sv::4veclist-p
                          :hyp (and (sv::4veclist-p inputs)
                                    (svl-env-p delayed-env)
                                    (svl2-module-alist-p modules)))
                (next-delayed-env svl-env-p
                                  :hyp (and (sv::4veclist-p inputs)
                                            (svl-env-p delayed-env)
                                            (svl2-module-alist-p modules))))
   (cond ((not (svl2-well-ranked-module modname modules)) ;; for termination
          (mv
           (cw "Either Module ~p0 is missing or it has invalid ranks~%"
               modname)
           (make-svl-env)))
         (t
          (b* (((svl2-module module) (cdr (assoc-equal modname modules)))
               (env-wires (svl2-start-env module.inputs inputs))
               (env-wires
                (svl-run-add-delayed-ins env-wires delayed-env
                                         module.delayed-inputs))
               ((mv env-wires next-delayed-env.modules)
                (svl2-run-cycle-occs module.occs
                                     env-wires
                                     (svl-env->modules delayed-env)
                                     modules))
               (out-vals (svl2-retrieve-values module.outputs
                                               env-wires))
               (next-delayed-env (make-svl-env
                                  :wires (hons-gets-fast-alist
                                          module.delayed-inputs
                                          env-wires)
                                  :modules next-delayed-env.modules))
               (- (fast-alist-free env-wires)))
            (mv out-vals
                next-delayed-env)))))

 (define svl2-run-cycle-occs ((occs svl2-occ-alist-p)
                              (env-wires sv::svex-env-p)
                              (delayed-env-alist svl-env-alist-p)
                              (modules svl2-module-alist-p))
   :measure (acl2::nat-list-measure
             (list (svl2-get-max-occ-rank occs modules)
                   (cons-count occs)))

   :returns (mv (res-env-wires sv::svex-env-p :hyp (and (svl2-occ-alist-p occs)
                                                        (sv::svex-env-p env-wires)
                                                        (svl-env-alist-p delayed-env-alist)
                                                        (svl2-module-alist-p modules)))
                (next-delayed-env.modules SVL-ENV-ALIST-P
                                          :hyp (and (svl2-occ-alist-p occs)
                                                    (sv::svex-env-p env-wires)
                                                    (svl-env-alist-p delayed-env-alist)
                                                    (svl2-module-alist-p modules))))

   (let ((occ-name (caar occs))
         (occ (cdar occs)))
     (cond ((atom occs)
            (mv env-wires nil))
           ((equal (svl2-occ-kind occ) ':assign)
            (b* ((env-wires (hons-acons (svl2-occ-assign->output occ)
                                        (svex-eval (svl2-occ-assign->svex occ)
                                                        env-wires)
                                        env-wires)))
              (svl2-run-cycle-occs (cdr occs)
                                   env-wires
                                   delayed-env-alist
                                   modules)))
           (t (b* ((mod-input-vals (sv::svexlist-eval (svl2-occ-module->inputs occ)
                                                           env-wires))
                   (mod.delayed-env (entry-svl-env-fix (hons-get occ-name delayed-env-alist)))
                   ((mv mod-output-vals mod-delayed-env)
                    (svl2-run-cycle (svl2-occ-module->name occ)
                                    mod-input-vals
                                    mod.delayed-env
                                    modules))
                   (env-wires (svl2-save-mod-outputs mod-output-vals
                                                     (svl2-occ-module->outputs  occ)
                                                     env-wires))
                   ((mv env-wires rest-delayed-env)
                    (svl2-run-cycle-occs (cdr occs)
                                         env-wires
                                         delayed-env-alist
                                         modules)))
                (mv env-wires
                    (if (not (equal mod-delayed-env (make-svl-env)))
                        (hons-acons occ-name
                                    mod-delayed-env
                                    rest-delayed-env)
                      rest-delayed-env)))))))
 ///

 (local
  (defthm svex-env-p-of-hons-gets-fast-alist
    (implies (and (sv::svarlist-p names)
                  (sv::svex-env-p env))
             (sv::svex-env-p (hons-gets-fast-alist names env)))
    :hints (("goal"
             :expand (hons-gets-fast-alist (cdr names) nil)
             :induct (hons-gets-fast-alist names env)
             :do-not-induct t
             :in-theory (e/d (hons-gets-fast-alist
                              sv::svar-p
                              occ-name-p
                              svex-env-p
                              occ-name-list-p)
                             ())))))

 (local
  (defthm guard-lemma1
    (implies (and (SVL2-MODULE-ALIST-P modules)
                  (ASSOC-EQUAL MODNAME MODULES))
             (and (SVL2-MODULE-P (CDR (ASSOC-EQUAL MODNAME MODULES)))
                  (CONSP (ASSOC-EQUAL MODNAME MODULES))))
    :hints (("Goal"
             :in-theory (e/d (SVL2-MODULE-ALIST-P) ())))))

 (verify-guards svl2-run-cycle-occs
   :otf-flg t
   :hints (("Goal"
            :in-theory (e/d (svexlist-eval2-is-svexlist-eval
                             svl2-well-ranked-module)
                            ())))))


#|
:i-am-here

(make-event
 (b* ((modnames '("full_adder_1$WIDTH=1"
                  "full_adder$WIDTH=1"
                  "booth2_reduction_dadda_17x65_97"
                  "booth2_multiplier_signed_64x32_97"))
      ((mv modules rp::rp-state)
       (svl2-flatten-design modnames
                            *big-sv-design*
                            *big-vl-design2*)))
   (mv nil
       `(defconst *big-svl2-design*
          ',modules)
       state
       rp::rp-state)))

(make-event
 (b* ((modnames '("FullAdder" "LF_127_126" "HalfAdder"))
      ((mv modules rp::rp-state)
       (svl2-flatten-design modnames
                            *signed64-sv-design*
                            *signed64-vl-design2*)))
   (mv nil
       `(defconst *signed64-svl2-design*
          ',modules)
       state
       rp::rp-state)))

(make-event
 (b* ((modnames '("FullAdder" "LF_255_254" "HalfAdder"))
      ((mv modules rp::rp-state)
       (svl2-flatten-design modnames
                            *signed128-sv-design*
                            *signed128-vl-design2*)))
   (mv nil
       `(defconst *signed128-svl2-design*
          ',modules)
       state
       rp::rp-state)))

(make-event
 (b* ((modnames '("FullAdder" "BK_511_510" "HalfAdder"))
      ((mv modules rp::rp-state)
       (svl2-flatten-design modnames
                            *signed256-sv-design*
                            *signed256-vl-design2*)))
   (mv nil
       `(defconst *signed256-svl2-design*
          ',modules)
       state
       rp::rp-state)))

(make-event
 (b* ((modnames '())
      ((mv modules rp::rp-state)
       (svl2-flatten-design modnames
                            *mult-sv-design*
                            *mult-vl-design2*)))
   (mv nil
       `(defconst *mult-svl2-design*
          ',modules)
       state
       rp::rp-state)))

(get-svl2-modules-ports *signed128-svl2-design*)

(time$
 (svl2-run-cycle "Multiplier_15_0_1000"
                 (list 233 45)
                 (make-svl-env)
                 *mult-svl2-design*))

(time$
 (svl2-run-cycle "Mult_64_64"
                 (list 233 45)
                 (make-svl-env)
                 *signed64-svl2-design*))

(time$
 (svl2-run-cycle "Mult_256_256"
                 (list 233 45)
                 (make-svl-env)
                 *signed256-svl2-design*))

(time$
 (svl2-run-cycle "Mult_128_128"
                 (list 233 45)
                 (make-svl-env)
                 *signed128-svl2-design*))

(time$
 (b* (((mv res &)
       (svl2-run-cycle "booth2_multiplier_signed_64x32_97"
                       (list 0 0 233 45)
                       (make-svl-env)
                       *big-svl2-design*)))
   (bits (+ (bits (car res) 0 97 )
                 (bits (car res) 97 97 )) 
             0 97 )))
||#
