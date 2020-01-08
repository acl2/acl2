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

(include-book "svl-run")

(local
 (in-theory (enable bits)))

(progn

  (def-rw-opener-error
    svl-start-env-opener-error
    (svl-start-env wires vals))
  
  (def-rp-rule svl-start-env-cons-1
    (equal (svl-start-env (cons `(,wire-name) rest-wires)
                           (cons val rest-vals))
           (hons-acons wire-name
                       val
                       (svl-start-env rest-wires rest-vals)))
    :hints (("Goal"
             :expand (svl-start-env (cons `(,wire-name) rest-wires)
                                     (cons val rest-vals))
             :in-theory (e/d () ()))))

  (def-rp-rule svl-start-env-nil
    (and (equal (svl-start-env nil vals)
                nil)
         (equal (svl-start-env wires nil)
                nil))
    :hints (("Goal"
             :in-theory (e/d (svl-start-env) ()))))

  (def-rp-rule svl-start-env-cons-2
    (equal (svl-start-env (cons `(,wire-name ,size . ,start)
                                 rest-wires)
                           (cons val rest-vals))
           (hons-acons wire-name
                       (bits val start size )
                       (svl-start-env rest-wires rest-vals)))
    :hints (("Goal"
             :expand (svl-start-env (cons `(,wire-name ,size . ,start)
                                           rest-wires)
                                     (cons val rest-vals))
             :in-theory (e/d () ())))))

(progn

  (def-rw-opener-error
    svl-retrieve-values-opener-error
    (svl-retrieve-values wires env-wires)
    :do-not-print (env-wires))
  
  (def-rp-rule svl-retrieve-values-nil
    (equal (svl-retrieve-values nil env-wires)
           nil)
    :hints (("Goal"
             :in-theory (e/d (svl-retrieve-values) ()))))

  (def-rp-rule svl-retrieve-values-cons-1
    (equal (svl-retrieve-values (cons `(,wire-name) rest) env-wires)
           (cons (entry-4vec-fix (hons-get wire-name env-wires))
                 (svl-retrieve-values rest env-wires)))
    #|(if (hons-get wire-name env-wires)
    (cdr (hons-get wire-name env-wires)) ;
    (sv::4vec-x))||#
    :hints (("Goal"
             :expand (svl-retrieve-values (cons `(,wire-name) rest) env-wires)
             :in-theory (e/d () ()))))

  (def-rp-rule svl-retrieve-values-cons-2
    (equal (svl-retrieve-values (cons `(,wire-name ,w . ,s) rest) env-wires)
           (cons (bits (entry-4vec-fix (hons-get wire-name env-wires)) s w )
                 (svl-retrieve-values rest env-wires)))
    #|(if (hons-get wire-name env-wires)
    (cdr (hons-get wire-name env-wires)) ;
    (sv::4vec-x))||#
    :hints (("Goal"
             :expand (svl-retrieve-values (cons `(,wire-name ,w . ,s) rest) env-wires)
             :in-theory (e/d ()
                             (entry-4vec-fix))))))

#|
(defthm save-lhs-to-env-wires-nil
  (equal (save-lhs-to-env-wires val nil env-wires)
         env-wires)
  :hints (("Goal"
           :expand (save-lhs-to-env-wires val nil env-wires)
           :in-theory (e/d () ()))))

(defthm save-lhs-to-env-wires-cons-1
  (implies (and (posp w))
           (equal (save-lhs-to-env-wires val (cons (cons w :z) rest) env-wires)
                  (save-lhs-to-env-wires (4vec-rsh w val)
                                         rest
                                         env-wires)))
  :hints (("Goal"
           :expand (save-lhs-to-env-wires val (cons (cons w :z) rest) env-wires)
           :in-theory (e/d (SV::LHRANGE->ATOM
                            SV::LHRANGE->W
                            SV::LHATOM-VAR->NAME) ()))))

(defthm save-lhs-to-env-wires-cons-2
  (implies t
           (equal (save-lhs-to-env-wires val (cons :z rest) env-wires)
                  (save-lhs-to-env-wires (4vec-rsh 1 val)
                                         rest
                                         env-wires)))
  :hints (("Goal"
           :expand (save-lhs-to-env-wires val (cons :z rest) env-wires)
           :in-theory (e/d (SV::LHRANGE->ATOM
                            SV::LHRANGE->W
                            SV::LHATOM-VAR->NAME) ()))))

(defthm save-lhs-to-env-wires-cons-3
  (implies (and (posp w))
           (equal (save-lhs-to-env-wires val
                                         (cons (cons w atom) rest)
                                         env-wires)
                  (save-lhs-to-env-wires (4vec-rsh w val)
                                         rest
                                         env-wires)))
  :hints (("Goal"
           :expand (save-lhs-to-env-wires val (cons :z rest) env-wires)
           :in-theory (e/d (SV::LHRANGE->ATOM
                            SV::LHRANGE->W
                            SV::LHATOM-VAR->NAME) ()))))
||#

(progn

  (def-rw-opener-error
    save-wires-to-env-wires-opener-error
    (save-wires-to-env-wires val wires env-wires)
    :do-not-print (env-wires))
  
  (def-rp-rule save-wires-to-env-wires-cons-1
    (equal (save-wires-to-env-wires val (cons `(,wire-name) rest) env-wires)
           (hons-acons wire-name val env-wires))
    :hints (("Goal"
             :Expand (save-wires-to-env-wires val (cons `(,wire-name) rest) env-wires)
             :in-theory (e/d () ()))))

  (def-rp-rule save-wires-to-env-wires-nil
    (equal (save-wires-to-env-wires val nil env-wires)
           env-wires)
    :hints (("Goal"
             :expand (save-wires-to-env-wires val nil env-wires)
             :in-theory (e/d () ()))))

  (def-rp-rule save-wires-to-env-wires-cons-2
    (equal (save-wires-to-env-wires val (cons `(,wire-name ,w . ,s) rest) env-wires)
           (hons-acons
            wire-name
            (sbits s w val (entry-4vec-fix (hons-get wire-name env-wires)))
            (save-wires-to-env-wires (4vec-rsh w val)
                                     rest
                                     env-wires)))
    :hints (("Goal"
             :Expand (save-wires-to-env-wires val (cons `(,wire-name ,w . ,s) rest) env-wires)
             :in-theory (e/d () ()))))

  (def-rp-rule save-wires-to-env-wires-cons-3
    (equal (save-wires-to-env-wires val (cons `(,wire-name ,w . ,s) nil) env-wires)
           (hons-acons
            wire-name
            (sbits s w val (entry-4vec-fix (hons-get wire-name env-wires)))
            env-wires))
    :hints (("Goal"
             :Expand (save-wires-to-env-wires val (cons `(,wire-name ,w . ,s) rest) env-wires)
             :in-theory (e/d () ())))))



(progn

  (def-rw-opener-error
    svex-env-append-opener-error
    (svex-env-append term1 term2)) 
  
  (def-rp-rule svex-env-append-opener-cons
    (equal (svex-env-append (cons x rest) lst2)
           (hons-acons (car x) (cdr x)
                       (svex-env-append rest lst2)))
    :hints (("Goal"
             :in-theory (e/d (svex-env-append) ()))))

  (def-rp-rule svex-env-append-opener-nil
    (equal (svex-env-append nil lst2)
           lst2)
    :hints (("Goal"
             :in-theory (e/d (svex-env-append) ())))))

(progn
  (def-rp-rule create-next-env-for-wires-opener-nil
    (equal (create-next-env-for-wires nil env-wires)
           nil)
    :hints (("Goal"
             :in-theory (e/d (create-next-env-for-wires) ()))))

  (def-rp-rule create-next-env-for-wires-opener-cons
    (equal (create-next-env-for-wires (cons x rest) env-wires)
           (acons x
                  (entry-4vec-fix (hons-get (sv::change-svar x :delay 0)
                                            env-wires))
                  (create-next-env-for-wires rest env-wires)))
    :hints (("Goal"
             :in-theory (e/d (create-next-env-for-wires) ())))))

(progn

  (def-rw-opener-error
    svl-save-mod-outputs-opener-error
    (svl-save-mod-outputs vals wire-list-list env-wires)
    :do-not-print (env-wires))
  
  (def-rp-rule svl-save-mod-outputs-nil
    (and (equal (svl-save-mod-outputs nil wire-list-list env-wires)
                env-wires)
         (equal (svl-save-mod-outputs vals nil env-wires)
                env-wires))
    :hints (("Goal"
             :in-theory (e/d (svl-save-mod-outputs) ()))))

  (def-rp-rule svl-save-mod-outputs-cons
    (equal (svl-save-mod-outputs (cons val1 rest-vals)
                                  (cons wires rest-wires)
                                  env-wires)
           (b* ((env-wires (save-wires-to-env-wires val1
                                                    wires
                                                    env-wires)))
             (svl-save-mod-outputs rest-vals
                                    rest-wires
                                    env-wires)))
    :hints (("Goal"
             :in-theory (e/d (svl-save-mod-outputs) ())))))


(encapsulate
  nil
  (local
   (in-theory (enable SVL-MODULE-ALIST-P
                      SVL-OCC-P
                      SVL-MODULE-P)))
  
  (define svl-get-module-rank$ ((modname sv::modname-p)
                                 (modules svl-module-alist-p))
    (b* ((module (assoc-equal modname modules)))
      (if module
          (nfix (cdr (std::da-nth 0 (cdr module))))
        0)))

  (define svl-get-max-occ-rank$ ((occs svl-occ-alist-p)
                                  (modules svl-module-alist-p))
    (cond ((atom occs)
           0)
          ((equal (car (cdar occs)) ':assign)
           (svl-get-max-occ-rank$ (cdr occs)
                                   modules))
          (t (max (svl-get-module-rank$ (STD::DA-NTH 2 (CDR  (cdar occs))) modules)
                  (svl-get-max-occ-rank$ (cdr occs) modules)))))

  (define svl-well-ranked-module$ ((modname sv::modname-p)
                                    (modules svl-module-alist-p)) 
    (and (assoc-equal modname modules)
         (> (svl-get-module-rank$ modname modules)
            (svl-get-max-occ-rank$ (CDR (STD::DA-NTH 4
                                                      (cdr (assoc-equal modname modules))))
                                    modules)))))

(memoize 'svl-well-ranked-module$)

(encapsulate
  nil

  (local
   (defthm svl-get-module-rank$-is-svl-get-module-rank
     (implies (and (sv::modname-p modname)
                   (svl-module-alist-p modules))
              (equal (svl-get-module-rank$ modname modules)
                     (svl-get-module-rank modname modules)))
     :hints (("Goal"
              :in-theory (e/d (svl-get-module-rank$
                               svl-get-module-rank
                               SVL-MODULE->RANK) ())))))

  (local
   (defthm svl-get-max-occ-rank$-is-svl-get-max-occ-rank
     (implies (and (svl-occ-alist-p occs)
                   (svl-module-alist-p modules))
              (equal (svl-get-max-occ-rank$ occs modules)
                     (svl-get-max-occ-rank occs modules)))
     :hints (("Goal"
              :do-not-induct t
              :induct (svl-get-max-occ-rank$ occs modules)
              :in-theory (e/d (svl-get-max-occ-rank$
                               SVL-OCC-KIND
                               SV::MODNAME-FIX
                               SVL-OCC-MODULE->NAME
                               SV::MODNAME-P
                               SVL-OCC-ALIST-P
                               SVL-OCC-P
                               svl-get-max-occ-rank) ())))))

  (local
   (defthm SVL-MODULE-P-implies
     (implies (SVL-MODULE-P x)
              (svl-occ-alist-p (CDR (CADR (CDDDR x)))))
     :hints (("Goal"
              :in-theory (e/d (SVL-MODULE-P) ())))))

  (local
   (defthm lemma1
     (implies (and (svl-module-alist-p modules)
                   (ASSOC-EQUAL MODNAME MODULES))
              (SVL-MODULE-P  (cdr  (ASSOC-EQUAL MODNAME MODULES))))))

  (def-rp-rule svl-well-ranked-module-is-svl-well-ranked-module$
    (implies (and (sv::modname-p modname)
                  (svl-module-alist-p modules))
             (equal
              (svl-well-ranked-module modname modules)
              (svl-well-ranked-module$ modname modules)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (svl-well-ranked-module
                              SVL-MODULE->OCCS
                              svl-well-ranked-module$)
                             ())))))

(def-rw-opener-error
  svl-run-phase-opener-error
  (svl-run-phase modname inputs delayed-env modules)
  :do-not-print (modules))

(def-rw-opener-error
  svl-run-phase-occs-opener-error
  (svl-run-phase-occs occs env-wires delayed-env modules)
  :do-not-print (modules
                  env-wires
                  delayed-env))

(defmacro make-svl-env-wog (&rest args)
  (std::make-aggregate 'list
                       args '((:wires) (:modules))
                       'make-svl-env-wog
                       nil))

(acl2::defines
 svl-run-phase-wog
 :flag-defthm-macro defthm-svl-run-phase-wog
 (define svl-run-phase-wog (modname
                          inputs
                          delayed-env
                          modules)
   :verify-guards nil
   :flag svl-run-phase-wog
   :measure (acl2::nat-list-measure
             (list (svl-get-module-rank$ modname; (sv::modname-fix modname)
                                          modules;(svl-module-alist-fix modules)
                                          )
                   (cons-count modname;(sv::modname-fix modname)
                               )))
   :hints (("Goal"
            :in-theory (e/d (rp::measure-lemmas
                             SVL-GET-MAX-OCC-RANK$
                             SVL-WELL-RANKED-MODULE$) ())))

   (cond ((not (svl-well-ranked-module$ modname modules)) ;; for termination
          (mv nil (make-svl-env)))
         (t
          (b* ((x (cdr (assoc-equal modname modules)))
               (env-wires (svl-start-env (CDR (STD::DA-NTH 1 X)) inputs))
               (env-wires
                (svex-env-append (car delayed-env)
                                 env-wires))
                #|(svl-run-add-delayed-ins env-wires delayed-env
                                         (CDR (STD::DA-NTH 2 X)))||#
               ((mv env-wires next-delayed-env.modules)
                (svl-run-phase-occs-wog (CDR (STD::DA-NTH 4 X))
                                      env-wires
                                      (cadr delayed-env)
                                      modules))
               (out-vals (svl-retrieve-values (CDR (STD::DA-NTH 3 X))
                                               env-wires))
               (next-delayed-env (make-svl-env-wog
                                  :wires (create-next-env-for-wires
                                          (CDR (STD::DA-NTH 2 X))
                                          env-wires)
                                  :modules next-delayed-env.modules))
               (- (fast-alist-free env-wires)))
            (mv out-vals
                next-delayed-env)))))

 (define svl-run-phase-occs-wog (occs
                               env-wires
                               delayed-env-alist
                               modules)
   :measure (acl2::nat-list-measure
             (list (svl-get-max-occ-rank$ occs;(svl-occ-alist-fix occs)
                                           modules;(svl-module-alist-fix modules)
                                           )
                   (cons-count occs;(svl-occ-alist-fix occs)
                               )))
   :flag svl-run-phase-occs-wog
   (let ((occ-name (caar occs))
         (occ (cdar occs)))
     (cond ((atom occs)
            (mv env-wires nil))
           ((equal (car occ) ':assign)
            (b* ((env-wires (hons-acons (STD::DA-NTH 0 (CDR occ))
                                        (svex-eval-wog (std::da-nth 1 (cdr occ))
                                                    env-wires)
                                        env-wires)))
              (svl-run-phase-occs-wog (cdr occs)
                                    env-wires
                                    delayed-env-alist
                                    modules)))
           (t (b* ((mod-input-vals (svexlist-eval-wog (STD::DA-NTH 0 (CDR occ))
                                                   env-wires))
                   (mod.delayed-env (entry-svl-env-fix (hons-get occ-name delayed-env-alist)))

                   ((mv mod-output-vals mod-delayed-env)
                    (svl-run-phase-wog (std::da-nth 2 (cdr occ))
                                     mod-input-vals
                                     mod.delayed-env
                                     modules))
                   (env-wires (svl-save-mod-outputs mod-output-vals
                                                     (STD::DA-NTH 1 (CDR occ))
                                                     env-wires))
                   ((mv env-wires rest-delayed-env)
                    (svl-run-phase-occs-wog (cdr occs)
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
  (defthm svl-occ-kind-redef
    (implies (and (SVL-OCC-P x))
             (equal (svl-occ-kind x)
                    (car x)))
    :hints (("Goal"
             :in-theory (e/d (svl-occ-module->inputs
                              SVL-OCC-KIND
                              SVL-OCC-P) ())))))

 (local
  (defthm svl-occ-module->inputs-redef
    (implies (and (svl-occ-p x)
                  (not (equal (svl-occ-kind x) :assign)))
             (equal (svl-occ-module->inputs x)
                    (std::da-nth 0 (cdr x))))
    :hints (("goal"
             :in-theory (e/d (svl-occ-module->inputs
                              svl-occ-kind
                              svl-occ-p) ())))))

 (local
  (defthm svl-occ-module->name-redef
    (implies (and (svl-occ-p x)
                  (not (equal (svl-occ-kind x) :assign)))
             (equal (svl-occ-module->name x)
                    (std::da-nth 2 (cdr x))))
    :hints (("goal"
             :in-theory (e/d (svl-occ-module->name
                              svl-occ-kind
                              svl-occ-p) ())))))

 (local
  (defthm lemma1
    (implies (and (consp occs)
                  (not (equal (cadr (car occs)) :assign))
                  (svl-occ-alist-p occs))
             (and (svexlist-p (caddr (car occs)))
                  (sv::modname-p (car (cddddr (car occs))))))
    :hints (("goal"
             :expand (svl-occ-alist-p occs)
             :do-not-induct t
             :in-theory (e/d (svl-occ-alist-p
                              svl-occ-p) ())))))

 (local
  (defthm lemma2
    (implies (and (consp occs)
                  (equal (cadr (car occs)) :assign)
                  (svl-occ-alist-p occs))
             (and (svex-p (cadddr (car occs)))
                  ))
    :hints (("goal"
             :expand (svl-occ-alist-p occs)
             :do-not-induct t
             :in-theory (e/d (svl-occ-alist-p
                              svl-occ-p) ())))))

 (local
  (defthm svl-occ-module->outputs-redef
    (implies (and (svl-occ-p x)
                  (not (equal (svl-occ-kind x) :assign)))
             (equal (svl-occ-module->outputs x)
                    (std::da-nth 1 (cdr x))))
    :hints (("goal"
             :in-theory (e/d (svl-occ-module->outputs
                              svl-occ-kind
                              svl-occ-p) ())))))

 (local
  (defthm svl-occ-assign-redef
    (implies (and (svl-occ-p x)
                  (equal (svl-occ-kind x) :assign))
             (and (equal (svl-occ-assign->output x)
                         (std::da-nth 0 (cdr x)))
                  (equal (svl-occ-assign->svex x)
                         (std::da-nth 1 (cdr x)))))
    :hints (("goal"
             :in-theory (e/d (svl-occ-assign->output
                              svl-occ-assign->svex
                              svl-occ-kind
                              SVL-OCC-P) ())))))

 (defthm wire-list-fix-def
   (implies (wire-list-p x)
            (equal (wire-list-fix x)
                   x)))

 (local
  (defthm SVL-MODULE->OUTPUTS-redef
    (implies (SVL-MODULE-P x)
             (equal (SVL-MODULE->OUTPUTS x)
                    (CDR (STD::DA-NTH 3 X))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (SVL-MODULE->OUTPUTS
                              SVL-MODULE-P) ())))))

 (local
  (defthm SVL-MODULE->occs-redef
    (implies (SVL-MODULE-P x)
             (equal (SVL-MODULE->occs x)
                    (CDR (STD::DA-NTH 4 X))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (SVL-MODULE->occs
                              SVL-MODULE-P) ())))))

 (local
  (defthm SVL-MODULE->inputs-redef
    (implies (SVL-MODULE-P x)
             (equal (SVL-MODULE->inputs x)
                    (CDR (STD::DA-NTH 1 X))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (SVL-MODULE->inputs
                              SVL-MODULE-P) ())))))

 (local
  (defthm SVL-MODULE->delayed-inputs-redef
    (implies (SVL-MODULE-P x)
             (equal (SVL-MODULE->delayed-inputs x)
                    (CDR (STD::DA-NTH 2 X))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (SVL-MODULE->delayed-inputs
                              SVL-MODULE-P) ())))))

 (local
  (defthm SVL-WELL-RANKED-MODULE$-implies
    (implies (SVL-WELL-RANKED-MODULE$ x y)
             (assoc-equal x y))
    :hints (("Goal"
             :in-theory (e/d (SVL-WELL-RANKED-MODULE$) ())))))

 (local
  (defthm SVL-MODULE-P-of-assoc-equal
    (implies (and (SVL-MODULE-ALIST-P MODULES)
                  (ASSOC-EQUAL MODNAME MODULES))
             (SVL-MODULE-P (CDR (ASSOC-EQUAL MODNAME MODULES))))
    :hints (("Goal"
             :do-not-induct t
             :induct (ASSOC-EQUAL MODNAME MODULES)
             :in-theory (e/d (SVL-WELL-RANKED-MODULE$
                              SVL-MODULE-ALIST-P) ())))))

 (local
  (defthm lemma3
    (implies (SVL-MODULE-P module)
             (and (SVL-OCC-ALIST-P (CDR (CADR (CDDDR module))))
                  (WIRE-LIST-P (CDR (Cadr module)))))
    :hints (("Goal"
             :in-theory (e/d (SVL-MODULE-P) ())))))

 (local
  (defthm lemma4
    (implies (and (SVL-OCC-ALIST-P OCCS)
                  (EQUAL (CADR (CAR OCCS)) :ASSIGN))
             (SV::SVAR-P (CADDR (CAR OCCS))))
    :hints (("Goal"
             :expand (SVL-OCC-ALIST-P OCCS)
             :in-theory (e/d (SVL-OCC-P) ())))))

 (local
  (defthm lemma5
    (implies (and (CONSP OCCS)
                  (NOT (EQUAL (CADR (CAR OCCS)) :ASSIGN))
                  (SVL-OCC-ALIST-P OCCS))
             (WIRE-LIST-LISTP (CADDDR (CAR OCCS))))
    :hints (("Goal"
             :expand (SVL-OCC-ALIST-P OCCS)
             :in-theory (e/d (SVL-OCC-P) ())))))


 (local
  (defthm lemma6
    (implies (and (force (svex-env-p wires))
                  (force (svl-env-alist-p modules)))
             (equal (make-svl-env :wires wires :modules modules)
                    (make-svl-env-wog :wires wires :modules modules)))
    :hints (("Goal"
             :in-theory (e/d (SVL-ENV->MODULES
                              SVL-ENV-P
                              SVL-ENV->WIRES) ())))))


 (local
  (defthm lemma7
    (implies (and (SVL-MODULE-ALIST-P MODULES)
                  (SV::MODNAME-P MODNAME))
             (SV::SVARLIST-P (CDR (CADDDR (ASSOC-EQUAL MODNAME MODULES)))))
    :hints (("Goal"
             :in-theory (e/d (SVL-MODULE-ALIST-P
                              SVL-MODULE-P)
                             ((:DEFINITION WIRE-P)
                              (:REWRITE LEMMA3)
                              (:REWRITE
                                SVL-MODULE-P-OF-CDAR-WHEN-SVL-MODULE-ALIST-P)))))))
 
 (defthm-svl-run-phase-wog
   (defthm svl-run-phase-is-svl-run-phase-wog
     (implies (and (force (sv::modname-p modname))
                   (force (sv::4veclist-p inputs))
                   (force (svl-env-p delayed-env))
                   (force (svl-module-alist-p modules)))
              (equal (svl-run-phase modname inputs delayed-env modules)
                     (svl-run-phase-wog modname inputs delayed-env modules)))
     :flag svl-run-phase-wog)

   (defthm svl-run-phase-occs-is-svl-run-phase-occs-wog
     (implies (and (svl-occ-alist-p occs)
                   (sv::svex-env-p env-wires)
                   (svl-env-alist-p delayed-env-alist)
                   (svl-module-alist-p modules))
              (equal (svl-run-phase-occs occs env-wires delayed-env-alist modules)
                     (svl-run-phase-occs-wog occs env-wires delayed-env-alist modules)))
     :flag svl-run-phase-occs-wog)
   :hints (("Goal"
            :expand ((SVL-RUN-PHASE-OCCS OCCS
                                          ENV-WIRES DELAYED-ENV-ALIST MODULES)
                     (SVL-RUN-PHASE-OCCS-WOG OCCS
                                           ENV-WIRES DELAYED-ENV-ALIST MODULES)
                     (SVL-RUN-PHASE MODNAME INPUTS DELAYED-ENV MODULES)
                     (:free (x y)
                            (svl-env->wires (cons x y)))
                     (:free (x y)
                            (svl-env->modules (cons x y)))
                     (:free (x y)
                            (svl-env-p (cons x y))))
            :in-theory (e/d (svexlist-eval-wog-is-svexlist-eval
                             svl-run-phase
                             svl-run-phase-wog
                             SVL-RUN-PHASE-OCCS-WOG
                             svl-run-phase-occs) ()))))

 (add-rp-rule svl-run-phase-is-svl-run-phase-wog)
 (add-rp-rule svl-run-phase-occs-is-svl-run-phase-occs-wog))



(progn
  (def-rw-opener-error
    svl-run-phase-wog-opener-error
    (svl-run-phase-wog modname inputs
                     delayed-env
                     modules)
    :do-not-print (modules))

  (rp::defthm-lambda
   svl-run-phase-wog-opener
   (implies
    (svl-well-ranked-module$ modname modules)
    (equal (svl-run-phase-wog modname inputs
                            delayed-env
                            modules)
           (b* ((x (cdr (assoc-equal modname modules)))
                (- (cw "Using svl-run-phase-wog-opener for ~p0 ~%"
                       modname))
                (env-wires (svex-env-append
                            (car delayed-env)
                            (svl-start-env (CDR (STD::DA-NTH 1 X)) inputs)
                                        ;delayed-env
                                        ;(CDR (STD::DA-NTH 2 X))
                                        ))
                ((mv env-wires next-delayed-env.modules)
                 (svl-run-phase-occs-wog (CDR (STD::DA-NTH 4 X))
                                       env-wires
                                       (cadr delayed-env)
                                       modules))
                (out-vals (svl-retrieve-values (CDR (STD::DA-NTH 3 X))
                                                env-wires))
                (next-delayed-env (make-svl-env-wog
                                   :wires (create-next-env-for-wires
                                           (CDR (STD::DA-NTH 2 X))
                                           env-wires)
                                   :modules next-delayed-env.modules))
                (- (fast-alist-free env-wires)))
             (mv out-vals
                 next-delayed-env))))
   :hints (("Goal"
            :expand (svl-run-phase-wog modname inputs
                                     delayed-env
                                     modules)
            :in-theory (e/d () ())))))

(progn
  (def-rw-opener-error
    svl-run-phase-occs-wog-opener-error
    (svl-run-phase-occs-wog occs env-wires delayed-env-alist modules)
    :do-not-print (env-wires))

  (def-rp-rule svl-run-phase-occs-wog-opener-nil
    (equal (svl-run-phase-occs-wog nil env-wires delayed-env-alist modules)
           (mv env-wires nil))
    :hints (("Goal"
             :expand (svl-run-phase-occs-wog nil env-wires delayed-env-alist modules)
             :in-theory (e/d () ()))))

  (def-rp-rule svl-run-phase-occs-wog-opener-cons-assign
    (equal (svl-run-phase-occs-wog
            (cons (cons occ-name (cons ':assign cdr-occ)) rest)
            env-wires delayed-env-alist modules)
           (b* ((env-wires (hons-acons (std::da-nth 0 cdr-occ)
                                       (svex-eval-wog (std::da-nth 1 cdr-occ)
                                                   env-wires)
                                       env-wires)))
             (svl-run-phase-occs-wog rest
                                   env-wires
                                   delayed-env-alist
                                   modules)))
    :hints (("Goal"
             :expand (svl-run-phase-occs-wog
                      (cons (cons occ-name (cons ':assign cdr-occ)) rest)
                      env-wires delayed-env-alist modules)
             :in-theory (e/d () ()))))

  (defthm-lambda svl-run-phase-occs-wog-opener-cons-module
    (equal (svl-run-phase-occs-wog
            (cons (cons occ-name (cons ':module cdr-occ)) rest)
            env-wires delayed-env-alist modules)
           (b* (((mv mod-output-vals mod-delayed-env)
                 (svl-run-phase-wog (std::da-nth 2 cdr-occ)
                                  (svexlist-eval-wog (STD::DA-NTH 0 cdr-occ)
                                                env-wires)
                                  (entry-svl-env-fix (hons-get occ-name delayed-env-alist))
                                  modules))
                ((mv env-wires rest-delayed-env)
                 (svl-run-phase-occs-wog rest
                                       (svl-save-mod-outputs mod-output-vals
                                                  (std::da-nth 1 cdr-occ)
                                                  env-wires)
                                       delayed-env-alist
                                       modules)))
             (mv env-wires
                 (if (not (equal mod-delayed-env (make-svl-env)))
                     (hons-acons occ-name
                                 mod-delayed-env
                                 rest-delayed-env)
                   rest-delayed-env))))
    :hints (("Goal"
             :expand (svl-run-phase-occs-wog
                      (cons (cons occ-name (cons ':module cdr-occ)) rest)
                      env-wires delayed-env-alist modules)
             :in-theory (e/d () ())))))



(progn
  (def-rw-opener-error
    pairlis3-opener-error
    (pairlis3 x y))

  (def-rp-rule pairlis3-opener-done
    (implies (or (atom x)
                 (atom y))
             (equal (pairlis3 x y)
                    nil))
    :hints (("Goal"
             :in-theory (e/d (pairlis3) ()))))

  (def-rp-rule pairlis3-opener-cons
    (equal (pairlis3 (cons x rest1)
                     (cons y rest2))
           (acons x y (pairlis3 rest1 rest2)))
    :hints (("Goal"
             :in-theory (e/d (pairlis3) ())))))

(progn
  (def-rw-opener-error
    svl-run-save-output-opener-error
    (svl-run-save-output out-alist out-bind-alist))

  (def-rp-rule svl-run-save-output-opener-nil
    (equal (svl-run-save-output out-alist nil)
           (mv nil nil))
    :hints (("Goal"
             :in-theory (e/d (svl-run-save-output) ()))))

  (rp::defthm-lambda
   svl-run-save-output-opener-cons
   (equal (svl-run-save-output out-alist
                                (cons x rest))
          (b* (((mv rest-outputs rest-out-bind-alist)
                (svl-run-save-output out-alist rest))
               (this x)
               (key (car this))
               (val (cdr this))
               ((when (atom val))
                (mv rest-outputs rest-out-bind-alist))
               ((when (s-equal (car val) '_))
                (mv rest-outputs (acons key (cdr val) rest-out-bind-alist)))
               ((mv signame pos1 pos2)
                (svl-run-simplify-signame key))
               (out-entry (assoc-equal signame out-alist))
               ((unless out-entry)
                (progn$ (cw "Warning \"~p0\" is not an output signal. ~%" signame)
                        (mv rest-outputs (acons key (cdr val) rest-out-bind-alist))))        
               (out-val (cdr out-entry)) 
               ((unless (and (natp pos1)
                             (natp pos2)))
                (mv (acons (car val) out-val rest-outputs)
                    (acons key (cdr val) rest-out-bind-alist)))
               ((mv start size) (if (> pos1 pos2)
                                    (mv pos2 (nfix (+ pos1 (- pos2) 1)))
                                  (mv pos1 (nfix (+ pos2 (- pos1) 1))))))
            (mv (acons (car val) (bits out-val start size) rest-outputs)
                (acons key (cdr val) rest-out-bind-alist))))
   :hints (("Goal"
            :in-theory (e/d (svl-run-save-output) ())))))





(progn
  (define svl-run-aux-wog (modname
                           inputs
                           out-wires
                           out-bind-alist
                           delayed-env
                           modules)
    :verify-guards nil
    (if (atom inputs)
        (progn$ ;(svl-free-env modname delayed-env modules (expt 2 30))
         nil)
      (b* (((mv out-vals next-delayed-env)
            (svl-run-phase-wog modname (car inputs) delayed-env modules))
           (out-alist (pairlis3 out-wires out-vals))
           ((mv outputs out-bind-alist) (svl-run-save-output out-alist out-bind-alist))
           (rest (svl-run-aux-wog modname (cdr inputs) out-wires out-bind-alist next-delayed-env modules)))
        (append outputs rest))))
  
  (def-rw-opener-error
    svl-run-aux-opener-error
    (svl-run-aux modname inputs out-wires out-bind-alist delayed-env modules)
    :do-not-print (modules delayed-env))

  (def-rw-opener-error
    svl-run-aux-wog-opener-error
    (svl-run-aux-wog modname inputs out-wires out-bind-alist delayed-env modules)
    :do-not-print (modules delayed-env))

  (def-rp-rule svl-run-aux-is-svl-run-aux-wog
    (implies (and (force (sv::modname-p modname))
                  (force (4vec-list-listp inputs ))
                  (force (sv::svarlist-p out-wires))
                  (force (alistp out-bind-alist))
                  (force (svl-env-p delayed-env))
                  (force (svl-module-alist-p modules)))
             (equal (svl-run-aux modname inputs out-wires out-bind-alist
                                 delayed-env modules)
                    (svl-run-aux-wog modname inputs out-wires out-bind-alist
                                     delayed-env modules)))
    :hints (("Goal" 
             :in-theory (e/d (SVL-RUN-AUX
                              svl-run-aux-wog)
                             (RETURN-TYPE-OF-SVL-RUN-PHASE.NEXT-DELAYED-ENV)))
            ("Subgoal *1/2"
             :use ((:instance return-type-of-svl-run-phase.next-delayed-env
                              (inputs (car inputs)))))
            ("Subgoal *1/4"
             :use ((:instance return-type-of-svl-run-phase.next-delayed-env
                              (inputs (car inputs)))))))

  (def-rp-rule svl-run-aux-wog-opener-nil
    (equal (svl-run-aux-wog modname nil out-wires out-bind-alist
                            delayed-env modules)
           nil)
    :hints (("Goal"
             :in-theory (e/d (svl-run-aux-wog) ()))))
  
  (rp::defthm-lambda
   svl-run-aux-opener-cons
   (equal (svl-run-aux-wog modname (cons x y) out-wires out-bind-alist
                           delayed-env modules)
          (b* (((mv out-vals next-delayed-env)
                (svl-run-phase-wog modname x delayed-env modules))
               (out-alist (pairlis3 out-wires out-vals))
               ((mv outputs out-bind-alist) (svl-run-save-output out-alist out-bind-alist))
               (rest (svl-run-aux-wog modname y out-wires out-bind-alist next-delayed-env modules)))
            (append outputs rest)))
   :hints (("Goal"
            :in-theory (e/d (svl-run-aux-wog)
                            (svl-run-phase-is-svl-run-phase-wog))))))



(progn
  #|(define svl-run-wog (modname inputs-env ;; needs to be fast-alist
                               ins-bind-alist ;; a constant to tell what input
                               ;; signal should be assigned to what and when
                               out-bind-alist ;; same as above but for outputs
                               modules)
    :guard (and (string-listp (strip-cars out-bind-alist))
                (string-listp (strip-cars ins-bind-alist)))
    (declare (ignorable out-bind-alist))
    (b* ((module (assoc-equal modname modules))
         ((unless module)
          (hard-error 'svl-run
                      "Module ~p0 cannot be found! ~%"
                      (list (cons #\0 modname))))
         (module (cdr module))
         (input-wires (svl-module->inputs module))
         (output-wires (strip-cars (svl-module->outputs module)))
         (inputs-unbound (svl-generate-inputs ins-bind-alist input-wires))
         ((unless (svex-list-listp inputs-unbound))
          (hard-error 'svl-run
                      "Something went wrong while parsing inputs... ~p0 ~%"
                      (list (cons #\0 inputs-unbound))))
         ;; everything up to here uses only constants (only executable counterparts)
         (inputs (svexlist-list-eval-wog inputs-unbound inputs-env)))
      (svl-run-aux modname inputs output-wires out-bind-alist (make-svl-env) modules)))||#

  
  (def-rw-opener-error
    svl-run-opener-error
    (svl-run modname inputs-env ins-bind-alist out-bind-alist modules)
    :do-not-print (modules))


  

  (local
   (defthm strip-cars-of-wire-listp-is-svar-listp
     (implies (and (wire-list-p wires))
              (sv::svarlist-p (strip-cars wires))))) 

  
  (rp::defthm-lambda
   svl-run-def-opener
   (implies (and (force (sv::modname-p modname))
                 (force (svex-env-p inputs-env))
                 (force (alistp out-bind-alist))
                 (force (svl-module-alist-p modules))) 
            (equal (svl-run modname
                            inputs-env
                            ins-bind-alist
                            out-bind-alist
                            modules)
                   (b* ((module (assoc-equal modname modules))
                        ((unless module)
                         (hard-error 'svl-run
                                     "Module ~p0 cannot be found! ~%"
                                     (list (cons #\0 modname))))
                        (module (cdr module))
                        (input-wires (svl-module->inputs module))
                        (output-wires (strip-cars (svl-module->outputs module)))
                        (inputs-unbound (svl-generate-inputs ins-bind-alist input-wires))
                        ((unless (svex-list-listp inputs-unbound))
                         (hard-error 'svl-run
                                     "Something went wrong while parsing inputs... ~p0 ~%"
                                     (list (cons #\0 inputs-unbound))))
                        ;; everything up to here uses only constants (only executable counterparts)
                        (inputs (svexlist-list-eval-wog inputs-unbound inputs-env)))
                     (svl-run-aux-wog modname inputs output-wires out-bind-alist
                                      (make-svl-env) modules))))
   :hints (("Goal"
            :in-theory (e/d (svl-run) ())))))


(rp::add-rp-rule sv::4veclist-p-of-cons)

(def-rp-rule svex-env-p-of-falist
  (equal (sv::svex-env-p (cons (cons a b) rest))
         (and (sv::svar-p a)
              (sv::4vec-p b)
              (sv::svex-env-p rest))))


