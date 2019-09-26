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

(include-book "svl2")

(progn

  (def-rw-opener-error
    svl2-start-env-opener-error
    (svl2-start-env wires vals))
  
  (defthm svl2-start-env-cons-1
    (equal (svl2-start-env (cons `(,wire-name) rest-wires)
                           (cons val rest-vals))
           (hons-acons wire-name
                       val
                       (svl2-start-env rest-wires rest-vals)))
    :hints (("Goal"
             :expand (svl2-start-env (cons `(,wire-name) rest-wires)
                                     (cons val rest-vals))
             :in-theory (e/d () ()))))

  (defthm svl2-start-env-nil
    (and (equal (svl2-start-env nil vals)
                nil)
         (equal (svl2-start-env wires nil)
                nil))
    :hints (("Goal"
             :in-theory (e/d (svl2-start-env) ()))))

  (defthm svl2-start-env-cons-2
    (equal (svl2-start-env (cons `(,wire-name ,size . ,start)
                                 rest-wires)
                           (cons val rest-vals))
           (hons-acons wire-name
                       (bits val start size )
                       (svl2-start-env rest-wires rest-vals)))
    :hints (("Goal"
             :expand (svl2-start-env (cons `(,wire-name ,size . ,start)
                                           rest-wires)
                                     (cons val rest-vals))
             :in-theory (e/d () ())))))

(progn

  (def-rw-opener-error
    svl2-retrieve-values-opener-error
    (svl2-retrieve-values wires env-wires)
    :vars-to-avoid (env-wires))
  
  (defthm svl2-retrieve-values-nil
    (equal (svl2-retrieve-values nil env-wires)
           nil)
    :hints (("Goal"
             :in-theory (e/d (svl2-retrieve-values) ()))))

  (defthm svl2-retrieve-values-cons-1
    (equal (svl2-retrieve-values (cons `(,wire-name) rest) env-wires)
           (cons (entry-4vec-fix (hons-get wire-name env-wires))
                 (svl2-retrieve-values rest env-wires)))
    #|(if (hons-get wire-name env-wires)
    (cdr (hons-get wire-name env-wires)) ;
    (sv::4vec-x))||#
    :hints (("Goal"
             :expand (svl2-retrieve-values (cons `(,wire-name) rest) env-wires)
             :in-theory (e/d () ()))))

  (defthm svl2-retrieve-values-cons-2
    (equal (svl2-retrieve-values (cons `(,wire-name ,w . ,s) rest) env-wires)
           (cons (bits (entry-4vec-fix (hons-get wire-name env-wires)) s w )
                 (svl2-retrieve-values rest env-wires)))
    #|(if (hons-get wire-name env-wires)
    (cdr (hons-get wire-name env-wires)) ;
    (sv::4vec-x))||#
    :hints (("Goal"
             :expand (svl2-retrieve-values (cons `(,wire-name ,w . ,s) rest) env-wires)
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
    :vars-to-avoid (env-wires))
  
  (defthm save-wires-to-env-wires-cons-1
    (equal (save-wires-to-env-wires val (cons `(,wire-name) rest) env-wires)
           (hons-acons wire-name val env-wires))
    :hints (("Goal"
             :Expand (save-wires-to-env-wires val (cons `(,wire-name) rest) env-wires)
             :in-theory (e/d () ()))))

  (defthm save-wires-to-env-wires-nil
    (equal (save-wires-to-env-wires val nil env-wires)
           env-wires)
    :hints (("Goal"
             :expand (save-wires-to-env-wires val nil env-wires)
             :in-theory (e/d () ()))))

  (defthm save-wires-to-env-wires-cons-2
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

  (defthm save-wires-to-env-wires-cons-3
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
    svl2-save-mod-outputs-opener-error
    (svl2-save-mod-outputs vals wire-list-list env-wires)
    :vars-to-avoid (env-wires))
  
  (defthm svl2-save-mod-outputs-nil
    (and (equal (svl2-save-mod-outputs nil wire-list-list env-wires)
                env-wires)
         (equal (svl2-save-mod-outputs vals nil env-wires)
                env-wires))
    :hints (("Goal"
             :in-theory (e/d (svl2-save-mod-outputs) ()))))

  (defthm svl2-save-mod-outputs-cons
    (equal (svl2-save-mod-outputs (cons val1 rest-vals)
                                  (cons wires rest-wires)
                                  env-wires)
           (b* ((env-wires (save-wires-to-env-wires val1
                                                    wires
                                                    env-wires)))
             (svl2-save-mod-outputs rest-vals
                                    rest-wires
                                    env-wires)))
    :hints (("Goal"
             :in-theory (e/d (svl2-save-mod-outputs) ())))))


(encapsulate
  nil
  (local
   (in-theory (enable SVL2-MODULE-ALIST-P
                      SVL2-OCC-P
                      SVL2-MODULE-P)))
  
  (define svl2-get-module-rank$ ((modname sv::modname-p)
                                 (modules svl2-module-alist-p))
    (b* ((module (assoc-equal modname modules)))
      (if module
          (nfix (cdr (std::da-nth 0 (cdr module))))
        0)))

  (define svl2-get-max-occ-rank$ ((occs svl2-occ-alist-p)
                                  (modules svl2-module-alist-p))
    (cond ((atom occs)
           0)
          ((equal (car (cdar occs)) ':assign)
           (svl2-get-max-occ-rank$ (cdr occs)
                                   modules))
          (t (max (svl2-get-module-rank$ (STD::DA-NTH 2 (CDR  (cdar occs))) modules)
                  (svl2-get-max-occ-rank$ (cdr occs) modules)))))

  (define svl2-well-ranked-module$ ((modname sv::modname-p)
                                    (modules svl2-module-alist-p)) 
    (and (assoc-equal modname modules)
         (> (svl2-get-module-rank$ modname modules)
            (svl2-get-max-occ-rank$ (CDR (STD::DA-NTH 4
                                                      (cdr (assoc-equal modname modules))))
                                    modules)))))

(memoize 'svl2-well-ranked-module$)

(encapsulate
  nil

  (local
   (defthm svl2-get-module-rank$-is-svl2-get-module-rank
     (implies (and (sv::modname-p modname)
                   (svl2-module-alist-p modules))
              (equal (svl2-get-module-rank$ modname modules)
                     (svl2-get-module-rank modname modules)))
     :hints (("Goal"
              :in-theory (e/d (svl2-get-module-rank$
                               svl2-get-module-rank
                               SVL2-MODULE->RANK) ())))))

  (local
   (defthm svl2-get-max-occ-rank$-is-svl2-get-max-occ-rank
     (implies (and (svl2-occ-alist-p occs)
                   (svl2-module-alist-p modules))
              (equal (svl2-get-max-occ-rank$ occs modules)
                     (svl2-get-max-occ-rank occs modules)))
     :hints (("Goal"
              :do-not-induct t
              :induct (svl2-get-max-occ-rank$ occs modules)
              :in-theory (e/d (svl2-get-max-occ-rank$
                               SVL2-OCC-KIND
                               SV::MODNAME-FIX
                               SVL2-OCC-MODULE->NAME
                               SV::MODNAME-P
                               SVL2-OCC-ALIST-P
                               SVL2-OCC-P
                               svl2-get-max-occ-rank) ())))))

  (local
   (defthm SVL2-MODULE-P-implies
     (implies (SVL2-MODULE-P x)
              (svl2-occ-alist-p (CDR (CADR (CDDDR x)))))
     :hints (("Goal"
              :in-theory (e/d (SVL2-MODULE-P) ())))))

  (local
   (defthm lemma1
     (implies (and (svl2-module-alist-p modules)
                   (ASSOC-EQUAL MODNAME MODULES))
              (SVL2-MODULE-P  (cdr  (ASSOC-EQUAL MODNAME MODULES))))))

  (defthm svl2-well-ranked-module-is-svl2-well-ranked-module$
    (implies (and (sv::modname-p modname)
                  (svl2-module-alist-p modules))
             (equal
              (svl2-well-ranked-module modname modules)
              (svl2-well-ranked-module$ modname modules)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (svl2-well-ranked-module
;SVL2-MODULE-ALIST-P
                              SVL2-MODULE->OCCS
; SVL2-OCC-ALIST-FIX
;SVL2-MODULE-P
                              svl2-well-ranked-module$)
                             ())))))

(def-rw-opener-error
  svl2-run-cycle-opener-error
  (svl2-run-cycle modname inputs delayed-env modules)
  :vars-to-avoid (modules))

(def-rw-opener-error
  svl2-run-cycle-occs-opener-error
  (svl2-run-cycle-occs occs env-wires delayed-env modules)
  :vars-to-avoid (modules
                  env-wires
                  delayed-env))

(acl2::defines
 svl2-run-cycle$
 :flag-defthm-macro defthm-svl2-run-cycle$
 (define svl2-run-cycle$ (modname
                          inputs
                          delayed-env
                          modules)
   :verify-guards nil
   :flag svl2-run-cycle$
   :measure (acl2::nat-list-measure
             (list (svl2-get-module-rank$ modname; (sv::modname-fix modname)
                                          modules;(svl2-module-alist-fix modules)
                                          )
                   (cons-count modname;(sv::modname-fix modname)
                               )))
   :hints (("Goal"
            :in-theory (e/d (rp::measure-lemmas
                             SVL2-GET-MAX-OCC-RANK$
                             SVL2-WELL-RANKED-MODULE$) ())))

   (cond ((not (svl2-well-ranked-module$ modname modules)) ;; for termination
          (mv nil (make-svl-env)))
         (t
          (b* ((x (cdr (assoc-equal modname modules)))
               (env-wires (svl2-start-env (CDR (STD::DA-NTH 1 X)) inputs))
               (env-wires
                (svl-run-add-delayed-ins env-wires delayed-env
                                         (CDR (STD::DA-NTH 2 X))))
               ((mv env-wires next-delayed-env.modules)
                (svl2-run-cycle-occs$ (CDR (STD::DA-NTH 4 X))
                                      env-wires
                                      (svl-env->modules delayed-env)
                                      modules))
               (out-vals (svl2-retrieve-values (CDR (STD::DA-NTH 3 X))
                                               env-wires))
               (next-delayed-env (make-svl-env
                                  :wires (hons-gets-fast-alist
                                          (CDR (STD::DA-NTH 2 X))
                                          env-wires)
                                  :modules next-delayed-env.modules))
               (- (fast-alist-free env-wires)))
            (mv out-vals
                next-delayed-env)))))

 (define svl2-run-cycle-occs$ (occs
                               env-wires
                               delayed-env-alist
                               modules)
   :measure (acl2::nat-list-measure
             (list (svl2-get-max-occ-rank$ occs;(svl2-occ-alist-fix occs)
                                           modules;(svl2-module-alist-fix modules)
                                           )
                   (cons-count occs;(svl2-occ-alist-fix occs)
                               )))
   :flag svl2-run-cycle-occs$
   (let ((occ-name (caar occs))
         (occ (cdar occs)))
     (cond ((atom occs)
            (mv env-wires nil))
           ((equal (car occ) ':assign)
            (b* ((env-wires (hons-acons (STD::DA-NTH 0 (CDR occ))
                                        (svex-eval2 (std::da-nth 1 (cdr occ))
                                                    env-wires)
                                        env-wires)))
              (svl2-run-cycle-occs$ (cdr occs)
                                    env-wires
                                    delayed-env-alist
                                    modules)))
           (t (b* ((mod-input-vals (svexlist-eval2 (STD::DA-NTH 0 (CDR occ))
                                                   env-wires))
                   (mod.delayed-env (entry-svl-env-fix (hons-get occ-name delayed-env-alist)))

                   ((mv mod-output-vals mod-delayed-env)
                    (svl2-run-cycle$ (std::da-nth 2 (cdr occ))
                                     mod-input-vals
                                     mod.delayed-env
                                     modules))
                   (env-wires (svl2-save-mod-outputs mod-output-vals
                                                     (STD::DA-NTH 1 (CDR occ))
                                                     env-wires))
                   ((mv env-wires rest-delayed-env)
                    (svl2-run-cycle-occs$ (cdr occs)
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
  (defthm SVL2-OCC-kind-redef
    (implies (and (SVL2-OCC-P x))
             (equal (svl2-occ-kind x)
                    (car x)))
    :hints (("Goal"
             :in-theory (e/d (svl2-occ-module->inputs
                              SVL2-OCC-KIND
                              SVL2-OCC-P) ())))))

 (local
  (defthm SVL2-OCC-MODULE->INPUTS-redef
    (implies (and (SVL2-OCC-P x)
                  (not (EQUAL (SVL2-OCC-KIND X) :assign)))
             (equal (svl2-occ-module->inputs x)
                    (STD::DA-NTH 0 (CDR X))))
    :hints (("Goal"
             :in-theory (e/d (svl2-occ-module->inputs
                              SVL2-OCC-KIND
                              SVL2-OCC-P) ())))))

 (local
  (defthm SVL2-OCC-MODULE->name-redef
    (implies (and (SVL2-OCC-P x)
                  (not (EQUAL (SVL2-OCC-KIND X) :assign)))
             (equal (SVL2-OCC-MODULE->NAME x)
                    (STD::DA-NTH 2 (CDR X))))
    :hints (("Goal"
             :in-theory (e/d (SVL2-OCC-MODULE->NAME
                              SVL2-OCC-KIND
                              SVL2-OCC-P) ())))))

 (local
  (defthm lemma1
    (implies (and (consp occs)
                  (NOT (EQUAL (CADR (CAR OCCS)) :ASSIGN))
                  (SVL2-OCC-ALIST-P OCCS))
             (and (SVEXLIST-P (CADDR (CAR OCCS)))
                  (SV::MODNAME-P (CAR (CDDDDR (CAR OCCS))))))
    :hints (("Goal"
             :expand (SVL2-OCC-ALIST-P OCCS)
             :do-not-induct t
             :in-theory (e/d (SVL2-OCC-ALIST-P
                              SVL2-OCC-P) ())))))

 (local
  (defthm lemma2
    (implies (and (consp occs)
                  (EQUAL (CADR (CAR OCCS)) :ASSIGN)
                  (SVL2-OCC-ALIST-P OCCS))
             (and (SVEX-P (CADDDR (CAR OCCS)))
                  ))
    :hints (("Goal"
             :expand (SVL2-OCC-ALIST-P OCCS)
             :do-not-induct t
             :in-theory (e/d (SVL2-OCC-ALIST-P
                              SVL2-OCC-P) ())))))

 (local
  (defthm SVL2-OCC-MODULE->outputs-redef
    (implies (and (SVL2-OCC-P x)
                  (not (EQUAL (SVL2-OCC-KIND X) :assign)))
             (equal (svl2-occ-module->outputs x)
                    (STD::DA-NTH 1 (CDR X))))
    :hints (("Goal"
             :in-theory (e/d (SVL2-OCC-MODULE->OUTPUTS
                              SVL2-OCC-KIND
                              SVL2-OCC-P) ())))))

 (local
  (defthm SVL2-OCC-ASSIGN-redef
    (implies (and (SVL2-OCC-P x)
                  (EQUAL (SVL2-OCC-KIND X) :assign))
             (and (equal (SVL2-OCC-ASSIGN->OUTPUT x)
                         (STD::DA-NTH 0 (CDR X)))
                  (equal (SVL2-OCC-ASSIGN->svex x)
                         (STD::DA-NTH 1 (CDR X)))))
    :hints (("Goal"
             :in-theory (e/d (SVL2-OCC-ASSIGN->OUTPUT
                              SVL2-OCC-ASSIGN->svex
                              SVL2-OCC-KIND
                              SVL2-OCC-P) ())))))

 (defthm wire-list-fix-def
   (implies (wire-list-p x)
            (equal (wire-list-fix x)
                   x)))

 (local
  (defthm SVL2-MODULE->OUTPUTS-redef
    (implies (SVL2-MODULE-P x)
             (equal (SVL2-MODULE->OUTPUTS x)
                    (CDR (STD::DA-NTH 3 X))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (SVL2-MODULE->OUTPUTS
                              SVL2-MODULE-P) ())))))

 (local
  (defthm SVL2-MODULE->occs-redef
    (implies (SVL2-MODULE-P x)
             (equal (SVL2-MODULE->occs x)
                    (CDR (STD::DA-NTH 4 X))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (SVL2-MODULE->occs
                              SVL2-MODULE-P) ())))))

 (local
  (defthm SVL2-MODULE->inputs-redef
    (implies (SVL2-MODULE-P x)
             (equal (SVL2-MODULE->inputs x)
                    (CDR (STD::DA-NTH 1 X))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (SVL2-MODULE->inputs
                              SVL2-MODULE-P) ())))))

 (local
  (defthm SVL2-MODULE->delayed-inputs-redef
    (implies (SVL2-MODULE-P x)
             (equal (SVL2-MODULE->delayed-inputs x)
                    (CDR (STD::DA-NTH 2 X))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (SVL2-MODULE->delayed-inputs
                              SVL2-MODULE-P) ())))))

 (local
  (defthm SVL2-WELL-RANKED-MODULE$-implies
    (implies (SVL2-WELL-RANKED-MODULE$ x y)
             (assoc-equal x y))
    :hints (("Goal"
             :in-theory (e/d (SVL2-WELL-RANKED-MODULE$) ())))))

 (local
  (defthm SVL2-MODULE-P-of-assoc-equal
    (implies (and (SVL2-MODULE-ALIST-P MODULES)
                  (ASSOC-EQUAL MODNAME MODULES))
             (SVL2-MODULE-P (CDR (ASSOC-EQUAL MODNAME MODULES))))
    :hints (("Goal"
             :do-not-induct t
             :induct (ASSOC-EQUAL MODNAME MODULES)
             :in-theory (e/d (SVL2-WELL-RANKED-MODULE$
                              SVL2-MODULE-ALIST-P) ())))))

 (local
  (defthm lemma3
    (implies (SVL2-MODULE-P module)
             (and (SVL2-OCC-ALIST-P (CDR (CADR (CDDDR module))))
                  (WIRE-LIST-P (CDR (Cadr module)))))
    :hints (("Goal"
             :in-theory (e/d (SVL2-MODULE-P) ())))))

 (local
  (defthm lemma4
    (implies (and (SVL2-OCC-ALIST-P OCCS)
                  (EQUAL (CADR (CAR OCCS)) :ASSIGN))
             (SV::SVAR-P (CADDR (CAR OCCS))))
    :hints (("Goal"
             :expand (SVL2-OCC-ALIST-P OCCS)
             :in-theory (e/d (SVL2-OCC-P) ())))))

 (local
  (defthm lemma5
    (implies (and (CONSP OCCS)
                  (NOT (EQUAL (CADR (CAR OCCS)) :ASSIGN))
                  (SVL2-OCC-ALIST-P OCCS))
             (WIRE-LIST-LISTP (CADDDR (CAR OCCS))))
    :hints (("Goal"
             :expand (SVL2-OCC-ALIST-P OCCS)
             :in-theory (e/d (SVL2-OCC-P) ())))))
                  

 (defthm-svl2-run-cycle$
   (defthm svl2-run-cycle-is-svl2-run-cycle$
     (implies (and (sv::modname-p modname)
                   (sv::4veclist-p inputs)
                   (svl-env-p delayed-env)
                   (svl2-module-alist-p modules))
              (equal (svl2-run-cycle modname inputs delayed-env modules)
                     (svl2-run-cycle$ modname inputs delayed-env modules)))
     :flag svl2-run-cycle$)

   (defthm svl2-run-cycle-occs-is-svl2-run-cycle-occs$
     (implies (and (svl2-occ-alist-p occs)
                   (sv::svex-env-p env-wires)
                   (svl-env-alist-p delayed-env-alist)
                   (svl2-module-alist-p modules))
              (equal (svl2-run-cycle-occs occs env-wires delayed-env-alist modules)
                     (svl2-run-cycle-occs$ occs env-wires delayed-env-alist modules)))
     :flag svl2-run-cycle-occs$)
   :hints (("Goal"
            :expand ((SVL2-RUN-CYCLE-OCCS OCCS
                                          ENV-WIRES DELAYED-ENV-ALIST MODULES)
                     (SVL2-RUN-CYCLE-OCCS$ OCCS
                                           ENV-WIRES DELAYED-ENV-ALIST MODULES)
                     (SVL2-RUN-CYCLE MODNAME INPUTS DELAYED-ENV MODULES)
                     )
            :in-theory (e/d (svexlist-eval2-is-svexlist-eval
                             svl2-run-cycle
                             svl2-run-cycle$
                             SVL2-RUN-CYCLE-OCCS$
                             svl2-run-cycle-occs) ())))))



(progn
  (def-rw-opener-error
    svl2-run-cycle$-opener-error
    (svl2-run-cycle$ modname inputs
                     delayed-env
                     modules)
    :vars-to-avoid (modules))

  (rp::defthm-lambda
   svl2-run-cycle$-opener
   (implies
    (svl2-well-ranked-module$ modname modules)
    (equal (svl2-run-cycle$ modname inputs
                            delayed-env
                            modules)
           (b* ((x (cdr (assoc-equal modname modules)))
                (- (cw "Using svl2-run-cycle$-opener for ~p0 ~%"
                       modname))
                (env-wires (svl-run-add-delayed-ins
                                        (svl2-start-env (CDR (STD::DA-NTH 1 X)) inputs)
                                        delayed-env
                                        (CDR (STD::DA-NTH 2 X))))
                ((mv env-wires next-delayed-env.modules)
                 (svl2-run-cycle-occs$ (CDR (STD::DA-NTH 4 X))
                                       env-wires
                                       (svl-env->modules delayed-env)
                                       modules))
                (out-vals (svl2-retrieve-values (CDR (STD::DA-NTH 3 X))
                                                env-wires))
                (next-delayed-env (make-svl-env
                                   :wires (hons-gets-fast-alist
                                           (CDR (STD::DA-NTH 2 X))
                                           env-wires)
                                   :modules next-delayed-env.modules))
                (- (fast-alist-free env-wires)))
             (mv out-vals
                 next-delayed-env))))
   :hints (("Goal"
            :expand (svl2-run-cycle$ modname inputs
                                     delayed-env
                                     modules)
            :in-theory (e/d () ())))))

(progn
  (def-rw-opener-error
    svl2-run-cycle-occs$-opener-error
    (svl2-run-cycle-occs$ occs env-wires delayed-env-alist modules)
    :vars-to-avoid (env-wires))

  (defthm svl2-run-cycle-occs$-opener-nil
    (equal (svl2-run-cycle-occs$ nil env-wires delayed-env-alist modules)
           (mv env-wires nil))
    :hints (("Goal"
             :expand (svl2-run-cycle-occs$ nil env-wires delayed-env-alist modules)
             :in-theory (e/d () ()))))

  (defthm svl2-run-cycle-occs$-opener-cons-assign
    (equal (svl2-run-cycle-occs$
            (cons (cons occ-name (cons ':assign cdr-occ)) rest)
            env-wires delayed-env-alist modules)
           (b* ((env-wires (hons-acons (STD::DA-NTH 0 cdr-occ)
                                       (svex-eval2 (std::da-nth 1 cdr-occ)
                                                   env-wires)
                                       env-wires)))
             (svl2-run-cycle-occs$ rest
                                   env-wires
                                   delayed-env-alist
                                   modules)))
    :hints (("Goal"
             :expand (svl2-run-cycle-occs$
                      (cons (cons occ-name (cons ':assign cdr-occ)) rest)
                      env-wires delayed-env-alist modules)
             :in-theory (e/d () ()))))

  (defthm-lambda svl2-run-cycle-occs$-opener-cons-module
    (equal (svl2-run-cycle-occs$
            (cons (cons occ-name (cons ':module cdr-occ)) rest)
            env-wires delayed-env-alist modules)
           (b* (((mv mod-output-vals mod-delayed-env)
                 (svl2-run-cycle$ (std::da-nth 2 cdr-occ)
                                  (svexlist-eval2 (STD::DA-NTH 0 cdr-occ)
                                                env-wires)
                                  (entry-svl-env-fix (hons-get occ-name delayed-env-alist))
                                  modules))
                ((mv env-wires rest-delayed-env)
                 (svl2-run-cycle-occs$ rest
                                       (svl2-save-mod-outputs mod-output-vals
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
             :expand (svl2-run-cycle-occs$
                      (cons (cons occ-name (cons ':module cdr-occ)) rest)
                      env-wires delayed-env-alist modules)
             :in-theory (e/d () ())))))
