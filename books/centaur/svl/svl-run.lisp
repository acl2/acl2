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

(include-book "type-defs")

(include-book "bits-sbits-defs")

(include-book "svex-eval-wog")


(local
 (defthm natp-implied-4vec-p
   (implies (natp x)
            (4vec-p x))
   :hints (("Goal"
            :in-theory (e/d (4vec-p)
                            ())))
   :rule-classes :type-prescription))


(define entry-4vec-fix (entry)
  :guard (or (consp entry)
             (not entry))
  :enabled t
  (if entry
      (cdr entry)
    (sv::4vec-x))
  ///
  (add-rp-rule entry-4vec-fix))

(define save-wires-to-env-wires ((val sv::4vec-p)
                                 (wires wire-list-p)
                                 (env-wires sv::svex-env-p))
  :returns (res sv::svex-env-p
                :hyp (and (sv::4vec-p val)
                          (wire-list-p wires)
                          (sv::svex-env-p env-wires)))
  :verify-guards nil
  (if (atom wires)
      env-wires
    (b* ((wire (car wires))
         (old-val-entry (hons-get (wire-name wire) env-wires)))
      (case-match wire
        ((& w . s) (hons-acons
                    (wire-name wire)
                    (sbits s w val (entry-4vec-fix old-val-entry))
                    (save-wires-to-env-wires (4vec-rsh w val)
                                             (cdr wires)
                                             env-wires)))
        (& (hons-acons
            (wire-name wire)
            val
            env-wires)))))
  ///

  (local
   (defthm lemma
     (IMPLIES (AND
               (WIRE-LIST-P WIRES)
               (CONSP WIRES)
               (CONSP (CAR WIRES))
               (CONSP (CDR (CAR WIRES))))
              (4VEC-P (CADR (CAR WIRES))))
     :hints (("Goal"
              :in-theory (e/d (wire-list-p 4vec-p
                                           sv::svar-p) ())))))

  (verify-guards save-wires-to-env-wires ))

(progn
  (define svl-get-module-rank ((modname sv::modname-p)
                               (modules svl-module-alist-p))
    :returns (res natp)
    (b* ((module (assoc-equal modname modules)))
      (if module
          (nfix (svl-module->rank (cdr module)))
        0)))

  (define svl-get-max-occ-rank ((occs svl-occ-alist-p)
                                (modules svl-module-alist-p))
    :returns (res natp)
    (cond ((atom occs)
           0)
          ((equal (svl-occ-kind (cdar occs)) ':assign)
           (svl-get-max-occ-rank (cdr occs)
                                 modules))
          (t (max (svl-get-module-rank (svl-occ-module->name (cdar occs)) modules)
                  (svl-get-max-occ-rank (cdr occs) modules)))))

  (define svl-well-ranked-module ((modname sv::modname-p)
                                  (modules svl-module-alist-p))
    (and (or (assoc-equal modname modules)
             (cw "Module ~p0 is not found in the given svl-module-alist ~%."
                 modname))
         (> (svl-get-module-rank modname modules)
            (svl-get-max-occ-rank (svl-module->occs
                                   (cdr (assoc-equal modname modules)))
                                  modules)))))

(define svl-start-env ((wires wire-list-p)
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
     (svl-start-env (cdr wires) (cdr vals)))))

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

(define svl-retrieve-values ((wires wire-list-p)
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
            (svl-retrieve-values (cdr wires)
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



(define svl-save-mod-outputs ((vals sv::4veclist-p)
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
      (svl-save-mod-outputs (cdr vals)
                            (cdr wire-list-list)
                            env-wires))))

(memoize 'svl-module-alist-p)
(memoize 'svl-well-ranked-module)

(define create-next-env-for-wires ((delayed-ins SV::SVARLIST-P)
                                   (env-wires sv::svex-env-p))
  :returns (res sv::svex-env-p
                :hyp (and (SV::SVARLIST-P delayed-ins)
                          (sv::svex-env-p env-wires)))
  (if (atom delayed-ins)
      nil
    (b* ((cur (car delayed-ins))
         (cur- (sv::change-svar cur :delay 0)) ;; read the value from evn-wires
         ;; by converting the delay to 0, but save with delay=1
         (val (entry-4vec-fix (hons-get cur- env-wires))))
      (acons cur
             val
             (create-next-env-for-wires (cdr delayed-ins)
                                        env-wires)))))

(define svex-env-append ((lst1 sv::svex-env-p)
                         (lst2 sv::svex-env-p))
  :returns (res sv::svex-env-p
                :hyp (and (sv::svex-env-p lst1)
                          (sv::svex-env-p lst2)))
  (if (atom lst1)
      lst2
    (hons-acons (caar lst1)
                (cdar lst1)
                (svex-env-append (cdr lst1) lst2))))

(acl2::defines
 svl-run-phase
 (define svl-run-phase ((modname sv::modname-p "Name of the module to run")
                        (inputs sv::4veclist-p "Values of the inputs as a list")
                        (delayed-env svl-env-p "Environment from the previos
 phase for state holding components")
                        (modules svl-module-alist-p "The constant SVL-design instance"))
   :verify-guards nil

   ;; :guard (and (assoc-equal modname modules)
   ;;             (svl-well-ranked-module modname modules))


   :parents (svl-run)
   :short "Run a single phase of @(see svl::svl-run)"
   :long "<p> The @(see svl::svl-run) function operates on phases as defined by
the input bindings alits (input simulation pattern). SVL-RUN-PHASE is the
function to run each each phase for each module. </p>

<p> 'inputs' arguments should be a list of the concrete (for execution) or
variables (for proofs). The order of inputs are determined by their order in
the SVL-design entry. </p>

<p> 'delayed-env' is a special structure for state holding elements. If the
user is dealing with sequential circuit designs, then it is recommended to use
@(see svl::svl-run) instead. @(see svl::svl-run) can be used for combinational
circuits as well. If you would like to use svl-run-phase on combinational
circuits, then you can pass '(nil nil) or (svl::make-svl-env) for
delayed-env. This designates empty state. </p>

<p> svl-run-phase might be too slow to use for proofs. You can use @(see
svl-run-phase-wog) instead, which has the same arguments but no guards.
</p>
"
   :measure (acl2::nat-list-measure
             (list (svl-get-module-rank modname modules)
                   (cons-count (sv::modname-fix modname))))
   :hints (("Goal"
            :in-theory (e/d (rp::measure-lemmas
                             SVL-GET-MAX-OCC-RANK
                             SVL-MODULE->OCCS
                             SV::MODNAME-FIX
                             SVL-WELL-RANKED-MODULE
                             svl-occ-module->name) ())))

   :returns (mv (out-vals sv::4veclist-p
                          :hyp (and (sv::4veclist-p inputs)
                                    (svl-env-p delayed-env)
                                    (svl-module-alist-p modules)))
                (next-delayed-env svl-env-p
                                  :hyp (and (sv::4veclist-p inputs)
                                            (svl-env-p delayed-env)
                                            (svl-module-alist-p modules))))
   (cond ((not (svl-well-ranked-module modname modules)) ;; for termination
          (mv
           (cw "Either Module ~p0 is missing or it has invalid ranks~%"
               modname)
           (make-svl-env)))
         (t
          (b* (((svl-module module) (cdr (assoc-equal modname modules)))
               (env-wires (svl-start-env module.inputs inputs))
               (env-wires
                (svex-env-append (svl-env->wires delayed-env)
                                 env-wires))
               ((mv env-wires next-delayed-env.modules)
                (svl-run-phase-occs module.occs
                                    env-wires
                                    (svl-env->modules delayed-env)
                                    modules))
               (out-vals (svl-retrieve-values module.outputs
                                              env-wires))
               (next-delayed-env (make-svl-env
                                  :wires (create-next-env-for-wires
                                          module.delayed-inputs
                                          env-wires)
                                  :modules next-delayed-env.modules))
               (- (fast-alist-free env-wires)))
            (mv out-vals
                next-delayed-env)))))

 (define svl-run-phase-occs ((occs svl-occ-alist-p)
                             (env-wires sv::svex-env-p)
                             (delayed-env-alist svl-env-alist-p)
                             (modules svl-module-alist-p))
   :measure (acl2::nat-list-measure
             (list (svl-get-max-occ-rank occs modules)
                   (cons-count occs)))

   :returns (mv (res-env-wires sv::svex-env-p :hyp (and (svl-occ-alist-p occs)
                                                        (sv::svex-env-p env-wires)
                                                        (svl-env-alist-p delayed-env-alist)
                                                        (svl-module-alist-p modules)))
                (next-delayed-env.modules SVL-ENV-ALIST-P
                                          :hyp (and (svl-occ-alist-p occs)
                                                    (sv::svex-env-p env-wires)
                                                    (svl-env-alist-p delayed-env-alist)
                                                    (svl-module-alist-p modules))))

   (let ((occ-name (caar occs))
         (occ (cdar occs)))
     (cond ((atom occs)
            (mv env-wires nil))
           ((equal (svl-occ-kind occ) ':assign)
            (b* ((env-wires (hons-acons (svl-occ-assign->output occ)
                                        (mbe :logic (svex-eval-wog (svl-occ-assign->svex occ)
                                                                   env-wires)
                                             :exec (svex-eval (svl-occ-assign->svex occ)
                                                              env-wires))
                                        env-wires)))
              (svl-run-phase-occs (cdr occs)
                                  env-wires
                                  delayed-env-alist
                                  modules)))
           (t (b* ((mod-input-vals (mbe :logic
                                        (svexlist-eval-wog (svl-occ-module->inputs occ)
                                                           env-wires)
                                        :exec
                                        (sv::svexlist-eval (svl-occ-module->inputs occ)
                                                           env-wires)))
                   (mod.delayed-env (entry-svl-env-fix (hons-get occ-name delayed-env-alist)))
                   ((mv mod-output-vals mod-delayed-env)
                    (svl-run-phase (svl-occ-module->name occ)
                                   mod-input-vals
                                   mod.delayed-env
                                   modules))
                   (env-wires (svl-save-mod-outputs mod-output-vals
                                                    (svl-occ-module->outputs  occ)
                                                    env-wires))
                   ((mv env-wires rest-delayed-env)
                    (svl-run-phase-occs (cdr occs)
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

 #|(local
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
 ())))))||#

 (local
  (defthm guard-lemma1
    (implies (and (SVL-MODULE-ALIST-P modules)
                  (ASSOC-EQUAL MODNAME MODULES))
             (and (SVL-MODULE-P (CDR (ASSOC-EQUAL MODNAME MODULES)))
                  (CONSP (ASSOC-EQUAL MODNAME MODULES))))
    :hints (("Goal"
             :in-theory (e/d (SVL-MODULE-ALIST-P) ())))))

 (verify-guards svl-run-phase-occs
   :otf-flg t
   :hints (("Goal"
            :in-theory (e/d (svexlist-eval-wog-is-svexlist-eval
                             SVEX-EVAL-IS-SVEX-EVAL-WOG
                             svl-well-ranked-module)
                            ())))))

(defmacro svl-run-cycle (modnames inputs
                                  delayed-env
                                  modules)
  `(svl-run-phase ,modnames ,inputs ,delayed-env
                  ,modules))

(defmacro svl-run-cycle-occs (occs
                              env-wires
                              delayed-env-alist
                              modules)
  `(svl-run-phase-occs ,occs ,env-wires
                       ,delayed-env-alist
                       ,modules))

(local
 (defthm consp-assoc-equal-in-iff-context
   (implies (alistp x)
            (iff (consp (assoc-equal key x))
                 (assoc-equal key x)))))

(encapsulate
  nil

  ;; Functions to parse input signal bindings across phases.
  ;; For example:
  ;; (defconst *counter-inputs*
  ;; `(("Clock" 0 ~)
  ;;   ("Reset" 1 1 0 0 1)
  ;;   ("Enable" 0 0 0 0 0 0)
  ;;   ("Load" 0 0 _ _ 0)
  ;;   ("Mode" 0 0 0 1)
  ;;   ("Data[8:0]" data8-10 _ _ data8-12)
  ;;   ("Data[63:9]" data-rest)))
  ;; is parsed and a list of list is created.
  ;; The inner lists contain inputs as svex'es when svl-run-cycle is to be
  ;; called at each cycle.
  ;; the outer list is as long as the total number of phases.

  ;; All the functions in this encapsulation will be executed.

  (define s-equal ((x)
                   (y))
    :inline t
    "Convert symbols into strings when checking equality to get rid of package"
    (equal (if (symbolp x) (symbol-name x) x)
           (if (symbolp y) (symbol-name y) y)))

  (define get-max-len (lsts)
    :returns (res natp)
    (if (atom lsts)
        0
      (max (len (car lsts))
           (get-max-len (cdr lsts)))))

  (progn
    (define svl-run-fix-inputs_phases-aux ((cur)
                                           (phase-cnt natp)
                                           (last))
      (cond ((zp phase-cnt) nil)
            ((atom cur)
             (cons last
                   (svl-run-fix-inputs_phases-aux cur
                                                  (1- phase-cnt)
                                                  last)))
            ((s-equal (car cur) '~)
             (cond ((equal last '0)
                    (cons 1
                          (svl-run-fix-inputs_phases-aux cur
                                                         (1- phase-cnt)
                                                         1)))
                   ((equal last '1)
                    (cons 0
                          (svl-run-fix-inputs_phases-aux cur
                                                         (1- phase-cnt)
                                                         0)))
                   ((s-equal last '_)
                    (cons '_
                          (svl-run-fix-inputs_phases-aux cur
                                                         (1- phase-cnt)
                                                         '_)))
                   (t
                    (cons `(sv::bitnot ,last)
                          (svl-run-fix-inputs_phases-aux cur
                                                         (1- phase-cnt)
                                                         `(sv::bitnot
                                                           ,last))))))
            (t
             (cons (cond ((s-equal (car cur) '_)
                          (sv::4vec-x))
                         (t (car cur)))
                   (svl-run-fix-inputs_phases-aux (cdr cur)
                                                  (1- phase-cnt)
                                                  (car cur))))))


    (define svl-run-fix-inputs_phases ((sig-binds)
                                       (phase-cnt natp))
      (if (atom sig-binds)
          nil
        (cons (svl-run-fix-inputs_phases-aux (car sig-binds)
                                             phase-cnt
                                             '_)
              (svl-run-fix-inputs_phases (cdr sig-binds)
                                         phase-cnt)))))

  (define get-substr ((str stringp)
                      (start natp)
                      (size natp))
    (b* ((chars (take (+ start size) (explode str)))
         (chars (nthcdr start chars)))
      (if (character-listp chars)
          (coerce chars 'string)
        "")))

  (define svl-run-simplify-signame ((signame stringp))
    (b* ((pos-of-[ (str::strpos "[" signame))
         (pos-of-colon (str::strpos ":" signame))
         (pos-of-] (str::strpos "]" signame)))
      (if (and pos-of-[
               pos-of-colon
               pos-of-])
          (b* ((pos1 (explode
                      (get-substr signame
                                  (nfix (1+ pos-of-[))
                                  (nfix (+ pos-of-colon (- pos-of-[) -1)))))
               (pos2 (explode
                      (get-substr signame
                                  (nfix (1+ pos-of-colon))
                                  (nfix (+ pos-of-] (- pos-of-colon) -1)))))
               ((unless (and (str::dec-digit-char-listp pos1)
                             (str::dec-digit-char-listp pos2)))
                (progn$
                 (hard-error 'svl-run-simplify-signame
                             "~p0 has an unexpected structure. It should be ~
    e.g., \"sig[32:0]\" or \"sig\""
                             (list (cons #\0 signame)))
                 (mv signame nil nil))))
            (mv (get-substr signame 0 pos-of-[)
                (Str::dec-digit-chars-value pos1)
                (str::dec-digit-chars-value pos2)))
        (mv signame nil nil))))



  (progn
    (define svl-run-fix-inputs_merge-aux (old-binds new-binds start size)

      (if (atom new-binds)
          nil
        (b* ((old-val (if (atom old-binds) (sv::4vec-x) (car old-binds)))
             (new-bind (car new-binds)))
          (cons `(sv::partinst ,start ,size ,old-val ,new-bind)
                (svl-run-fix-inputs_merge-aux (if (atom old-binds) nil (cdr old-binds))
                                              (cdr new-binds)
                                              start size)))))

    (define svl-run-fix-inputs_merge ((signames string-listp)
                                      (sig-binds))
      :verify-guards nil
      :returns (res alistp)
      (if (or (atom signames)
              (atom sig-binds))
          nil
        (b* ((rest (svl-run-fix-inputs_merge (cdr signames)
                                             (cdr sig-binds)))
             ((mv name b1 b2)
              (svl-run-simplify-signame (car signames))))
          (cond ((and (natp b1) (natp b2))
                 (b* (((mv b1 b2) (if (> b2 b1) (mv b2 b1) (mv b1 b2)))
                      (start b2)
                      (size (+ b1 (- b2) 1))
                      (old-assign (assoc-equal name rest))
                      (new-binds (svl-run-fix-inputs_merge-aux (cdr old-assign)
                                                               (car sig-binds)
                                                               start
                                                               size)))
                   (put-assoc-equal name new-binds rest)))
                (t
                 (acons (car signames) (car sig-binds) rest)))))
      ///
      (verify-guards svl-run-fix-inputs_merge)))


  (define svl-run-fix-inputs ((sig-bind-alist alistp))
    ;; in case an input sig-bind-alist has a key of the form "Data[8:0]"
    ;; merge it to a single binding "Data".
    ;; Also extend "~" and unfinished bindings.
    :guard (and (string-listp (strip-cars sig-bind-alist)))
    :returns (res alistp :hyp (alistp sig-bind-alist))
    (b* ((sig-names (strip-cars sig-bind-alist))
         (sig-binds (strip-cdrs sig-bind-alist))
         (phase-cnt (get-max-len sig-binds))
         (sig-binds (svl-run-fix-inputs_phases sig-binds phase-cnt))
         (sig-bind-alist (svl-run-fix-inputs_merge sig-names sig-binds)))
      sig-bind-alist))



  (define svl-generate-inputs_fixorder ((sig-bind-alist alistp)
                                        (wire-names ))
    :returns (res alistp :hyp (alistp sig-bind-alist))
    (if (atom wire-names)
        nil
      (b* ((entry (assoc-equal (car wire-names) sig-bind-alist))
           (rest (svl-generate-inputs_fixorder sig-bind-alist
                                               (cdr wire-names))))
        (if entry
            (cons entry rest)
          (progn$ (cw "Warning! Input ~p0 does not have an assigned value. ~%"
                      (car wire-names))
                  (acons
                   (car wire-names)
                   (repeat (len (cdar sig-bind-alist))
                           (sv::4vec-x))
                   rest))))))

  (define strip-cars$ (x)
    (cond
     ((atom x) nil)
     (t (cons (if (consp (car x))
                  (car (car x))
                nil)
              (strip-cars$ (cdr x))))))

  (define strip-cdrs$ (x)
    (cond
     ((atom x) nil)
     (t (cons (if (consp (car x))
                  (cdr (car x))
                nil)
              (strip-cdrs$ (cdr x))))))

  (define transpose (x)
    :hints (("Goal"
             :in-theory (e/d (strip-cdrs$ strip-cars$) ())))
    (if (or (atom x)
            (atom (car x)))
        nil
      (cons (strip-cars$ x)
            (transpose (strip-cdrs$ x)))))

  (define svl-generate-inputs ((sig-bind-alist alistp)
                               (input-wires wire-list-p))
    :guard (and (string-listp (strip-cars sig-bind-alist)))
    (b* ((sig-bind-alist (svl-run-fix-inputs sig-bind-alist))
         (sig-bind-alist (svl-generate-inputs_fixorder
                          sig-bind-alist (strip-cars input-wires)))
         (inputs (transpose (strip-cdrs sig-bind-alist))))
      inputs)))




;; save the output in an alist according to out-bind-alist
(define svl-run-save-output ((out-alist sv::svex-env-p)
                             (out-bind-alist alistp))
  :verify-guards nil
  :returns (mv (res1 alistp)
               (res2 alistp))
  :guard (string-listp (strip-cars out-bind-alist))
  ;;:verify-guards nil
  (if (atom out-bind-alist)
      (mv nil nil)
    (b* (((mv rest-outputs rest-out-bind-alist)
          (svl-run-save-output out-alist (cdr out-bind-alist)))
         (this (car out-bind-alist))
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
  ///

  (local
   (defthm svex-env-p-returns-4vec-p
     (implies (and (sv::svex-env-p env)
                   (assoc-equal key env))
              (4vec-p (cdr (assoc-equal key env))))))

  (verify-guards svl-run-save-output
    :hints (("Goal"
             :in-theory (e/d () ())))))

(local
 (defthm svl-run-save-output-returns-string-alistp
   (implies (string-listp (strip-cars out-bind-alist))
            (string-listp (strip-cars (mv-nth 1 (svl-run-save-output out-alist
                                                                     out-bind-alist)))))
   :hints (("Goal"
            :in-theory (e/d (svl-run-save-output) ())))))

(encapsulate
  nil

  (define pairlis3 (x y)
    (if (or (atom x)
            (atom y))
        nil
      (acons (car x) (car y)
             (pairlis3 (cdr x) (cdr y)))))

  (local
   (defthm svex-env-p-of-parlis3
     (implies (and (sv::svarlist-p x)
                   (sv::4veclist-p y))
              (sv::svex-env-p (pairlis3 x y)))
     :hints (("Goal"
              :in-theory (e/d (sv::svex-env-p
                               pairlis3
                               sv::svar-p)
                              ())))))

  (local
   (defthm alistp-append
     (implies (and (alistp x)
                   (alistp y))
              (alistp (append x y)))))

  (define svl-run-aux ((modname sv::modname-p)
                       (inputs 4vec-list-listp)
                       (out-wires sv::svarlist-p)
                       (out-bind-alist alistp)
                       (delayed-env svl-env-p)
                       (modules svl-module-alist-p))
    :guard (string-listp (strip-cars out-bind-alist))
    :returns (res alistp)
    (if (atom inputs)
        (progn$ ;(svl-free-env modname delayed-env modules (expt 2 30))
         nil)
      (b* (((mv out-vals next-delayed-env)
            (svl-run-phase modname (car inputs) delayed-env modules))
           (out-alist (pairlis3 out-wires out-vals))
           ((mv outputs out-bind-alist) (svl-run-save-output out-alist out-bind-alist))
           (rest (svl-run-aux modname (cdr inputs) out-wires out-bind-alist next-delayed-env modules)))
        (append outputs rest))))

  (local
   (defthm svl-run-guard-lemma1
     (implies (and (wire-list-p x))
              (sv::svarlist-p (strip-cars x)))
     :hints (("goal"
              :in-theory (e/d (svl-module->outputs
                               svl-module-alist-p
                               sv::svarlist-p
                               wire-list-p
                               wire-list-fix)
                              ())))))

  (local
   (defthm svl-run-guard-lemma2
     (implies (and (svl-module-alist-p modules)
                   (assoc-equal modname modules))
              (svl-module-p (cdr (assoc-equal modname modules))))
     :hints (("goal"
              :in-theory (e/d (svl-module->outputs
                               svl-module-alist-p
                               sv::svarlist-p
                               wire-list-p
                               wire-list-fix)
                              ())))))

  (local
   (defthm wire-listp-implies-alistp
     (implies (and
               (wire-list-p wires))
              (alistp wires))
     :rule-classes :type-prescription))

  (define svl-run ((modname sv::modname-p)
                   (inputs-env sv::svex-env-p) ;; needs to be fast-alist
                   (ins-bind-alist alistp) ;; a constant to tell what input
                   ;; signal should be assigned to what and when
                   (out-bind-alist alistp) ;; same as above but for outputs
                   (modules svl-module-alist-p))
    :guard (and (string-listp (strip-cars out-bind-alist))
                (string-listp (strip-cars ins-bind-alist)))
    :returns (res alistp)
    :parents (acl2::svl)
    :short "Evaluate SVL designs"
    :long "<p>SVL-RUN has similar inputs to (@see acl2::def-svtv). However, some
of those inputs (i.e., simulation patterns) are supplied to svl-run at runtime
(or during the proofs). </p>

<ul>
<li>modname: Name of the module to run.</li>
<li>inputs-env: An alist that binds input wires to concrete values (during
execution) or variables (during proofs).</li>
<li>ins-bind-alist: the simulation pattern for inputs. It should be an alist,
an example is given below. </li>
<li>out-bind-alist: same as ins-bind-alist but for outputs instead.</li>
</ul>

<p>
For example:
</p>
<code>
@('
(defconst *counter-input-binds-alist*
   `((\"Clock\" 0 ~)
     (\"Reset\" 1 1 1 1 1)
     (\"Enable\" 0 0 0 0 0 0 0 0 0 0)
     (\"Load\" 0 1)
     (\"Mode\" 0)
     (\"Data[8:0]\" data8-10)
     (\"Data[63:9]\" data-rest)))
')
</code>
<code>
@('
   (defconst *counter-outputs*
     `((\"Count[31:0]\" count_low1 _ _ _ _ _ _ _ _ _ count_low8 _ count_low10)
       (\"Count[63:32]\" count_high1 _ _ _ count_high2)))
')
</code>

<code>
@('
(svl-run \"COUNTER\"
         (make-fast-alist '((count_low1 . -5)
                            (count_low8 . 5)
                            (count_low10 . 10)))
         *counter-input-binds-alist*
         *counter-outputs*
         *counter-svl-design*)))
')
</code>
"
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
      (svl-run-aux modname inputs output-wires out-bind-alist (make-svl-env) modules))))


;; :i-am-here

;; (include-book "/Users/user/async/fft/svl-tests/svl-tests")

;; ;;*counter-svl-design*

;; (progn
;;   (defconst *counter-inputs*
;;     `(("Clock" 0 ~)
;;       ("Reset" 1 1 1 1 1)
;;       ("Enable" 0 0 0 0 0 0 0 0 0 0)
;;       ("Load" 0 1)
;;       ("Mode" 0)
;;       ("Data[8:0]" data8-10)
;;       ("Data[63:9]" data-rest)))

;;   (defconst *counter-outputs*
;;     `(("Count[31:0]" count_low1 _ _ _ count_low2 count_low3 count_low4
;;        count_low5 count_low6 count_low7 count_low8 count_low9 count_low10)
;;       ("Count[63:32]" count_high1 _ _ _ count_high2)))

;;   (value-triple (svl-run "COUNTER" (make-fast-alist '((data8-10 . -5)
;;                                                        (data8-12 . 5)
;;                                                        (data-rest . 10)))
;;                           *counter-inputs*
;;                           *counter-outputs*
;;                           *counter-svl-design*)))

;; :i-am-here
#|
(make-event
(b* ((modnames '("full_adder_1$WIDTH=1"
"full_adder$WIDTH=1"
"booth2_reduction_dadda_17x65_97"
"booth2_multiplier_signed_64x32_97"))
((mv modules rp::rp-state)
(svl-flatten-design modnames
*big-sv-design*
*big-vl-design2*)))
(mv nil
`(defconst *big-svl-design*
',modules)
state
rp::rp-state)))

(make-event
(b* ((modnames '("FullAdder" "LF_127_126" "HalfAdder"))
((mv modules rp::rp-state)
(svl-flatten-design modnames
*signed64-sv-design*
*signed64-vl-design2*)))
(mv nil
`(defconst *signed64-svl-design*
',modules)
state
rp::rp-state)))

(make-event
(b* ((modnames '("FullAdder" "LF_255_254" "HalfAdder"))
((mv modules rp::rp-state)
(svl-flatten-design modnames
*signed128-sv-design*
*signed128-vl-design2*)))
(mv nil
`(defconst *signed128-svl-design*
',modules)
state
rp::rp-state)))

(make-event
(b* ((modnames '("FullAdder" "BK_511_510" "HalfAdder"))
((mv modules rp::rp-state)
(svl-flatten-design modnames
*signed256-sv-design*
*signed256-vl-design2*)))
(mv nil
`(defconst *signed256-svl-design*
',modules)
state
rp::rp-state)))

(make-event
(b* ((modnames '())
((mv modules rp::rp-state)
(svl-flatten-design modnames
*mult-sv-design*
*mult-vl-design2*)))
(mv nil
`(defconst *mult-svl-design*
',modules)
state
rp::rp-state)))

(get-svl-modules-ports *signed128-svl-design*)

(time$
(svl-run-cycle "Multiplier_15_0_1000"
(list 233 45)
(make-svl-env)
*mult-svl-design*))

(time$
(svl-run-cycle "Mult_64_64"
(list 233 45)
(make-svl-env)
*signed64-svl-design*))

(time$
(svl-run-cycle "Mult_256_256"
(list 233 45)
(make-svl-env)
*signed256-svl-design*))

(time$
(svl-run-cycle "Mult_128_128"
(list 233 45)
(make-svl-env)
*signed128-svl-design*))

(time$
(b* (((mv res &)
(svl-run-cycle "booth2_multiplier_signed_64x32_97"
(list 0 0 233 45)
(make-svl-env)
*big-svl-design*)))
(bits (+ (bits (car res) 0 97 )
(bits (car res) 97 97 ))
0 97 )))
||#
