
(in-package "SVL")

(include-book "svl2-flatten")
(include-book "svl")


(define svl2-start-env ((wires wire-list-p)
                        (vals sv::4veclist-p)) 
  :returns (res sv::svex-env-p
                :hyp (and (wire-list-p wires)
                          (sv::4veclist-p vals)))
  (if (atom wires)
      nil
    (hons-acons
     (wire-name (car wires))
     (b* ((wire (car wires))
          ((mv s w)
           (mv (wire-start wire) (wire-size wire))))
       (cond ((not (car vals))
              (sv::4vec-x))
             (s 
              (4vec-part-select s w (car vals)))
             (t (car vals))))
     (svl2-start-env (cdr wires) (cdr vals)))))

(define svl2-retrieve-values ((wires wire-list-p)
                              (env-wires sv::svex-env-p))
  :returns (res sv::4veclist-p :hyp (and (wire-list-p wires)
                                         (sv::svex-env-p env-wires)))
  (if (atom wires)
      nil
    (b* ((wire (car wires))
         ((mv name s w)
          (mv (wire-name wire) (wire-start wire) (wire-size wire)))
         (value (hons-get name env-wires)))
      (cons (cond ((not value)
                   (sv::4vec-x))
                  (s
                   (4vec-part-select s w (cdr value)))
                  (t (cdr value)))
            (svl2-retrieve-values (cdr wires)
                                  env-wires)))))


(define save-lhs-to-env-wires ((val sv::4vec-p)
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
  (verify-guards save-lhs-to-env-wires))       

(define svl2-save-mod-outputs ((vals sv::4veclist-p)
                               (lhs-lst sv::lhslist-p)
                               (env-wires sv::svex-env-p))
  :returns (res sv::svex-env-p
                :hyp (and (sv::4veclist-p vals)
                          (sv::lhslist-p lhs-lst)
                          (sv::svex-env-p env-wires )))
  (if (or (atom vals)
          (atom lhs-lst))
      env-wires
    (b* ((cur-lhs (car lhs-lst))
         (cur-val (car vals))
         (env-wires (save-lhs-to-env-wires cur-val
                                           cur-lhs
                                           env-wires)))
      (svl2-save-mod-outputs (cdr vals)
                             (cdr lhs-lst)
                             env-wires))))
         
                               

(acl2::defines
 svl2-run-cycle
 (define svl2-run-cycle ((module-name sv::modname-p)
                         (inputs sv::4veclist-p)
                         (delayed-env svl-env-p)
                         (modules svl2-module-alist-p))
   :verify-guards nil
   (declare (xargs :mode :program))

   (let ((module (cdr (assoc-equal module-name modules))))
     (cond ((or (not module))
            (mv
             (cw "Either Module ~p0 is missing or it has invalid ranks~%"
                 module-name)
             (make-svl-env)))
           (t
            (b* (((svl2-module module) module)
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
                  next-delayed-env))))))
 
 (define svl2-run-cycle-occs ((occs svl2-occ-alist-p)
                              (env-wires sv::svex-env-p)
                              (delayed-env-alist svl-env-alist-p)
                              (modules svl2-module-alist-p))
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
                   (mod.delayed-env (hons-get occ-name delayed-env-alist))
                   (mod.delayed-env (if mod.delayed-env
                                        (cdr mod.delayed-env)
                                      (make-svl-env)))
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
                      rest-delayed-env))))))))


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

(get-svl2-modules-ports *signed64-svl2-design*)

(time$
 (svl2-run-cycle "Mult_64_64"
                 (list 233 45)
                 (make-svl-env)
                 *signed64-svl2-design*))

(time$
 (b* (((mv res &)
      (svl2-run-cycle "booth2_multiplier_signed_64x32_97"
                      (list 0 0 233 45)
                      (make-svl-env)
                      *big-svl2-design*)))
  (bits 0 97 (+ (bits 0 97 (car res))
                (bits 97 97 (car res))))))
||#
