; FGL - A Symbolic Simulation Framework for ACL2
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "FGL")


(include-book "top-bare")
(include-book "std/strings/hexify" :dir :system)
(include-book "std/util/defconsts" :dir :system)       
(include-book "checks")


(defconst *incremental-extremize-config-fields*
  '((numerator  "integer value to maximize, or numerator of ratio to maximize")
    (denominator "denominator of ratio to maximize, or 1")
    (direction "t for maximize, nil for minimize")
    (sat-config "config for subsequent solves")
    (obj  "to evaluate on satisfying assignments, returning the last which (if successful) extremizes the value/ratio")
    (progress-term "term to symbolically interpret for side effects on start of each iteration")
    (final-term "term to symbolically interpret for side effects when finishing successfully")
    (unsat-term "term to symbolically interpret for side effects on unsat calls")
    (sat-term "term to symbolically interpret for side effects on sat calls (with counterexample values avaliable")
    (error-term "term to symbolically interpret for side effects when sat check or counterexample generation fails")
    (bad-ctrex-term "term to symbolically interpret for side effects when an invalid counterexample is produced")
    (interpolate-factor
     "fraction between 0 and 1 (exclusive) determining
                        where the next target is picked -- between 1/8 and
                        1/2 is reasonable")))
(make-event `(std::defaggregate incremental-extremize-config ,*incremental-extremize-config-fields*))

(defun prefix-qmark-to-syms (syms)
  (if (atom syms)
      nil
    (cons (intern-in-package-of-symbol (concatenate 'string "?" (symbol-name (car syms))) (car syms))
          (prefix-qmark-to-syms (cdr syms)))))

(def-b*-binder incremental-extremize-bind
  :body
  (b* ((?args args))
    `(b* (((acl2::assocs . ,(prefix-qmark-to-syms (strip-cars *incremental-extremize-config-fields*))) . ,acl2::forms))
       ,acl2::rest-expr)))

(fgl::def-fgl-program incr-extrem-counterexample (config)
  (fgl::syntax-interp (fgl::show-counterexample-bind config fgl::interp-st state)))


(def-fgl-program incremental-extremize-iter
  ((known-exceedable "integer value that can be met or exceeded, i.e. if
                      maximizing, exists env for which x >= y * known-exceedable")
   (known-bound "integer value that we know can't be exceeded, i.e. if
                 maximizing, for all envs x < y * (1+known-bound)")
   (next-sat-config "sat config for the next solve")
   (last-obj "value from last satisfying assignment")
   (config "incremental-extremize-config object"))
  :returns (mv (successp "succeeded in extremizing the value / ratio")
               (final-obj "result of evaluating obj under the assignment that extremized the value / ratio")
               (bound "final value of known bound"))
  :def-body (mv nil nil nil)
  :ignore-ok t :irrelevant-formals-ok t
  (b* (((incremental-extremize-bind) config)
       (?ign (fgl-interp-obj progress-term))
       ((when (if direction
                  (<= known-bound known-exceedable)
                (>= known-bound known-exceedable)))
        (b* ((?ign (fgl-interp-obj final-term)))
          (mv t last-obj known-bound)))
       ;; dividing by 8 here means we go closer to the known SAT lower bound,
       ;; biasing toward SAT calls.  This is because SAT calls tend to be
       ;; faster AND we get a more specific next step than with UNSAT.
       (middle (+ known-exceedable
                  (if direction
                      (ceiling (* (numerator interpolate-factor)
                                  (- known-bound known-exceedable))
                               (denominator interpolate-factor))
                    (- (ceiling (* (numerator interpolate-factor)
                                   (- known-exceedable known-bound))
                                (denominator interpolate-factor))))))
       (cond (if direction (<= (* denominator middle) numerator) (>= (* denominator middle) numerator)))
       (sat-res (fgl-sat-check next-sat-config cond))
       (unsat (syntax-interp (not sat-res)))
       ((when unsat)
        (b* ((?ign (fgl-interp-obj unsat-term)))
          (incremental-extremize-iter known-exceedable (if direction (1- middle) (1+ middle))
                                      sat-config last-obj config)))
       ((list (list error bindings ?vars) &) (incr-extrem-counterexample next-sat-config))
       ;; (syntax-interp (show-counterexample-bind first-sat-config interp-st state)))
       ((when error)
        (b* ((?ign (fgl-interp-obj error-term)))
          (mv nil last-obj known-bound)))
       (ctrex-num (cdr (assoc 'numerator bindings)))
       (ctrex-denom (cdr (assoc 'denominator bindings)))
       (ctrex-obj (cdr (assoc 'obj bindings)))
       ;; (?ign (syntax-interp (cw! "bindings: ~x0~%" bindings)))
       (?ign (fgl-interp-obj sat-term))
       ((unless (if direction (<= (* ctrex-denom middle) ctrex-num) (>= (* ctrex-denom middle) ctrex-num)))
        (b* ((?ign (fgl-interp-obj bad-ctrex-term)))
          (mv nil last-obj known-bound))))
    (incremental-extremize-iter (if direction
                                    (floor ctrex-num ctrex-denom)
                                  (ceiling ctrex-num ctrex-denom))
                                known-bound sat-config ctrex-obj config)))



(defconsts (*incremental-maximize-defaults* state)
  (b* (((mv err alist state)
        (b* (((er progress-term)
              (acl2::translate '(fgl::syntax-interp (cw! "Incremental-maximize, lower: ~s0 upper: ~s1~%"
                                                         (str::hexify known-exceedable)
                                                         (str::hexify known-bound)))
                               t t nil 'incremental-maximize-defaults (w state) state))
             ((er final-term)
              (acl2::translate '(fgl::syntax-interp (cw "Final upper bound: x <= ~s0~%" (str::hexify known-exceedable)))
                               t t nil 'incremental-maximize-defaults (w state) state))
             ((er unsat-term)
              (acl2::translate '(fgl::syntax-interp (cw "Unsat: x < ~s0~%" (str::hexify middle)))
                               t t nil 'incremental-maximize-defaults (w state) state))
             ((er sat-term)
              (acl2::translate '(fgl::syntax-interp
                                 (Cw! "SAT -- x: ~s0~%obj: ~x1~%" (str::hexify ctrex-num) (g-concrete->val ctrex-obj)))
                               t t nil 'incremental-maximize-defaults (w state) state))
             ((er error-term)
              (acl2::translate '(fgl::syntax-interp
                                 (cw "Finished with error (SAT check failed?): ~x0~%Lower: ~s1~%Upper: ~s2~%"
                                     error (str::hexify known-exceedable) (str::hexify known-bound)))
                               t t nil 'incremental-maximize-defaults (w state) state))
             ((er bad-ctrex-term)
              (acl2::translate '(fgl::syntax-interp
                                 (cw "Error: invalid counterexample ~s0 -- should have been >= ~s1~%"
                                     (str::hexify ctrex-num) (str::hexify middle)))
                               t t nil 'incremental-maximize-defaults (w state) state)))
          (value `((progress-term . ,progress-term)
                   (final-term . ,final-term)
                   (unsat-term . ,unsat-term)
                   (sat-term . ,sat-term)
                   (error-term . ,error-term)
                   (bad-ctrex-term . ,bad-ctrex-term))))))
    (and err
         (er hard? '*incremental-maximize-defaults*
             "Error translating default terms: ~@0~%" err))
    (mv alist state)))


                               

(fgl::def-fgl-program incremental-maximize
  ((x "(symbolic) integer value to maximize")
   &key
   (lower "integer value that we know x can achieve/exceed")
   (upper "known upper bound for x")
   (obj "Object to return under maximizing assignment")
   ((first-sat-config
     "SAT config object to use for the first solve")
    '(make-fgl-ipasir-config :ipasir-callback-limit 10000))
   ((sat-config
     "SAT config object for subsequent solves")
    '(make-fgl-ipasir-config :ipasir-callback-limit 1000))
   ((progress-term
     "term to symbolically interpret for side effects on start of each iteration") '(cdr (assoc 'progress-term *incremental-maximize-defaults*)))
   ((final-term
     "term to symbolically interpret for side effects when finishing successfully")
    '(cdr (assoc 'final-term *incremental-maximize-defaults*)))
   ((unsat-term
     "term to symbolically interpret for side effects on unsat calls")
    '(cdr (assoc 'unsat-term *incremental-maximize-defaults*)))
   ((sat-term
     "term to symbolically interpret for side effects on sat calls (with counterexample values avaliable")
    '(cdr (assoc 'sat-term *incremental-maximize-defaults*)))
   ((error-term
     "term to symbolically interpret for side effects when sat check or counterexample generation fails")
    '(cdr (assoc 'error-term *incremental-maximize-defaults*)))
   ((bad-ctrex-term
     "term to symbolically interpret for side effects when an invalid counterexample is produced")
    '(cdr (assoc 'bad-ctrex-term *incremental-maximize-defaults*)))
   ((interpolate-factor
     "fraction between 0 and 1 (exclusive) determining where the next target
      is picked -- between 1/8 and 1/2 is reasonable")
    '1/4))

  (b* ((lower (or lower
                  (syntax-interp (mv-let (err val)
                                   (interp-st-fgl-object-eval x (make-fgl-env) 'interp-st 'state)
                                   (if err
                                       (cw "Eval error: ~x0~%" err)
                                     val)))))
       (upper (or upper
                  (ash 1 (integer-length-bound x-length x))))
       ((unless (syntax-interp (and (integerp lower)
                                    (integerp upper))))
        (syntax-interp (cw "Couldn't find concrete integer lower and upper bounds: ~x0, ~x1~%" lower upper))
        (mv nil nil nil))
       (config (make-incremental-extremize-config
                :numerator x
                :denominator 1
                :direction t
                :sat-config sat-config
                :obj obj
                :progress-term progress-term
                :final-term final-term
                :unsat-term unsat-term
                :sat-term sat-term
                :error-term error-term
                :bad-ctrex-term bad-ctrex-term
                :interpolate-factor interpolate-factor)))
    (incremental-extremize-iter lower upper first-sat-config nil config)))





(defconsts (*incremental-minimize-defaults* state)
  (b* (((mv err alist state)
        (b* (((er progress-term)
              (acl2::translate '(fgl::syntax-interp (cw! "Incremental-minimize, lower: ~s0 upper: ~s1~%"
                                                         (str::hexify known-bound)
                                                         (str::hexify known-exceedable)))
                               t t nil 'incremental-minimize-defaults (w state) state))
             ((er final-term)
              (acl2::translate '(fgl::syntax-interp (cw "Final lower bound: x >= ~s0~%" (str::hexify known-exceedable)))
                               t t nil 'incremental-minimize-defaults (w state) state))
             ((er unsat-term)
              (acl2::translate '(fgl::syntax-interp (cw "Unsat: x > ~s0~%" (str::hexify middle)))
                               t t nil 'incremental-minimize-defaults (w state) state))
             ((er sat-term)
              (acl2::translate '(fgl::syntax-interp
                                 (Cw! "SAT -- x: ~s0~%obj: ~x1~%" (str::hexify ctrex-num) (g-concrete->val ctrex-obj)))
                               t t nil 'incremental-minimize-defaults (w state) state))
             ((er error-term)
              (acl2::translate '(fgl::syntax-interp
                                 (cw "Finished with error (SAT check failed?): ~x0~%Lower: ~s1~%Upper: ~s2~%"
                                     error (str::hexify known-bound) (str::hexify known-exceedable)))
                               t t nil 'incremental-minimize-defaults (w state) state))
             ((er bad-ctrex-term)
              (acl2::translate '(fgl::syntax-interp
                                 (cw "Error: invalid counterexample ~s0 -- should have been <= ~s1~%"
                                     (str::hexify ctrex-num) (str::hexify middle)))
                               t t nil 'incremental-minimize-defaults (w state) state)))
          (value `((progress-term . ,progress-term)
                   (final-term . ,final-term)
                   (unsat-term . ,unsat-term)
                   (sat-term . ,sat-term)
                   (error-term . ,error-term)
                   (bad-ctrex-term . ,bad-ctrex-term))))))
    (and err
         (er hard? '*incremental-minimize-defaults*
             "Error translating default terms: ~@0~%" err))
    (mv alist state)))


                               

(fgl::def-fgl-program incremental-minimize
  ((x "(symbolic) integer value to minimize")
   &key
   (lower "known lower bound for x")
   (upper "integer value that we know x can be less than or equal")
   (obj "Object to return under maximizing assignment")
   ((first-sat-config
     "SAT config object to use for the first solve")
    '(make-fgl-ipasir-config :ipasir-callback-limit 10000))
   ((sat-config
     "SAT config object for subsequent solves")
    '(make-fgl-ipasir-config :ipasir-callback-limit 1000))
   ((progress-term
     "term to symbolically interpret for side effects on start of each iteration") '(cdr (assoc 'progress-term *incremental-minimize-defaults*)))
   ((final-term
     "term to symbolically interpret for side effects when finishing successfully")
    '(cdr (assoc 'final-term *incremental-minimize-defaults*)))
   ((unsat-term
     "term to symbolically interpret for side effects on unsat calls")
    '(cdr (assoc 'unsat-term *incremental-minimize-defaults*)))
   ((sat-term
     "term to symbolically interpret for side effects on sat calls (with counterexample values avaliable")
    '(cdr (assoc 'sat-term *incremental-minimize-defaults*)))
   ((error-term
     "term to symbolically interpret for side effects when sat check or counterexample generation fails")
    '(cdr (assoc 'error-term *incremental-minimize-defaults*)))
   ((bad-ctrex-term
     "term to symbolically interpret for side effects when an invalid counterexample is produced")
    '(cdr (assoc 'bad-ctrex-term *incremental-minimize-defaults*)))
   ((interpolate-factor
     "fraction between 0 and 1 (exclusive) determining where the next target
      is picked -- between 1/8 and 1/2 is reasonable")
    '1/4))

  (b* ((upper (or upper
                  (syntax-interp (mv-let (err val)
                                   (interp-st-fgl-object-eval x (make-fgl-env) 'interp-st 'state)
                                   (if err
                                       (cw "Eval error: ~x0~%" err)
                                     val)))))
       (lower (or lower
                  (1- (ash -1 (integer-length-bound x-length x)))))
       ((unless (syntax-interp (and (integerp lower)
                                    (integerp upper))))
        (syntax-interp (cw "Couldn't find concrete integer lower and upper bounds: ~x0, ~x1~%" lower upper))
        (mv nil nil nil))
       (config (make-incremental-extremize-config
                :numerator x
                :denominator 1
                :direction nil
                :sat-config sat-config
                :obj obj
                :progress-term progress-term
                :final-term final-term
                :unsat-term unsat-term
                :sat-term sat-term
                :error-term error-term
                :bad-ctrex-term bad-ctrex-term
                :interpolate-factor interpolate-factor)))
    (incremental-extremize-iter upper lower first-sat-config nil config)))




(defconsts (*incremental-maximize-ratio-defaults* state)
  (b* (((mv err alist state)
        (b* (((er progress-term)
              (acl2::translate '(fgl::syntax-interp (cw! "Incremental-maximize-ratio, lower: ~s0 upper: ~s1~%"
                                                         (str::hexify known-exceedable)
                                                         (str::hexify known-bound)))
                               t t nil 'incremental-maximize-ratio-defaults (w state) state))
             ((er final-term)
              (acl2::translate '(fgl::syntax-interp (cw "Final upper bound: x/y <= ~s0~%" (str::hexify known-exceedable)))
                               t t nil 'incremental-maximize-ratio-defaults (w state) state))
             ((er unsat-term)
              (acl2::translate '(fgl::syntax-interp (cw "Unsat: x/y < ~s0~%" (str::hexify middle)))
                               t t nil 'incremental-maximize-ratio-defaults (w state) state))
             ((er sat-term)
              (acl2::translate '(fgl::syntax-interp
                                 (Cw! "SAT -- x: ~s0~%y: ~s1~%obj: ~x2~%" (str::hexify ctrex-num) (str::hexify ctrex-denom)
                                      (g-concrete->val ctrex-obj)))
                               t t nil 'incremental-maximize-ratio-defaults (w state) state))
             ((er error-term)
              (acl2::translate '(fgl::syntax-interp
                                 (cw "Finished with error (SAT check failed?): ~x0~%Lower: ~s1~%Upper: ~s2~%"
                                     error (str::hexify known-exceedable) (str::hexify known-bound)))
                               t t nil 'incremental-maximize-ratio-defaults (w state) state))
             ((er bad-ctrex-term)
              (acl2::translate '(fgl::syntax-interp
                                 (cw "Error: invalid counterexample ~s0 / ~s1 -- should have been >= ~s2~%"
                                     (str::hexify ctrex-num) (str::hexify ctrex-denom) (str::hexify middle)))
                               t t nil 'incremental-maximize-ratio-defaults (w state) state)))
          (value `((progress-term . ,progress-term)
                   (final-term . ,final-term)
                   (unsat-term . ,unsat-term)
                   (sat-term . ,sat-term)
                   (error-term . ,error-term)
                   (bad-ctrex-term . ,bad-ctrex-term))))))
    (and err
         (er hard? '*incremental-maximize-ratio-defaults*
             "Error translating default terms: ~@0~%" err))
    (mv alist state)))


;; Note: consider possibility of y being negative.  We assume it can't be zero.
(fgl::def-fgl-program incremental-maximize-ratio
  ((x "(symbolic) numerator of the ratio  to maximize")
   (y "(symbolic) denominator of the ratio  to maximize")
   &key
   (lower "integer value that we know x/y can achieve/exceed")
   (upper "known upper bound for x/y")
   (obj "Object to return under maximizing assignment")
   ((first-sat-config
     "SAT config object to use for the first solve")
    '(make-fgl-ipasir-config :ipasir-callback-limit 10000))
   ((sat-config
     "SAT config object for subsequent solves")
    '(make-fgl-ipasir-config :ipasir-callback-limit 1000))
   ((progress-term
     "term to symbolically interpret for side effects on start of each iteration")
    '(cdr (assoc 'progress-term *incremental-maximize-ratio-defaults*)))
   ((final-term
     "term to symbolically interpret for side effects when finishing successfully")
    '(cdr (assoc 'final-term *incremental-maximize-ratio-defaults*)))
   ((unsat-term
     "term to symbolically interpret for side effects on unsat calls")
    '(cdr (assoc 'unsat-term *incremental-maximize-ratio-defaults*)))
   ((sat-term
     "term to symbolically interpret for side effects on sat calls (with counterexample values avaliable")
    '(cdr (assoc 'sat-term *incremental-maximize-ratio-defaults*)))
   ((error-term
     "term to symbolically interpret for side effects when sat check or counterexample generation fails")
    '(cdr (assoc 'error-term *incremental-maximize-ratio-defaults*)))
   ((bad-ctrex-term
     "term to symbolically interpret for side effects when an invalid counterexample is produced")
    '(cdr (assoc 'bad-ctrex-term *incremental-maximize-ratio-defaults*)))
   ((interpolate-factor
     "fraction between 0 and 1 (exclusive) determining where the next target
      is picked -- between 1/8 and 1/2 is reasonable")
    '1/4))

  (b* ((lower (or lower
                  (syntax-interp (b* (((mv err xval)
                                       (interp-st-fgl-object-eval x (make-fgl-env) 'interp-st 'state))
                                      ((when err) nil)
                                      ((mv err yval)
                                       (interp-st-fgl-object-eval y (make-fgl-env) 'interp-st 'state))
                                      ((when err) nil))
                                   (floor xval yval)))))
       (upper (or upper
                  ;; this is likely to be a bad upper bound
                  (ash 1 (integer-length-bound x-length x))))
       ((unless (syntax-interp (and (integerp lower)
                                    (integerp upper))))
        (syntax-interp (cw "Couldn't find concrete integer lower and upper bounds: ~x0, ~x1~%" lower upper))
        (mv nil nil nil))
       (config (make-incremental-extremize-config
                :numerator x
                :denominator y
                :direction t
                :sat-config sat-config
                :obj obj
                :progress-term progress-term
                :final-term final-term
                :unsat-term unsat-term
                :sat-term sat-term
                :error-term error-term
                :bad-ctrex-term bad-ctrex-term
                :interpolate-factor interpolate-factor)))
    (incremental-extremize-iter lower upper first-sat-config nil config)))





(defconsts (*incremental-minimize-ratio-defaults* state)
  (b* (((mv err alist state)
        (b* (((er progress-term)
              (acl2::translate '(fgl::syntax-interp (cw! "Incremental-minimize-ratio, lower: ~s0 upper: ~s1~%"
                                                         (str::hexify known-bound)
                                                         (str::hexify known-exceedable)))
                               t t nil 'incremental-minimize-ratio-defaults (w state) state))
             ((er final-term)
              (acl2::translate '(fgl::syntax-interp (cw "Final lower bound: x/y >= ~s0~%" (str::hexify known-exceedable)))
                               t t nil 'incremental-minimize-ratio-defaults (w state) state))
             ((er unsat-term)
              (acl2::translate '(fgl::syntax-interp (cw "Unsat: x/y > ~s0~%" (str::hexify middle)))
                               t t nil 'incremental-minimize-ratio-defaults (w state) state))
             ((er sat-term)
              (acl2::translate '(fgl::syntax-interp
                                 (Cw! "SAT -- x: ~s0~%y: ~s1~%obj: ~x2~%" (str::hexify ctrex-num) (str::hexify ctrex-denom)
                                      (g-concrete->val ctrex-obj)))
                               t t nil 'incremental-minimize-ratio-defaults (w state) state))
             ((er error-term)
              (acl2::translate '(fgl::syntax-interp
                                 (cw "Finished with error (SAT check failed?): ~x0~%Lower: ~s1~%Upper: ~s2~%"
                                     error (str::hexify known-bound) (str::hexify known-exceedable)))
                               t t nil 'incremental-minimize-ratio-defaults (w state) state))
             ((er bad-ctrex-term)
              (acl2::translate '(fgl::syntax-interp
                                 (cw "Error: invalid counterexample ~s0 / ~s1 -- should have been <= ~s2~%"
                                     (str::hexify ctrex-num) (str::hexify ctrex-denom) (str::hexify middle)))
                               t t nil 'incremental-minimize-ratio-defaults (w state) state)))
          (value `((progress-term . ,progress-term)
                   (final-term . ,final-term)
                   (unsat-term . ,unsat-term)
                   (sat-term . ,sat-term)
                   (error-term . ,error-term)
                   (bad-ctrex-term . ,bad-ctrex-term))))))
    (and err
         (er hard? '*incremental-minimize-ratio-defaults*
             "Error translating default terms: ~@0~%" err))
    (mv alist state)))


;; Note: consider possibility of y being negative.  We assume it can't be zero.
(fgl::def-fgl-program incremental-minimize-ratio
  ((x "(symbolic) numerator of the ratio  to minimize")
   (y "(symbolic) denominator of the ratio  to minimize")
   &key
   (lower "integer value that we know x/y can achieve/exceed")
   (upper "known upper bound for x/y")
   (obj "Object to return under maximizing assignment")
   ((first-sat-config
     "SAT config object to use for the first solve")
    '(make-fgl-ipasir-config :ipasir-callback-limit 10000))
   ((sat-config
     "SAT config object for subsequent solves")
    '(make-fgl-ipasir-config :ipasir-callback-limit 1000))
   ((progress-term
     "term to symbolically interpret for side effects on start of each iteration")
    '(cdr (assoc 'progress-term *incremental-minimize-ratio-defaults*)))
   ((final-term
     "term to symbolically interpret for side effects when finishing successfully")
    '(cdr (assoc 'final-term *incremental-minimize-ratio-defaults*)))
   ((unsat-term
     "term to symbolically interpret for side effects on unsat calls")
    '(cdr (assoc 'unsat-term *incremental-minimize-ratio-defaults*)))
   ((sat-term
     "term to symbolically interpret for side effects on sat calls (with counterexample values avaliable")
    '(cdr (assoc 'sat-term *incremental-minimize-ratio-defaults*)))
   ((error-term
     "term to symbolically interpret for side effects when sat check or counterexample generation fails")
    '(cdr (assoc 'error-term *incremental-minimize-ratio-defaults*)))
   ((bad-ctrex-term
     "term to symbolically interpret for side effects when an invalid counterexample is produced")
    '(cdr (assoc 'bad-ctrex-term *incremental-minimize-ratio-defaults*)))
   ((interpolate-factor
     "fraction between 0 and 1 (exclusive) determining where the next target
      is picked -- between 1/8 and 1/2 is reasonable")
    '1/4))

  (b* ((upper (or upper
                  (syntax-interp (b* (((mv err xval)
                                       (interp-st-fgl-object-eval x (make-fgl-env) 'interp-st 'state))
                                      ((when err) nil)
                                      ((mv err yval)
                                       (interp-st-fgl-object-eval y (make-fgl-env) 'interp-st 'state))
                                      ((when err) nil))
                                   (ceiling xval yval)))))
       (lower (or lower
                  ;; this is likely to be a bad lower bound
                  (1- (ash -1 (integer-length-bound x-length x)))))
       ((unless (syntax-interp (and (integerp lower)
                                    (integerp upper))))
        (syntax-interp (cw "Couldn't find concrete integer lower and upper bounds: ~x0, ~x1~%" lower upper))
        (mv nil nil nil))
       (config (make-incremental-extremize-config
                :numerator x
                :denominator y
                :direction nil
                :sat-config sat-config
                :obj obj
                :progress-term progress-term
                :final-term final-term
                :unsat-term unsat-term
                :sat-term sat-term
                :error-term error-term
                :bad-ctrex-term bad-ctrex-term
                :interpolate-factor interpolate-factor)))
    (incremental-extremize-iter upper lower first-sat-config nil config)))

#||
;; Examples
(include-book
 "top")
(include-book
  "centaur/ipasir/ipasir-backend" :dir :System)
(local (table fgl-config-table :prof-enabledp nil))

(fgl-thm
 :hyp (signed-byte-p 10 x)
 :concl (b* ((poly (+ (- (* x x x)) (* 2 x x) (* 500000 x) 15))
             (denom (+ 100000 (* x x)))
             (obj `((x . ,x) (poly . ,poly)))
             (ratobj `((x . ,x) (poly . ,poly) (denom . ,denom))))
          (fgl-prog2 (b* (((mv max-ok max-obj upper-bound) (incremental-maximize poly :obj obj))
                          ((mv min-ok min-obj lower-bound) (incremental-minimize poly :obj obj))
                          ((mv maxrat-ok maxrat-obj rat-upper-bound) (incremental-maximize-ratio poly denom :obj ratobj))
                          ((mv minrat-ok minrat-obj rat-lower-bound) (incremental-minimize-ratio poly denom :obj ratobj))
                          (?ign (if max-ok
                                    (cw "Maximizing succeeded; poly=~x0 with x=~x1~%" (cdr (assoc 'poly max-obj)) (cdr (assoc 'x max-obj)))
                                  (cw "Maximizing failed, but found an upper bound of ~x0 with greatest example poly=~x1 with x=~x2~%"
                                      upper-bound (cdr (assoc 'poly max-obj)) (cdr (assoc 'x max-obj)))))
                          (?ign (if min-ok
                                    (cw "Minimizing succeeded; poly=~x0 with x=~x1~%" (cdr (assoc 'poly min-obj)) (cdr (assoc 'x min-obj)))
                                  (cw "Minimizing failed, but found a lower bound of ~x0 with least example poly=~x1 with x=~x2~%"
                                      lower-bound (cdr (assoc 'poly min-obj)) (cdr (assoc 'x min-obj)))))
                          (?ign (if maxrat-ok
                                    (cw "Maximizing ratio succeeded; poly=~x0, denom=~x1 with x=~x2~%"
                                        (cdr (assoc 'poly maxrat-obj)) (cdr (assoc 'denom maxrat-obj)) (cdr (assoc 'x maxrat-obj)))
                                  (cw "Maximizing failed, but found an upper bound of ~x0 with greatest example poly=~x1,denom=~x2 with x=~x3~%"
                                      rat-upper-bound (cdr (assoc 'poly maxrat-obj)) (cdr (assoc 'denom maxrat-obj)) (cdr (assoc 'x maxrat-obj)))))
                          (?ign (if minrat-ok
                                    (cw "Minimizing ratio succeeded; poly=~x0, denom=~x1 with x=~x2~%"
                                        (cdr (assoc 'poly minrat-obj)) (cdr (assoc 'denom minrat-obj)) (cdr (assoc 'x minrat-obj)))
                                  (cw "Minimizing failed, but found an upper bound of ~x0 with greatest example poly=~x1,denom=~x2 with x=~x3~%"
                                      rat-lower-bound (cdr (assoc 'poly minrat-obj)) (cdr (assoc 'denom minrat-obj)) (cdr (assoc 'x minrat-obj))))))
                       nil)
                     ;; trivial conclusion
                     (equal poly poly))))

||#
