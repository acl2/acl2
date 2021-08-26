; MULTIPLIER RULES

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Mertcan Temel         <mert@utexas.edu>

(in-package "RP")

(include-book "svl-top")

(include-book "centaur/sv/svtv/process" :dir :system)  ;

;;(include-book "centaur/vl/parsetree" :dir :system)

;;(include-book "centaur/svl/svexl/svtv-run-with-svexl" :dir :system)

(set-ignore-ok t)
(add-rp-rule acl2::svtv-run-fn
             :beta-reduce t
             :hints (("Goal"
                      :in-theory (e/d (acl2::svtv-run-fn) ()))))

;; (enable-rules '(svl::svexl-alist-correct
;;                 svl::svexllist-correct
;;                 svl::svexl-correct))

;; (rp::bump-rp-rule svl::svexl-alist-correct)
;; (rp::bump-rp-rule svl::svexllist-correct)
;; (rp::bump-rp-rule svl::svexl-correct)

;; (enable-rules '(svl::svexl-alist-fasteval-correct
;;                 svl::svexllist-fasteval-correct
;;                 svl::svexl-fasteval-correct))

;; (rp::bump-rp-rule svl::svexl-alist-fasteval-correct)
;; (rp::bump-rp-rule svl::svexllist-fasteval-correct)
;; (rp::bump-rp-rule svl::svexl-fasteval-correct)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defwarrant sym-app-fnc)

(defun replace-adders-fn (original-sv
                          original-vl
                          new-sv
                          new-adders-file
                          adder-module-names
                          sanity-check
                          local
                          dummy-top)
  (declare (ignorable original-sv original-vl new-adders-file
                      adder-module-names
                      local))

  `(encapsulate
       nil

       (local
        (include-book "centaur/sv/top" :dir :system))
       
       (local
        (defun get-vl-module (module-name vl-mods)
          (declare (xargs :guard (and (Vl::vl-modulelist-p vl-mods)
                                      (stringp module-name))))
          (if (atom vl-mods)
              (hard-error 'get-vl-module
                          "Module ~p0 cannot be found in the given VL-design-modlist~%"
                          (list (cons #\0 module-name)))
              (if (equal module-name (vl::vl-module->name (car vl-mods)))
                  (car vl-mods)
                  (get-vl-module module-name (cdr vl-mods))))))
       
     (,(if local 'local 'progn)
      (acl2::defconsts
       (*redefined-adders-vl-design* state)
       (b* (((mv loadresult state)
             (vl::vl-load (vl::make-vl-loadconfig
                           :start-files ',new-adders-file))))
         (mv (vl::vl-loadresult->design loadresult) state))))
     (,(if local 'local 'progn)
      ,(if dummy-top
           `(progn
              (acl2::defconsts
               (,(sa '*redefined dummy-top '-sv-design*))
               (b* (((mv errmsg new-sv-design & &)
                     (vl::vl-design->sv-design ,dummy-top
                                               *redefined-adders-vl-design*
                                               (vl::make-vl-simpconfig)))
                    (- (and errmsg (acl2::raise "~@0~%" errmsg))))
                 new-sv-design))

              (acl2::defconsts
               (,(sa '*redefined dummy-top '-svl-design*) rp::rp-state)
               (svl::svl-flatten-design ,(sa '*redefined dummy-top '-sv-design*)
                                        *redefined-adders-vl-design*
                                        :top ,dummy-top
                                        :dont-flatten :all))

              (acl2::defconsts
               (,(sa '*original dummy-top '-svl-design*) rp::rp-state)
               (b* ((sv-design ,original-sv)
                    (- (and (hons-assoc-equal ,dummy-top sv-design)
                            (hard-error 'replace-adders-fn
                                        "Original SV design contains a module of the same name as the given dummy-top module: ~p0.
Choose a different dummy-top name."
                                        (list (cons #\0 ,dummy-top)))))
                    (sv-design (sv::change-design
                                 sv-design
                                 :modalist
                                 (cons
                                  (hons-assoc-equal ,dummy-top (sv::design->modalist ,(sa '*redefined dummy-top '-sv-design*)))
                                  (sv::design->modalist sv-design))))
                    (vl-design ,original-vl)
                    (vl-design (vl::change-vl-design vl-design
                                                     :mods
                                                     (cons
                                                      (get-vl-module ,dummy-top
                                                                     (vl::vl-design->mods *redefined-adders-vl-design*))
                                                      (vl::vl-design->mods
                                                       vl-design)
                                                      
                                                      )))
                    )
                 (svl::svl-flatten-design sv-design
                                          vl-design
                                          :top ,dummy-top
                                          :dont-flatten :all)))
              .
              ,(if sanity-check
                   (loop$ for x in adder-module-names collect
                          `(progn
                             (make-event
                              (b* ((redefined-svl-design-ws ',(sa '*redefined dummy-top '-svl-design*))
                                   (original-svl-design-ws ',(sa '*original
                                                             dummy-top '-svl-design*))
                                   (redefined-svl-design ,(sa '*redefined dummy-top '-svl-design*))
                                   (original-svl-design ,(sa '*original
                                                             dummy-top '-svl-design*))
                                   (orig-mod (assoc-equal ,x original-svl-design))
                                   (redef-mod (assoc-equal ,x redefined-svl-design))
                                   (- (or orig-mod
                                          (hard-error 'replace-adders-fn
                                                      "Original svl netlist does not contain the module: ~p0 ~%"
                                                      (list (cons #\0 ,x)))))
                                   (- (or redef-mod
                                          (hard-error 'replace-adders-fn
                                                      "Redefined svl netlist does not contain the module: ~p0 ~%"
                                                      (list (cons #\0 ,x)))))
                                   (ins1 (svl::svl-module->inputs (cdr orig-mod)))
                                   (ins2 (svl::svl-module->inputs (cdr redef-mod)))
                                   ;; some checks:
                                   (- (or (equal ins1 ins2)
                                          (hard-error 'replace-adders-fn
                                                      "Input wires for ~p0
does not match with the module that is suggested for replication. ~%"
                                                      (list (cons #\0 ,x)))))
                                   (- (or (equal (svl::svl-module->outputs
                                                  (cdr (assoc-equal ,x
                                                                    original-svl-design)))
                                                 (svl::svl-module->outputs
                                                  (cdr (assoc-equal ,x
                                                                    redefined-svl-design))))
                                          (hard-error 'replace-adders-fn
                                                      "Output wires for ~p0
does not match with the module that is suggested for replication. ~%"
                                                      (list (cons #\0 ,x)))))
                                   (- (or (equal (svl::svl-module->outputs
                                                  (cdr (assoc-equal ,x
                                                                    original-svl-design)))
                                                 (svl::svl-module->outputs
                                                  (cdr (assoc-equal ,x
                                                                    redefined-svl-design))))
                                          (hard-error 'replace-adders-fn
                                                      "Output wires for ~p0
does not match with the module that is suggested for replication. ~%"
                                                      (list (cons #\0 ,x)))))
                                   (- (or (and (not (svl::svl-module->delayed-inputs
                                                     (cdr (assoc-equal ,x
                                                                       original-svl-design))))
                                               (not (svl::svl-module->delayed-inputs
                                                     (cdr (assoc-equal ,x
                                                                       redefined-svl-design)))))
                                          (hard-error 'replace-adders-fn
                                                      "One of the module to be
replaced includes a state holding element. This happened with module ~p0 ~%"
                                                      (list (cons #\0 ,x)))))
                                   (hyps
                                    (loop$ for y in ins1 collect
                                           `(unsigned-byte-p
                                             ,(svl::wire-size y)
                                             ,(sa (svl::wire-name y)
                                                  (svl::wire-start y)
                                                  (svl::wire-size y)))))

                                   (all-bitps
                                    (equal (loop$ for y in ins1 sum
                                                  (if (equal (svl::wire-size y) 1)
                                                      0 1))
                                           0))

                                   (ins-list
                                    (loop$ for y in ins1 collect
                                           (sa (svl::wire-name y)
                                               (svl::wire-start y)
                                               (svl::wire-size y)))))

                                `(,(if all-bitps 'defthm 'defthmrp)
                                  ,',(sa 'redefined-adder- x '-is-correct)
                                  (implies (and . ,hyps)
                                           (equal (svl::svl-run-phase-wog
                                                   ,',x (list . ,ins-list) svl::*empty-state* ,redefined-svl-design-ws)
                                                  (svl::svl-run-phase-wog
                                                   ,',x (list . ,ins-list) svl::*empty-state* ,original-svl-design-ws)))
                                  ,@(if all-bitps
                                        '(:hints (("Goal"
                                                   :in-theory (e/d (bitp)
                                                                   ()))))
                                      '(:disable-meta-rules (s-c-spec-meta)
                                                            :enable-rules
                                                            (append '(unsigned-byte-p INTEGER-RANGE-P)
                                                                    rp::*adder-rules*))))))))
                 nil))
         `(progn .
                 ,(loop$ for x in adder-module-names collect
                         `(progn
                            (acl2::defconsts
                             (,(sa '*redefined x '-sv-design*))
                             (b* (((mv errmsg new-sv-design & &)
                                   (vl::vl-design->sv-design ,(if dummy-top
                                                                  dummy-top x)
                                                             *redefined-adders-vl-design*
                                                             (vl::make-vl-simpconfig)))
                                  (- (and errmsg (acl2::raise "~@0~%" errmsg))))
                               new-sv-design))

                            ,(if sanity-check
                                 `(progn
                                    (acl2::defconsts
                                     (,(sa '*redefined x '-svl-design*) rp::rp-state)
                                     (svl::svl-flatten-design ,(sa '*redefined x '-sv-design*)
                                                              *redefined-adders-vl-design*
                                                              :top ,x
                                                              :dont-flatten :all))
                                    (acl2::defconsts
                                     (,(sa '*original x '-svl-design*) rp::rp-state)
                                     (svl::svl-flatten-design ,original-sv
                                                              ,original-vl
                                                              :top ,x
                                                              :dont-flatten :all))

                                    (make-event
                                     (b* ((ins1 (svl::svl-module->inputs
                                                 (cdr (assoc-equal ,x
                                                                   ,(sa '*original x
                                                                        '-svl-design*)))))
                                          (ins2 (svl::svl-module->inputs
                                                 (cdr (assoc-equal ,x
                                                                   ,(sa '*redefined x
                                                                        '-svl-design*)))))
                                          ;; some checks:
                                          (- (or (equal ins1 ins2)
                                                 (hard-error 'replace-adders-fn
                                                             "Input wires for ~p0
does not match with the module that is suggested for replication. ~%"
                                                             (list (cons #\0 ,x)))))
                                          (- (or (equal (svl::svl-module->outputs
                                                         (cdr (assoc-equal ,x
                                                                           ,(sa '*original x
                                                                                '-svl-design*))))
                                                        (svl::svl-module->outputs
                                                         (cdr (assoc-equal ,x
                                                                           ,(sa '*redefined x
                                                                                '-svl-design*)))))
                                                 (hard-error 'replace-adders-fn
                                                             "Output wires for ~p0
does not match with the module that is suggested for replication. ~%"
                                                             (list (cons #\0 ,x)))))
                                          (- (or (equal (svl::svl-module->outputs
                                                         (cdr (assoc-equal ,x
                                                                           ,(sa '*original x
                                                                                '-svl-design*))))
                                                        (svl::svl-module->outputs
                                                         (cdr (assoc-equal ,x
                                                                           ,(sa '*redefined x
                                                                                '-svl-design*)))))
                                                 (hard-error 'replace-adders-fn
                                                             "Output wires for ~p0
does not match with the module that is suggested for replication. ~%"
                                                             (list (cons #\0 ,x)))))
                                          (- (or (and (not (svl::svl-module->delayed-inputs
                                                            (cdr (assoc-equal ,x
                                                                              ,(sa '*original x
                                                                                   '-svl-design*)))))
                                                      (not (svl::svl-module->delayed-inputs
                                                            (cdr (assoc-equal ,x
                                                                              ,(sa '*redefined x
                                                                                   '-svl-design*))))))
                                                 (hard-error 'replace-adders-fn
                                                             "One of the module to be
replaced includes a state holding element. This happened with module ~p0 ~%"
                                                             (list (cons #\0 ,x)))))
                                          (hyps
                                           (loop$ for y in ins1 collect
                                                  `(unsigned-byte-p
                                                    ,(svl::wire-size y)
                                                    ,(sa (svl::wire-name y)
                                                         (svl::wire-start y)
                                                         (svl::wire-size y)))))

                                          (all-bitps
                                           (equal (loop$ for y in ins1 sum
                                                         (if (equal (svl::wire-size y) 1)
                                                             0 1))
                                                  0))

                                          (ins-list
                                           (loop$ for y in ins1 collect
                                                  (sa (svl::wire-name y)
                                                      (svl::wire-start y)
                                                      (svl::wire-size y)))))

                                       `(,(if all-bitps 'defthm 'defthmrp)
                                         ,',(sa 'redefined-adder- x '-is-correct)
                                         (implies (and . ,hyps)
                                                  (equal (svl::svl-run-phase-wog
                                                          ,',x (list . ,ins-list)
                                                          svl::*empty-state*
                                                          ,',(sa '*redefined x
                                                                 '-svl-design*))
                                                         (svl::svl-run-phase-wog
                                                          ,',x (list . ,ins-list)
                                                          svl::*empty-state*
                                                          ,',(sa '*original x
                                                                 '-svl-design*))))
                                         ,@(if all-bitps
                                               '(:hints (("Goal"
                                                          :in-theory (e/d (bitp)
                                                                          ()))))
                                             '(:disable-meta-rules (s-c-spec-meta)
                                                                   :enable-rules
                                                                   (append '(unsigned-byte-p INTEGER-RANGE-P)
                                                                           rp::*adder-rules*)))))))
                               `(value-triple :none))

                            )))))
     (acl2::defconsts
      ,new-sv
      (sv::change-design
       ,original-sv
       :modalist
       (fast-alist-clean
        (append

         ,@(if dummy-top
               `((remove1-assoc ',dummy-top
                                (SV::DESIGN->MODALIST ,(sa '*redefined
                                                           dummy-top '-sv-design*))
                                :test 'equal))
             (loop$ for x in adder-module-names collect
                    `(SV::DESIGN->MODALIST ,(sa '*redefined x '-sv-design*))))
         (sv::design->modalist ,original-sv)))))))

(defmacro replace-adders (&key original-sv original-vl  new-sv
                               new-adders-file adder-module-names
                               (sanity-check 't)
                               local
                               dummy-top)
  `(make-event
    (replace-adders-fn ',original-sv ',original-vl ',new-sv
                       ',new-adders-file
                       ',adder-module-names
                       ,sanity-check
                       ,local
                       ',dummy-top)))

(add-rp-rule unsigned-byte-p :disabled t)
(add-rp-rule INTEGER-RANGE-P :disabled t)

(def-rp-rule unsigned-byte-p-1-to-bitp
  (equal (unsigned-byte-p 1 x)
         (bitp x))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

