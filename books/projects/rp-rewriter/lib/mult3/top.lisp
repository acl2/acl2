
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


;; To load the verilog designs:
(include-book "centaur/sv/top" :dir :system) ;; a big book; takes around 30 seconds
(include-book "centaur/vl/loader/top" :dir :system) ;; takes around 10 seconds
(include-book "oslib/ls" :dir :system)

(value-triple (acl2::set-max-mem (* 10 (expt 2 30))))

;; for correctness proof
(include-book "projects/rp-rewriter/lib/mult3/svtv-top" :dir :system)
(include-book "projects/rp-rewriter/lib/mult3/fgl" :dir :system)
(include-book "projects/rp-rewriter/lib/mult3/doc" :dir :system)

(include-book "centaur/fgl/top" :dir :system)

(defmacro parse-and-create-svtv (&key file topmodule name)
  `(with-output
     :off :all
     :on (summary error)
     :gag-mode nil
     (make-event
      (b* ((file ',file)
           (topmodule ',topmodule)
           (name ',(or name (intern$ (string-upcase topmodule) "RP"))) 
           (vl-design (intern$ (str::cat "*" (symbol-name name) "-VL-DESIGN*")
                               "RP"))
           (sv-design (intern$ (str::cat "*" (symbol-name name) "-SV-DESIGN*")
                               "RP")))
        `(encapsulate
           nil
           (acl2::defconsts
             (,vl-design state)
             (b* (((mv loadresult state)
                   (vl::vl-load (vl::make-vl-loadconfig
                                 :start-files '(,file)))))
               (mv (vl::vl-loadresult->design loadresult) state)))
      
           ;; Load SV design
           (acl2::defconsts
             (,sv-design)
             (b* (((mv errmsg sv-design ?good ?bad)
                   (vl::vl-design->sv-design ,topmodule
                                             ,vl-design
                                             (vl::make-vl-simpconfig))))
               (and errmsg
                    (acl2::raise "~@0~%" errmsg))
               sv-design))

           (local
            (make-event
             (b* ((val (svl::vl-design-to-insouts ,vl-design ,sv-design
                                                  (list ,topmodule)))
                  (val (hons-assoc-equal ,topmodule val))
                  ((unless val)
                   (hard-error 'parse-error
                               "Something went wrong when looking for ins and outs of this design. Please parse this design without this macro following the instructions in the demo files" nil))) 
               ;; GOTTA LOOK AT WHAT "VAL" LOOKS LIKE...
               `(acl2::defconsts (*ins* *outs*)
                  (mv (list ,@(car (cdr val)))
                      (list ,@(cdr (cdr val))))
                  ))))

           (make-event
            `(sv::defsvtv$ ,',name
               :mod ,',sv-design
               :inputs ',(loop$ for x in *ins* collect
                                `(,x ,(intern$ (string-upcase x) "RP")))
               :outputs ',(loop$ for x in *outs* collect
                                 `(,x ,(intern$ (string-upcase x) "RP")))
               :simplify nil))

           (rp::add-rp-rule ,(intern$ (str::cat (symbol-name name) "-AUTOHYPS") "RP"))
           (rp::add-rp-rule ,(intern$ (str::cat (symbol-name name) "-AUTOINS") "RP"))

           (value-triple (clear-memoize-tables))
           (value-triple (hons-clear t))
           (value-triple (gc$))
           )))))


(defmacro verify-svtv-of-mult (&key name
                                    concl
                                    (then-fgl 'nil)
                                    (cases 'nil)
                                    (pkg '"RP"))
  (acl2::template-subst
   `(make-event
     (b* ((cases ',cases)
          (ins (strip-cars (strip-cdrs (sv::svtv->orig-ins (<mult>)))))
          (outs (strip-cars (strip-cdrs (sv::svtv->orig-outs (<mult>)))))
          ((acl2::er translated-concl)
           (acl2::translate ',concl t t nil
                            'verify-svtv-of-mult
                            (w state) state))
          (concl-vars (acl2::all-vars translated-concl))
          (free-vars (set-difference$ concl-vars
                                      (append outs ins)))
          (- (cw "concl vars: ~p0 ~%" concl-vars))
          (- (and free-vars
                  (not (cw "WARNING! THE GIVEN CONCL CONTAINS THESE FREE VARIABLES:~p0~%" free-vars))
                  (not (cw "Available inputs are: ~p0. And outputs are~p1~%" ins outs))))
          (ignorable-outs (loop$ for x in outs collect
                                 (intern-in-package-of-symbol
                                  (str::Cat "?" (symbol-name x))
                                  x)))
          (event `(:or
                   (defthmrp-multiplier :then-fgl ,',then-fgl
                     <mult>-is-correct
                     (implies (<mult>-autohyps)
                              (b* (((sv::svassocs ,@ignorable-outs)
                                    (sv::svtv-run (<mult>)
                                                  (<mult>-autoins))))
                                ,',concl))
                     ,@(and cases `(:cases ,cases)))
                   (value-triple
                    (cond (',free-vars
                           (hard-error 'verify-svtv-of-mult
                                       "THE GIVEN CONCL CONTAINS THESE FREE VARIABLES: ~p0.~%Available inputs are ~p1.~%Available outputs are ~p2~%"
                                       (list (cons #\0 ',free-vars)
                                             (cons #\1 ',ins)
                                             (cons #\2 ',outs))))
                          ((not ,',then-fgl)
                           (hard-error 'verify-svtv-of-mult
                                       "THE PROOF FAILED. YOU CAN GENERATE COUNTEREXAMPLES BY ~
                                    PASSING \":THEN-FGL T\" AS AN ARGUMENT." nil))
                          (t nil))))))
       (value
        (if ,then-fgl
            `(progn (value-triple (acl2::tshell-ensure))
                    (make-event ',event))
          event))))
   :atom-alist `((<mult> . ,name))
   :str-alist `(("<MULT>" . ,(symbol-name name)))
   :pkg-sym (pkg-witness pkg)))


;; (parse-and-create-svtv :file "DT_SB4_HC_8x8_11to0_multgen.sv"
;;                        :topmodule "DT_SB4_HC_8x8_11to0_spec")

;; (value-triple (acl2::tshell-ensure))

;; (verify-svtv-of-mult :topmodule "DT_SB4_HC_8x8_11to0_spec"
;;                      :then-fgl t
;;                      :concl (equal design_res
;;                                    ;; specification:
;;                                    (loghead 12 (* (logext 8 in1)
;;                                                   (logext 8 in2)))))
 
;; (defthmrp-multiplier multiplier-correct
;;   (implies (DT_SB4_HC_8x8_12_spec-autohyps)
;;            (b* (((sv::assocs design_res) ;; output signal name
;;                  (sv::svtv-run (DT_SB4_HC_8x8_12_spec)
;;                                (DT_SB4_HC_8x8_12_spec-autoins))))
;;              (equal design_res
;;                     ;; specification:
;;                     (loghead 12 (* (logext 8 IN1)
;;                                    (logext 8 IN2)))))))
