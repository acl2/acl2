
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

(defmacro parse-and-create-svtv (&key file topmodule)
  `(with-output
     :off :all
     :on (summary error)
     :gag-mode nil
     (make-event
      (b* ((file ',file)
           (topmodule ',topmodule)
           (topmodule-sym (intern$ (string-upcase topmodule) "RP"))
           (vl-design (intern$ (str::cat "*" (string-upcase topmodule) "-VL-DESIGN*")
                               "RP"))
           (sv-design (intern$ (str::cat "*" (string-upcase topmodule) "-SV-DESIGN*")
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
            `(sv::defsvtv$ ,',topmodule-sym
               :mod ,',sv-design
               :inputs ',(loop$ for x in *ins* collect
                                `(,x ,(intern$ (string-upcase x) "RP")))
               :outputs ',(loop$ for x in *outs* collect
                                 `(,x ,(intern$ (string-upcase x) "RP")))))

           (rp::add-rp-rule ,(intern$ (str::cat (string-upcase topmodule) "-AUTOHYPS") "RP"))
           (rp::add-rp-rule ,(intern$ (str::cat (string-upcase topmodule) "-AUTOINS") "RP"))

           (value-triple (clear-memoize-tables))
           (value-triple (hons-clear t))
           (value-triple (gc$))
           )))))   


;; (parse-and-create-svtv :file "DT_SB4_HC_8x8_12_multgen.sv"
;;                        :topmodule "DT_SB4_HC_8x8_12_spec")


;; (defthmrp-multiplier multiplier-correct
;;   (implies (DT_SB4_HC_8x8_12_spec-autohyps)
;;            (b* (((sv::assocs design_res) ;; output signal name
;;                  (sv::svtv-run (DT_SB4_HC_8x8_12_spec)
;;                                (DT_SB4_HC_8x8_12_spec-autoins))))
;;              (equal design_res
;;                     ;; specification:
;;                     (loghead 12 (* (logext 8 IN1)
;;                                    (logext 8 IN2)))))))
