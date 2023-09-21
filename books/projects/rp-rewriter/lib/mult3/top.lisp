
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

(include-book "misc/file-io" :dir :system)
(include-book "std/io/read-file-objects" :dir :system)
(include-book "std/io/read-file-characters" :dir :system)

(include-book "centaur/bitops/merge" :dir :system)

;; -------------------------------------------------------------------------------------
;; Parse macros.

(progn

  (defttag :write-to-file-okp)

  (defun save-the-svtv-to-file (filename svtv modified-svtv state)
    (declare (xargs :mode :program
                    :stobjs (state)))
    (b* ((svexl (svl::svex-alist-to-svexl-alist (sv::svtv->outexprs svtv)))
         (modified-svexl (and modified-svtv
                              (svl::svex-alist-to-svexl-alist (sv::svtv->outexprs modified-svtv))))
         (ins (sv::svtv->inmasks svtv))
         (outs (sv::svtv->orig-outs svtv))
         (lst `(:ins ,ins :outs ,outs :svexl ,svexl :modified-svexl ,modified-svexl))
         ((mv chan state)
          (open-output-channel! filename :object state)))
      (if chan
          (pprogn
           (acl2::write-objects lst chan state)
           (value ':done))
        (er soft 'write-object-to-file
            "Could not open for writing: ~x0"
            filename))))

  (defun write-string-to-file (filename str state)
    (declare (xargs :mode :program
                    :stobjs (state)))
    (b* (((mv chan state)
          (open-output-channel! filename :object state)))
      (if chan
          (pprogn
           (acl2::write-objects (list str) chan state)
           (value ':done))
        (er soft 'write-string-to-file
            "Could not open for writing: ~x0"
            filename))))

  (defmacro write-string-to-file-event (filename content)
    `(make-event
      (er-progn
       (write-string-to-file ,filename ,content state)
       (value '(value-triple :done)))))

  (defttag nil))


(defmacro parse-and-create-svtv (&key file
                                      topmodule
                                      name
                                      save-to-file
                                      modified-modules-file
                                      stages
                                      cycle-phases)
  (declare (xargs :guard (and (or (stringp file)
                                  (cw "File should be a string~%"))
                              (or (not modified-modules-file)
                                  (stringp modified-modules-file)
                                  (cw "given modified-modules-file should be a string if provided.~%"))
                              (or (not name)
                                  (symbolp name)
                                  (cw "given name should be a symbol~%"))
                              (or (not save-to-file)
                                  (stringp save-to-file)
                                  (cw "save-to-file should be a string if assigned")))))
  `(with-output
     :off :all
     :on (summary error)
     :gag-mode nil
     (make-event
      (b* ((file ',file)
           (modified-modules-file ',modified-modules-file)
           (topmodule ',topmodule)
           (name ',(or name (intern$ (string-upcase topmodule) "RP")))

           ;; (VL) event1
           (vl-design (intern$ (str::cat "*" (symbol-name name) "-VL-DESIGN*") "RP"))
           (vl-event `(acl2::defconsts
                        (,vl-design state)
                        (b* (((mv loadresult state)
                              (vl::vl-load (vl::make-vl-loadconfig
                                            :start-files '(,file)))))
                          (mv (vl::vl-loadresult->design loadresult) state))))
           (modified-vl-design (and modified-modules-file
                                    (intern$ (str::cat "*" (symbol-name name) "MODIFIED-VL-DESIGN*") "RP")))
           (modified-vl-event (and modified-modules-file
                                   `(acl2::defconsts
                                      (,modified-Vl-design state)
                                      (b* (((mv loadresult state)
                                            (vl::vl-load (vl::make-vl-loadconfig
                                                          :start-files '(,modified-modules-file ,file)))))
                                        (mv (vl::vl-loadresult->design loadresult) state)))))

           ;; (SV) event2
           (sv-design (intern$ (str::cat "*" (symbol-name name) "-SV-DESIGN*") "RP"))
           (sv-event `(acl2::defconsts
                        (,sv-design)
                        (b* (((mv errmsg sv-design ?good ?bad)
                              (vl::vl-design->sv-design ,topmodule
                                                        ,vl-design
                                                        (vl::make-vl-simpconfig))))
                          (and errmsg
                               (acl2::raise "~@0~%" errmsg))
                          sv-design)))
           (modified-sv-design (and modified-modules-file
                                    (intern$ (str::cat "*" (symbol-name name) "-MODIFIED-SV-DESIGN*") "RP")))
           (modified-sv-event (and modified-modules-file
                                   `(acl2::defconsts
                                      (,modified-sv-design)
                                      (b* (((mv errmsg sv-design ?good ?bad)
                                            (vl::vl-design->sv-design ,topmodule
                                                                      ,modified-vl-design
                                                                      (vl::make-vl-simpconfig))))
                                        (and errmsg
                                             (acl2::raise "~@0~%" errmsg))
                                        sv-design))))

           ;; (inputs/outputs) event3
           (get-io-event `(local
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
                                 )))))

           ;; (SVTV) event4
           (stages ',stages)
           (cycle-phases ',cycle-phases)
           (svtv-event
            `(progn
               (make-event
                `(sv::defsvtv$ ,',name
                   :mod ,',sv-design
                   ,@(and ',cycle-phases
                          '(:cycle-phases ,cycle-phases))
                   :stages
                   ,(or ',stages
                        `((:label
                           p
                           :inputs ,(loop$ for x in *ins* collect
                                           `(,x ,(intern$ (string-upcase x) "RP")))
                           :outputs ,(loop$ for x in *outs* collect
                                            `(,x ,(intern$ (string-upcase x) "RP"))))))))

               (rp::add-rp-rule ,(intern$ (str::cat (symbol-name name) "-AUTOHYPS") "RP"))
               (rp::add-rp-rule ,(intern$ (str::cat (symbol-name name) "-AUTOINS") "RP"))))

           (modified-name (and modified-modules-file (intern-in-package-of-symbol
                                                      (str::cat "MODIFIED-" (symbol-name name))
                                                      name)))
           (modified-svtv-event
            (and modified-modules-file
                 `(progn
                    (make-event
                     `(sv::defsvtv$ ,',modified-name
                        :mod ,',modified-sv-design
                        ,@(and ',cycle-phases
                               '(:cycle-phases ,cycle-phases))
                        :stages
                        ,(or ',stages
                             `((:label
                                p
                                :inputs ,(loop$ for x in *ins* collect
                                                `(,x ,(intern$ (string-upcase x) "RP")))
                                :outputs ,(loop$ for x in *outs* collect
                                                 `(,x ,(intern$ (string-upcase x) "RP"))))))))

                    (rp::add-rp-rule ,(intern$ (str::cat (symbol-name modified-name) "-AUTOHYPS") "RP"))
                    (rp::add-rp-rule ,(intern$ (str::cat (symbol-name modified-name) "-AUTOINS") "RP")))))

           ;; (SAVE-TO-FILE) event5
           ;; save-to-file can be a string or a symbol. If string use it as
           ;; prefix.
           (save-to-file ',save-to-file)
           (file-name (and save-to-file
                           (str::cat (if (stringp save-to-file) save-to-file "")
                                     (symbol-name name)
                                     ".svexl")))
           (save-to-file-event `(make-event
                                 (er-progn
                                  (save-the-svtv-to-file ',file-name
                                                         (,name)
                                                         ,(and modified-modules-file `(,modified-name))
                                                         state)
                                  (value '(value-triple :invisible))))))
        `(encapsulate
           nil

           ,@(if save-to-file
                 `((local ,vl-event)
                   ,@(and modified-modules-file `((local ,modified-vl-event)))
                   (local ,sv-event)
                   ,@(and modified-modules-file `((local ,modified-sv-event)))
                   (local ,get-io-event)
                   (local ,svtv-event)
                   ,@(and modified-modules-file `((local ,modified-svtv-event)))
                   (local ,save-to-file-event))
               `(,vl-event
                 ,@(and modified-modules-file `(,modified-vl-event))
                 ,sv-event
                 ,@(and modified-modules-file `(,modified-sv-event))
                 ,get-io-event
                 ,svtv-event
                 ,@(and modified-modules-file `(,modified-svtv-event))))

           (value-triple (clear-memoize-tables))
           ;;(value-triple (hons-clear t))
           ;;(value-triple (gc$))
           )))))

;; ---------------------------------------------------------------------------
;; Verify macros.

(defsection generate-proof-summary
  (defmacro start-timer ()
    `(make-event
      (b* (((mv time state)
            (read-run-time state)))
        (mv nil
            `(table mult-timer 'start ,time)
            state))))

  (defun get-time-aux (diff n)
    (if (zp n)
        (str::intstr (floor diff 1))
      (str::cat (get-time-aux (floor diff 10) (1- n))
                (if (equal n 1) "." "")
                (str::intstr (mod (floor diff 1) 10)))))

  (defun get-time (diff host-lisp)
    (if (equal host-lisp 'ccl)
        (get-time-aux (* 1000000 diff) 6)
      (get-time-aux (* 1000 diff) 3)))

  (defmacro end-timer ()
    `(make-event
      (b* (((mv end-time state)
            (read-run-time state))
           (start-time (rfix (cdr (assoc-equal 'start
                                               (table-alist 'mult-timer (w state))))))
           (host (cdr (assoc-equal 'host (table-alist 'host (w state)))))
           (message (str::cat "finished in -- "
                              (get-time (- end-time start-time) host)
                              " seconds --.")))
        (mv nil
            `(progn
               (table mult-timer 'end-message ,message)
               (value-triple (cw ,(str::cat "-- This event " message " --"))))
            state))))

  (progn
    (defttag :write-to-file-okp)

    (defun save-proof-summary-to-file (output-file-name name print-message event  state)
      (declare (xargs :mode :program
                      :stobjs (state)))
      (b* (;; ((mv chan state)
           ;;  (open-input-channel output-file-name :object state))
           ;; ((mv orig-content1 state)
           ;;  (acl2::read-object-all chan state))
           ;; (state (close-input-channel chan state))

           ((mv orig-content1 state)
            (acl2::read-file-as-string output-file-name state))
           (orig-content1 (if (stringp orig-content1) (str::trim orig-content1) ""))
           (failed? (cdr (hons-assoc-equal name (table-alist 'mult-failed (w state)))))
           (end-message (cdr (hons-assoc-equal 'end-message (table-alist 'mult-timer (w state)))))
           (end-message (str::cat (if failed? "The above event " "Proof for this conjecture ") end-message))
           (- (cw "~p0~%~p1~%" (if failed? '"!!! This proof has failed !!!" "") end-message))
           (lst `(,(str::Cat "--- Starting the proofs for "
                             (if (stringp print-message) (str::cat "- " print-message " - ") "")
                             (symbol-name name) " ---~%")
                  ,event
                  ,@(and failed? '("!!! This proof has failed !!!"))
                  ,end-message
                  ,(or orig-content1 "")))
           ((mv chan state)
            (open-output-channel! output-file-name :object state)))
        (if chan
            (pprogn
             (acl2::write-objects lst chan state)
             ;;(print-object$ lst chan state)
             (value ':done))
          (er soft 'write-object-to-file
              "Could not open for writing: ~x0"
              output-file-name))))

    (defttag nil))

  (defmacro save-summary-to-file (name event print-message)
    `(with-output :off :all :gag-mode nil
       (local
        (make-event
         (b* ((book-name (acl2::active-book-name (w state) state))
              (book-name (if (stringp book-name)
                             (car (last (str::strtok book-name (explode "/"))))
                           "interactive"))
              (output-file-name (str::cat "generated-proof-summary/" book-name "-summary.txt")))
           (er-progn
            (save-proof-summary-to-file output-file-name ',name ',print-message ',event state)
            (value '(value-triple :done))))))))

  (defmacro generate-proof-summary (name event &key keep-going print-message)
    `(encapsulate nil
       (local (start-timer))
       ,(if keep-going
            `(make-event
              '(:or ,event
                    (local (table mult-failed ',name t))))
          event)
       (local (end-timer))
       (save-summary-to-file ,name ,event ,print-message)
       )))

(defmacro read-mult-from-file (name read-from-file)
  `(with-output
     :off :all
     :gag-mode nil
     (make-event
      (b* ((__FUNCTION__ 'read-mult-from-file)
           (name ',name)
           (ins-name (intern-in-package-of-symbol (str::cat (symbol-name name) "-INMASKS") name))
           (outs-name (intern-in-package-of-symbol (str::cat (symbol-name name) "-OUTS") name))
           (read-from-file ',read-from-file)
           (filename (str::cat (if (stringp read-from-file) read-from-file "")
                               (symbol-name name)
                               ".svexl"))
           ((mv channel state)
            (open-input-channel filename :object state))
           ((mv content state)
            (acl2::read-object-all channel state))
           (state (close-input-channel channel state))
           ((std::extract-keyword-args ins outs svexl modified-svexl)
            content))
        (mv nil
            `(progn
               (defun ,ins-name ()
                 ',ins)
               (defun ,outs-name ()
                 ',outs)
               (defun ,name ()
                 (svl::svexl-alist-to-svex-alist ',svexl))

               ,@(and modified-svexl
                      `((defun ,(intern-in-package-of-symbol (str::cat "MODIFIED-" (symbol-name name)) name)
                            ()
                          (svl::svexl-alist-to-svex-alist ',modified-svexl)))))
            state)))))


(define verify-svtv-of-mult-fn (&key name
                                     concl
                                     thm-name
                                     (hyp)
                                     (then-fgl 'nil)
                                     (only-fgl 'nil)
                                     (cases 'nil)
                                     (read-from-file 'nil)
                                     (keep-going 'nil)
                                     (print-message 'nil)
                                     (pkg '"RP")
                                     )
  :mode :program
  (acl2::template-subst
   `(progn
      ,@(and read-from-file
             `((with-output :stack :pop
                 (read-mult-from-file ,name
                                      ,read-from-file))))
        (make-event
         (b* ((cases ',cases)
              (keep-going ',keep-going)
              (print-message ',print-message)

              (- (cw "~%-------~%Starting verify-svtv-of-mult for ~p0~%~%" ',name))
              (- (cw "~%--- Starting the proofs for ~s0~s1 ---~%"
                     (if (stringp print-message) (str::cat "- " print-message " - ") "")
                     (symbol-name ',name)))
              
              ;; ---------------
              ;; make decisions based on read-from-file:
              ((mv invars outvars has-modified)
               ,(if read-from-file
                    `(mv (strip-cars (<mult>-inmasks))
                         (remove-equal '&  (acl2::flatten (strip-cdrs (<mult>-outs))))
                         (not (equal (meta-extract-formula 'modified-<mult> state) ''t)))
                  `(mv (remove-equal '& (acl2::flatten (strip-cdrs (sv::svtv->orig-ins (<mult>)))))
                       (remove-equal '&  (acl2::flatten (strip-cdrs (sv::svtv->orig-outs (<mult>)))))
                       (not (equal (meta-extract-formula 'modified-<mult> state) ''t)))))
              ((mv hyps simulate-call modified-simulate-call)
               ,(if read-from-file
                    `(mv (cons 'and
                               (loop$ for x in (<mult>-inmasks) collect
                                      `(unsigned-byte-p ,(integer-length (cdr x))
                                                        ,(car x))))
                         `(sv::svex-alist-eval (<mult>)
                                               (list ,@(loop$ for x in invars collect
                                                              (list 'cons `',x x))))
                         `(sv::svex-alist-eval (modified-<mult>)
                                               (list ,@(loop$ for x in invars collect
                                                              (list 'cons `',x x)))))
                  `(mv '(<mult>-autohyps)
                       '(sv::svtv-run (<mult>) (<mult>-autoins))
                       '(sv::svtv-run (modified-<mult>) (<mult>-autoins)))))
              (hyps (if ',hyp `(and ,',hyp ,hyps) hyps))
              ;; ---------------

              ((acl2::er translated-concl)
               (acl2::translate ',concl t t nil
                                'verify-svtv-of-mult
                                (w state) state))
              (concl-vars (acl2::all-vars translated-concl))
              (free-vars (set-difference$ concl-vars
                                          (append outvars invars)))
              (& (cw "concl vars: ~p0 ~%" concl-vars))
              (- (and free-vars
                      (not (cw "WARNING! THE GIVEN CONCL CONTAINS THESE FREE VARIABLES:~p0~%" free-vars))
                      (not (cw "Available inputs are: ~p0. And outputs are~p1~%" invars outvars))))
              (ignorable-outs (loop$ for x in outvars collect
                                     (intern-in-package-of-symbol
                                      (str::Cat "?" (symbol-name x))
                                      x)))

              (vescmul-event ;;(with-output :stack :pop
               `(,',(if only-fgl 'fgl::def-fgl-thm 'defthmrp-multiplier)
                 ,@(and ,then-fgl `(:then-fgl ,',then-fgl))
                 ,(or ',thm-name '<mult>-is-correct)
                 (implies ,hyps
                          (b* (((sv::svassocs ,@ignorable-outs)
                                ,simulate-call))
                            ,',concl))

                 ,@(and cases `(:cases ,cases))))
                             ;;)

              (modified-equiv-events (and has-modified
                                          `(defsection <mult>-is-correct
                                             (local
                                              (value-triple (acl2::tshell-ensure)))
                                             (with-output :stack :pop
                                               (local
                                                (fgl::def-fgl-thm <mult>--rw-from-original-to-modified
                                                  (implies ,hyps
                                                           (equal ,simulate-call
                                                                  ,modified-simulate-call)))))
                                             (local
                                              (rp::add-rp-rule <mult>--rw-from-original-to-modified
                                                               :rw-direction :both))
                                             ,vescmul-event)))

              (event `(:or
                       (generate-proof-summary
                        ,(or ',thm-name '<mult>)
                        ,(if has-modified modified-equiv-events vescmul-event)
                        :keep-going ,keep-going
                        :print-message ,print-message)
                       (value-triple
                        (cond (',free-vars
                               (hard-error 'verify-svtv-of-mult
                                           "THE GIVEN CONCL CONTAINS THESE FREE VARIABLES: ~p0.~%Available inputs are ~p1.~%Available outputs are ~p2~%"
                                           (list (cons #\0 ',free-vars)
                                                 (cons #\1 ',invars)
                                                 (cons #\2 ',outvars))))
                              ((not ,',then-fgl)
                               (hard-error 'verify-svtv-of-mult
                                           "THE PROOF FAILED. YOU CAN GENERATE COUNTEREXAMPLES BY ~
                                    PASSING \":THEN-FGL T\" AS AN ARGUMENT." nil))
                              (t nil))))))
           (value
            (if ,(or only-fgl then-fgl)
                `(progn (value-triple (acl2::tshell-ensure))
                        (make-event ',event))
              event)))))
   :atom-alist `((<mult> . ,name))
   :str-alist `(("<MULT>" . ,(symbol-name name)))
   :pkg-sym (pkg-witness pkg)))
  

(defmacro verify-svtv-of-mult (&key name
                                    concl
                                    thm-name
                                    (hyp)
                                    (then-fgl 'nil)
                                    (only-fgl 'nil)
                                    (cases 'nil)
                                    (read-from-file 'nil)
                                    (keep-going 'nil)
                                    (print-message 'nil)
                                    (pkg '"RP")
                                    )
  `(make-event
    `(with-output
       :off :all
       ;;:gag-mode nil
       :on (error comment)
       :stack :push
       ,(verify-svtv-of-mult-fn :name ',name
                                :concl ',concl
                                :thm-name ',thm-name
                                :hyp ',hyp
                                :then-fgl ,(and (not only-fgl) then-fgl)
                                :only-fgl ,only-fgl
                                :cases ',(and (not only-fgl) cases)
                                :read-from-file ,read-from-file
                                :keep-going ',keep-going
                                :print-message ',print-message
                                :pkg ,pkg))))

;; (parse-and-create-svtv :file "demo/DT_SB4_HC_64_64_multgen.sv"
;;                        :topmodule "DT_SB4_HC_64_64"
;;                        :name my-multiplier-example
;;                        :save-to-file "parsed/")

;; (verify-svtv-of-mult :name my-multiplier-example
;;                      :concl (equal result
;;                                    (loghead 128 (* (logext 64 in1)
;;                                                    (logext 64 in2))))
;;                      :read-from-file "parsed/")

;; ;; OR:

;; (parse-and-create-svtv :file "demo/DT_SB4_HC_64_64_multgen.sv"
;;                        :topmodule "DT_SB4_HC_64_64"
;;                        :name my-multiplier-example-2)

;; (verify-svtv-of-mult :name my-multiplier-example-2
;;                      :concl (equal result
;;                                    (loghead 128 (* (logext 64 in1)
;;                                                    (logext 64 in2)))))

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

;;;;

(rp::add-rp-rule acl2::nth-slice32$inline)
(rp::add-rp-rule nth-slice)
(rp::add-rp-rule bitops::part-select-width-low$inline)
(rp::add-rp-rule bitops::part-select-width-low)
(rp::add-rp-rule bitops::part-select-low-high)
(rp::add-rp-rule MERGE-4-U32S)
