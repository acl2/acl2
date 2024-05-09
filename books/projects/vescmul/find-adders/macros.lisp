
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

(include-book "../fnc-defs")
(include-book "centaur/svl/portcullis" :dir :system)
;;(include-book "centaur/sv/svex/lists" :dir :system)
(include-book "centaur/misc/sneaky-load" :dir :system)
(include-book "centaur/fgl/portcullis" :dir :system)
(include-book "std/util/defconsts" :dir :system)

(defmacro defthmrp-multiplier (&rest args)
  `(make-event
    (b* ((args ',args)
         (then-fgl (cdr (extract-keyword-from-args :then-fgl args)))
         (args (remove-keywords-from-args '(:then-fgl) args)))
      `(encapsulate
         nil

         (local
          (disable-rules '((:meta svl::svex-alist-eval-meta
                                  .
                                  sv::svex-alist-eval))))

         (local
          (enable-rules '(;;(:rewrite trigger-rewrite-adders-in-svex-alist)
                          (:meta rewrite-adders-in-svex-alist
                                 .
                                 sv::svex-alist-eval))))
         (defthm-with-temporary-warrants
           ,@args
           :fns ,*adder-fncs*
           :defthm-macro ,(if then-fgl 'defthmrp-then-fgl 'defthmrp)
           )
         ))))

;;;;;

(defun remove-keywords-from-args (keywords args)
  (if (or (atom args)
          (atom (cdr args)))
      args
    (if (member-equal (car args) keywords)
        (remove-keywords-from-args keywords (cddr args))
      (cons (car args)
            (remove-keywords-from-args keywords (cdr args))))))

(defwarrant str::fast-string-append)

(defthmd car-and-cdr-when-not-consp
  (implies (not (consp x))
           (and (equal (car x) nil)
                (equal (cdr x) nil))))

(progn
  (defun defthm-with-temporary-warrants-fn (thm-name thm-body args
                                                     state)
    (declare (xargs :stobjs state
                    :mode :program))
    (b* ((fns (cdr (extract-keyword-from-args :fns args)))
         (defthm-macro (extract-keyword-from-args :defthm-macro args))
         (defthm-macro (If defthm-macro (cdr defthm-macro) 'defthm))
         (args (remove-keywords-from-args '(:defthm-macro :fns) args))
         (local-thm-name
          (intern-in-package-of-symbol (str::cat (symbol-name thm-name)
                                                 "-LOCAL-WITH-TEMP-WARRANTS")
                                       thm-name))

         (all-badges (cdr (assoc-equal :BADGE-USERFN-STRUCTURE
                                       (table-alist 'acl2::badge-table (w state)))))

         (- (loop$ for x in fns always
                   (or (assoc-equal x all-badges)
                       (hard-error 'warrant-check
                                   "Warrant cannot be found for ~p0. Please call (defwarrant ~p0) (or pass its actual function name, not its macro alias).~%"
                                   (list (cons #\0 x))))))

         (- (loop$ for x in fns
                   always
                   (or (equal (third (caddr (assoc-equal x all-badges)))
                              1)
                       (hard-error 'return-count-check
                                   "Right now, this program only supports functions that return only one value. However, ~p0 violates that.~%"
                                   (list (cons #\0 x))))))

         (my-badge-userfn-body
          (loop$ for x in fns
                 collect
                 `((eq fn ',x)
                   ',(caddr (assoc-equal x all-badges)))))

         ;;(- (cw "my-badge-userfn-body: ~p0~%" my-badge-userfn-body))

         (warrant-hyps (loop$ for x in fns collect
                              `(,(intern-in-package-of-symbol
                                  (str::cat "APPLY$-WARRANT-"
                                            (symbol-name x))
                                  x))))
         (my-apply$-userfn-body
          (loop$ for x in fns
                 collect
                 `((eq fn ',x)
                   (ec-call
                    (,x
                     ,@(loop$ for i
                              from 0 to (1- (second (caddr (assoc-equal x all-badges))))
                              collect
                              `(nth ,i args)))))))

         (warrant-bindings-for-hints
          (loop$ for x in warrant-hyps collect
                 (append x '((lambda () t)))))

         )
      `(encapsulate
         nil
          (with-output
            :off :all 
            :on (error summary comment)
            :gag-mode :goals
            ;;:stack :pop
            (local
             (,defthm-macro ,local-thm-name
               (implies (and ,@warrant-hyps)
                        ,thm-body)
               ,@args)))

         ;;(with-output :off :all :on (error) :gag-mode nil
           (local
            (defun my-badge-userfn (fn)
              (declare (xargs :guard t))
              (cond ,@my-badge-userfn-body)))
           ;;)

         ;;(with-output :off :all :on (error) :gag-mode nil
           (local
            (defun my-apply$-userfn (fn args)
              (declare (xargs :guard (True-listp args)))
              (cond ,@my-apply$-userfn-body)))
           ;;)

         ;; (with-output
         ;;   :off :all
         ;;   :gag-mode nil
         ;;   ;;:on (summary error)
         ;;   :stack :pop
           (with-output
             :off :all
             :stack :pop
             :gag-mode t
             :summary-off (acl2::rules acl2::steps acl2::hint-events time)
             :on (error summary)
             (defthm ,thm-name
               ,thm-body
               :otf-flg t
               :hints (("Goal"
                        :use ((:functional-instance
                               ,local-thm-name
                               (apply$-userfn my-apply$-userfn)
                               (badge-userfn my-badge-userfn)
                               ,@warrant-bindings-for-hints
                               ))

                        :expand ((:free (x y)
                                        (nth x y))
                                 (:free (x y)
                                        (take x y)))
                        :in-theory
                        (union-theories
                         (theory 'minimal-theory)
                         '(car-and-cdr-when-not-consp
                           my-apply$-userfn
                           my-badge-userfn
                           not
                           zp
                           (:definition nth)
                           take
                           car-cons
                           cdr-cons
                           (:executable-counterpart acl2::apply$-badgep)
                           (:executable-counterpart car)
                           (:executable-counterpart cdr)
                           (:executable-counterpart equal)
                           (:executable-counterpart my-badge-userfn))))
                       #|(and stable-under-simplificationp
                       '(:in-theory (e/d () ())))|#
                       )))
           ;;)

         )))

  (defmacro defthm-with-temporary-warrants (thm-name thm-body
                                                     &rest args)
    `(with-output
       :off :all
       :gag-mode t
       :on (error)
       :stack :push
       (make-event
        (defthm-with-temporary-warrants-fn ',thm-name ',thm-body ',args state)))
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Export verilog after adders are found.

(acl2::defconsts *adder-verilog-modules*
  "
module ha_c_chain(input a, input b, output o);
   assign o = a & b;
endmodule

module ha_s_chain(input a, input b, output o);
    assign o = a ^ b;
endmodule

module ha_1_c_chain(input a, input b, output o);
    assign o = a | b;
endmodule

module ha_1_s_chain(input integer m, input a, input b, output o);
    assign o = (m == 10) ? a ^ b : a ^ b ^ 1'b1;
endmodule

module fa_c_chain(input m, input a, input b, input c, output o);
    assign o = a & b | a & c | b & c;
endmodule

module fa_s_chain(input a, input b, input c, output o);
    assign o = a ^ b ^ c;
endmodule

module full_adder(input a, input b, input c, output [1:0] o);
    assign o = {a&b | a&c | b&c, a ^ b ^ c};
endmodule

module half_adder(input a, input b, output [1:0] o);
    assign o = {a&b, a^b};
endmodule
")

;; (FGL::FGL-INTERP-CP CLAUSE #@333# FGL::INTERP-ST STATE)

(defmacro export-to-verilog-after-adder-detection (module-name &key
                                                               (sanity-check 'nil))
  `(make-event
    (b* (((mv svexl-alist state) (acl2::sneaky-load 'after-all state))
         (svex-alist (svl::svexl-alist-to-svex-alist svexl-alist))
         (config (svex-reduce-w/-env-config-1))
         (extra-lines (list *adder-verilog-modules*))
         ((acl2::er parse-events-for-sanity-check)
          (svl::svex-alist-to-verilog-fn svex-alist ',module-name
                                         :extra-lines extra-lines
                                         :config config)))
      (if ,sanity-check
          (value
           `(encapsulate
              nil
              (with-output :off :all :on (error) :gag-mode nil
                (progn ,@parse-events-for-sanity-check
                       (local
                        (acl2::defconsts (*orig-svex-alist* state)
                          (acl2::sneaky-load 'orig-svex-alist state)))))
              (value-triple (acl2::tshell-ensure))
              (local
               (make-event
                `(:or
                  ,(if (or ,(equal ,sanity-check :rp)
                           ,(equal ,sanity-check :rp-then-fgl))
                       `(progn (add-rp-rule svl::exported-design-svtv-autohyps)
                               (add-rp-rule svl::exported-design-svtv-autoins)
                               ;; (disable-meta-rules s-c-spec-meta)
                               ;; (disable-rules '(S-C-SPEC-OPENER-ERROR))
                               ;; (disable-postprocessor unpack-booth-general-postprocessor)
                               (defthmrp-multiplier sanity-check
                                 ,@(and ,(equal ,sanity-check :rp-then-fgl) `(:then-fgl t))
                                 (implies (svl::exported-design-svtv-autohyps)
                                          (b* ((orig-out (sv::svex-alist-eval *orig-svex-alist*
                                                                              (svl::exported-design-svtv-autoins)))
                                               (exported-out (sv::svtv-run (svl::exported-design-svtv)
                                                                           (svl::exported-design-svtv-autoins))))
                                            (equal orig-out exported-out)))))
                     `(fgl::fgl-thm
                       (implies (svl::exported-design-svtv-autohyps)
                                (b* ((orig-out (sv::svex-alist-eval *orig-svex-alist*
                                                                    (svl::exported-design-svtv-autoins)))
                                     (exported-out (sv::svtv-run (svl::exported-design-svtv)
                                                                 (svl::exported-design-svtv-autoins)))
                                     (- (cw "~%Output values of the original design: ~p0~%" orig-out))
                                     (- (cw "~%Output values of the exported design: ~p0~%" exported-out)))
                                  (equal orig-out exported-out)))))
                  (value-triple (hard-error 'export-to-verilog-after-adder-detection
                                            "Sanity check failed. Please see the counterexample above~%"
                                            nil)))))
              (value-triple :sanity-check-passed)))
        (value '(value-triple :done))))))
