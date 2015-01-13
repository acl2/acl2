; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Jared Davis <jared@centtech.com>

; fvq bash
; ../bin/vl shell
(lp)
(in-package "VL")
(set-debugger-enable t)
(break-on-error t)

(defconst *lintconfig*
  (make-vl-lintconfig :start-files (list "./lucid1/temp.v")))

(defun vl-lint-report-wrap (lintresult state)
  (declare (xargs :mode :program :stobjs state))
  (vl-lint-report lintresult state))

(defconsts (*loadres* state)
  (b* (((vl-lintconfig config) *lintconfig*)
       (loadconfig (make-vl-loadconfig
                    :edition       config.edition
                    :strictp       config.strict
                    :start-files   config.start-files
                    :search-path   config.search-path
                    :search-exts   config.search-exts
                    :include-dirs  config.include-dirs)))
    (vl-load loadconfig)))

(vl-design->packages (vl-loadresult->design *loadres*))

(vl-trace-warnings)


;; Lucid Tracing

(trace$ (vl-luciddb-mark
         :entry (list 'vl-luciddb-mark
                      mtype
                      (with-local-ps (vl-pp-lucidkey key))
                      :occ (with-local-ps (vl-pp-lucidocc occ)))
         :exit (list 'vl-luciddb-mark)))

(trace$ (vl-scopestack-push
         :entry (list 'vl-scopestack-push
                      (vl-scope->name scope)
                      (vl-scopestack->path x))
         :exit (list 'vl-scopestack-push
                     (vl-scopestack->path (first values)))))

(trace$ (vl-rhsatom-lucidcheck
         :entry (list 'vl-rhsatom-lucidcheck
                      (vl-pps-expr x)
                      :ss (with-local-ps (vl-pp-scopestack-path ss))
                      :st (vl-pps-lucidstate st)
                      :raw x)
         :exit (let ((st (first acl2::values)))
                 (list 'vl-rhsatom-lucidcheck
                       (vl-pps-lucidstate st)))))

(trace$ (vl-rhsexpr-lucidcheck$notinline
         :entry (list 'vl-rhsexpr-lucidcheck
                      (vl-pps-expr x)
                      :ss (with-local-ps (vl-pp-scopestack-path ss))
                      :st (vl-pps-lucidstate st)
                      :raw x)
         :exit (let ((st (first acl2::values)))
                 (list 'vl-rhsexpr-lucidcheck
                       (vl-pps-lucidstate st)))))

(trace$ (vl-lhsexpr-lucidcheck$notinline
         :entry (list 'vl-lhsexpr-lucidcheck
                      (vl-pps-expr x)
                      :ss (with-local-ps (vl-pp-scopestack-path ss))
                      :st (vl-pps-lucidstate st)
                      :raw x)
         :exit (let ((st (first acl2::values)))
                 (list 'vl-lhsexpr-lucidcheck
                       (vl-pps-lucidstate st)))))


;; (trace$ (vl-initial-lucidcheck
;;          :entry (list 'vl-initial-lucidcheck
;;                       (with-local-ps (vl-pp-initial x))
;;                       :ss (with-local-ps (vl-pp-scopestack-path ss))
;;                       :st (vl-pps-lucidstate st))
;;          :exit (let ((st (first acl2::values)))
;;                  (list 'vl-initial-lucidcheck
;;                        (vl-pps-lucidstate st)))))

;; (trace$ (vl-fundecl-lucidcheck
;;          :entry (list 'vl-fundecl-lucidcheck
;;                       (with-local-ps (vl-pp-fundecl x))
;;                       :ss (with-local-ps (vl-pp-scopestack-path ss))
;;                       :st (vl-pps-lucidstate st))
;;          :exit (let ((st (first acl2::values)))
;;                  (list 'vl-fundecl-lucidcheck
;;                        (vl-pps-lucidstate st)))))

;; (trace$ (vl-package-lucidcheck
;;          :entry (list 'vl-package-lucidcheck
;;                       (with-local-ps (vl-pp-package x))
;;                       :ss (with-local-ps (vl-pp-scopestack-path ss))
;;                       :st (vl-pps-lucidstate st))
;;          :exit (let ((st (first acl2::values)))
;;                  (list 'vl-package-lucidcheck
;;                        (vl-pps-lucidstate st)))))



(ld "centaur/jared-customization.lsp" :dir :system)
(acl2::with-redef
  (define vl-design-lucid ((x vl-design-p)
                           &key
                           ((paramsp booleanp) 't))
    :returns (new-x vl-design-p)
    :guard-debug t
    (b* ((x  (cwtime (hons-copy (vl-design-fix x))
                     :name vl-design-lucid-hons
                     :mintime 1))
         (ss (vl-scopestack-init x))
         (st (cwtime (vl-lucidstate-init x :paramsp paramsp)))
         (st (cwtime (vl-design-lucidcheck-main x ss st)))
         (reportcard (cwtime (vl-lucid-dissect st))))
      (vl-scopestacks-free)

      ;; Just debugging
      (vl-cw-ps-seq (vl-pp-lucidstate st))
      (vl-cw-ps-seq (vl-print-reportcard reportcard :elide nil))
      (vl-apply-reportcard x reportcard))))

(defconsts *lintres*
  (run-vl-lint-main (vl-loadresult->design *loadres*)
                    *lintconfig*))

(vl-lint-report-wrap *lintres* state)


(trace$ (vl-fundecl-exprsize :entry
                             (list 'vl-fundecl-exprsize
                                   :x        (with-local-ps (vl-pp-fundecl x))
                                   :ss       (with-local-ps (vl-pp-scopestack-path ss))
                                   :warnings (with-local-ps (vl-print-warnings warnings)))
                             :exit
                             (b* (((list okp warnings new-x) acl2::values))
                               (list 'vl-fundecl-exprsize
                                     :okp      okp
                                     :warnings (with-local-ps (vl-print-warnings warnings))
                                     :new-x    (with-local-ps (vl-pp-fundecl new-x))))))






