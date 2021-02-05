; Centaur SV Hardware Verification Tutorial
; Copyright (C) 2016 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>


(in-package "SV")

(include-book "svtv-stobj")
(include-book "pipeline")

(local (include-book "std/util/termhints" :dir :system))
(local (defstub hq (x) nil))
(local (acl2::termhint-add-quotesym hq))

(local (in-theory (disable hons-dups-p)))

;; (local (defret no-dups-when-equal-svex-alist-keys-<fn>
;;          (implies (and (equal (svex-alist-keys y)
;;                               (svex-alist-keys (svtv-fsm->nextstate fsm)))
;;                        (not err))
;;                   (no-duplicatesp-equal (svex-alist-keys y)))
;;          :fn svtv-design-to-fsm))

(local (defthm svtv-data$c-pipeline-okp-of-compile
         (b* ((fsm (svtv-data$c->cycle-fsm svtv-data))
              ((pipeline-setup setup) (svtv-data$c->pipeline-setup svtv-data))
              (outvars (svtv-probealist-outvars setup.probes))
              (outs (svtv-fsm-run-compile setup.inputs setup.overrides setup.initst
                                                  (make-svtv-fsm :base-fsm fsm
                                                                 :namemap (svtv-data$c->namemap svtv-data))
                                                  outvars
                                                  rewrite))
              (result (svtv-probealist-extract-alist setup.probes outs)))
           (implies (equal (svex-alist-keys setup.initst)
                           (svex-alist-keys (base-fsm->nextstate fsm)))
                    (svtv-data$c-pipeline-okp svtv-data result)))
         :hints(("Goal" :in-theory (enable svtv-data$c-pipeline-okp)))))


(define svtv-data-compute-pipeline (svtv-data &key ((rewrite booleanp) 't))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              ;; (svtv-data->flatten-validp svtv-data)
              ;; (svtv-data->namemap-validp svtv-data)
              (svtv-data->cycle-fsm-validp svtv-data)
              (equal (svex-alist-keys (pipeline-setup->initst (svtv-data->pipeline-setup svtv-data)))
                     (svex-alist-keys (base-fsm->nextstate (svtv-data->cycle-fsm svtv-data)))))
  :guard-debug t
  :guard-hints (("goal" :do-not-induct t)
                (and stable-under-simplificationp
                     '(:in-theory (enable svtv-data$ap))))
  :returns new-svtv-data
  (b* ((fsm (svtv-data->cycle-fsm svtv-data))
       ((pipeline-setup setup) (svtv-data->pipeline-setup svtv-data))
       (outvars (svtv-probealist-outvars setup.probes))
       (outs (make-fast-alistlist (svtv-fsm-run-compile
                                   setup.inputs setup.overrides setup.initst
                                   (make-svtv-fsm :base-fsm fsm
                                                  :namemap (svtv-data->namemap svtv-data))
                                   outvars rewrite)))
       (result (svtv-probealist-extract-alist setup.probes outs))
       (- (fast-alistlist-clean outs))
       (svtv-data (update-svtv-data->pipeline result svtv-data)))
    (update-svtv-data->pipeline-validp t svtv-data))
  ///
  (defret svtv-data$c-get-of-<fn>
    (implies (and (equal key (svtv-data$c-field-fix k))
                  (not (equal key :pipeline))
                  (not (equal key :pipeline-validp)))
             (equal (svtv-data$c-get k new-svtv-data)
                    (svtv-data$c-get key svtv-data))))

  (defret svtv-data$c->pipeline-validp-of-<fn>
    (equal (svtv-data$c->pipeline-validp new-svtv-data) t)))


(define svtv-data-maybe-compute-pipeline ((pipeline-setup pipeline-setup-p)
                                          svtv-data
                                          &key ((rewrite booleanp) 't))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              (svtv-data->cycle-fsm-validp svtv-data)
              (equal (svex-alist-keys (pipeline-setup->initst pipeline-setup))
                     (svex-alist-keys (base-fsm->nextstate (svtv-data->cycle-fsm svtv-data)))))
  :returns new-svtv-data
  (if (and (equal (pipeline-setup-fix pipeline-setup)
                  (svtv-data->pipeline-setup svtv-data))
           (svtv-data->pipeline-validp svtv-data))
      svtv-data
    (b* ((svtv-data (update-svtv-data->pipeline-validp nil svtv-data))
         (svtv-data (update-svtv-data->pipeline-setup pipeline-setup svtv-data)))
      (svtv-data-compute-pipeline svtv-data :rewrite rewrite)))
  ///
  (defret svtv-data$c-get-of-<fn>
    (implies (and (equal key (svtv-data$c-field-fix k))
                  (not (equal key :pipeline))
                  (not (equal key :pipeline-validp))
                  (not (equal key :pipeline-setup)))
             (equal (svtv-data$c-get k new-svtv-data)
                    (svtv-data$c-get key svtv-data))))

  (defret svtv-data$c->pipeline-validp-of-<fn>
    (equal (svtv-data$c->pipeline-validp new-svtv-data) t))

  (defret svtv-data$c->pipeline-setup-of-<fn>
    (equal (svtv-data$c->pipeline-setup new-svtv-data)
           (pipeline-setup-fix pipeline-setup))))
