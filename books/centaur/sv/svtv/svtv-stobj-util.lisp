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



(define svtv-data-set-design ((design design-p)
                              svtv-data)
  :returns new-svtv-data
  :guard (modalist-addr-p (design->modalist design))
  (if (hons-equal (design-fix design) (svtv-data->design svtv-data))
      svtv-data
    (b* ((svtv-data (update-svtv-data->flatten-validp nil svtv-data))
         (svtv-data (update-svtv-data->namemap-validp nil svtv-data)))
      (update-svtv-data->design design svtv-data)))
  ///
  (defret svtv-data$c-get-of-<fn>
    (implies (and (equal key (svtv-data$c-field-fix k))
                  (not (equal key :design))
                  (not (equal key :flatten-validp))
                  (not (equal key :namemap-validp)))
             (equal (svtv-data$c-get k new-svtv-data)
                    (svtv-data$c-get key svtv-data))))

  (defret svtv-data$c->design-of-<fn>
    (equal (svtv-data$c->design new-svtv-data)
           (design-fix design))))


(define svtv-data-maybe-compute-flatten (svtv-data)
  :returns (mv err new-svtv-data)
  (if (svtv-data->flatten-validp svtv-data)
      (mv nil svtv-data)
    (b* ((svtv-data (update-svtv-data->flatnorm-validp nil svtv-data))
         (svtv-data (update-svtv-data->phase-fsm-validp nil svtv-data))
         (svtv-data (update-svtv-data->cycle-fsm-validp nil svtv-data))
         (svtv-data (update-svtv-data->pipeline-validp nil svtv-data))
         (svtv-data (update-svtv-data->namemap-validp nil svtv-data)))
      (svtv-data-compute-flatten svtv-data)))
  ///
  (defret svtv-data$c-get-of-<fn>
    (implies (and (equal key (svtv-data$c-field-fix k))
                  (not (equal key :flatten))
                  (not (equal key :flatten-validp))
                  (not (equal key :moddb))
                  (not (equal key :aliases))
                  (not (equal key :flatnorm-validp))
                  (not (equal key :phase-fsm-validp))
                  (not (equal key :cycle-fsm-validp))
                  (not (equal key :pipeline-validp))
                  (not (equal key :namemap-validp)))
             (equal (svtv-data$c-get k new-svtv-data)
                    (svtv-data$c-get key svtv-data))))

  (defret svtv-data$c->flatten-validp-of-<fn>
    (implies (not err)
             (equal (svtv-data$c->flatten-validp new-svtv-data)
                    t))))



(define svtv-data-maybe-compute-flatnorm (svtv-data (setup flatnorm-setup-p))
  :returns new-svtv-data
  :guard (svtv-data->flatten-validp svtv-data)
  (if (and (svtv-data->flatnorm-validp svtv-data)
           (equal (flatnorm-setup-fix setup) (svtv-data->flatnorm-setup svtv-data)))
      svtv-data
    (b* ((svtv-data (update-svtv-data->flatnorm-validp nil svtv-data))
         (svtv-data (update-svtv-data->phase-fsm-validp nil svtv-data))
         (svtv-data (update-svtv-data->flatnorm-setup setup svtv-data)))
    (svtv-data-compute-flatnorm svtv-data)))
  ///
  (defret svtv-data$c-get-of-<fn>
    (implies (and (equal key (svtv-data$c-field-fix k))
                  (not (equal key :flatnorm))
                  (not (equal key :flatnorm-setup))
                  (not (equal key :phase-fsm-validp))
                  (not (equal key :flatnorm-validp)))
             (equal (svtv-data$c-get k new-svtv-data)
                    (svtv-data$c-get key svtv-data))))

  (defret svtv-data$c->flatnorm-validp-of-<fn>
    (implies (not err)
             (equal (svtv-data$c->flatnorm-validp new-svtv-data)
                    t)))

  (defret svtv-data$c->flatnorm-setup-of-<fn>
    (equal (svtv-data$c->flatnorm-setup new-svtv-data)
           (flatnorm-setup-fix setup))))

(define svtv-data-maybe-compute-namemap ((user-names svtv-namemap-p) svtv-data)
  :guard (svtv-data->flatten-validp svtv-data)
  :returns (mv err new-svtv-data)
  (if (and (equal (svtv-data->user-names svtv-data) (svtv-namemap-fix user-names))
           (svtv-data->namemap-validp svtv-data))
      (mv nil svtv-data)
    (b* ((svtv-data (update-svtv-data->namemap-validp nil svtv-data))
         (svtv-data (update-svtv-data->user-names user-names svtv-data))
         (svtv-data (update-svtv-data->pipeline-validp nil svtv-data)))
      (svtv-data-compute-namemap svtv-data)))
  ///
  (defret svtv-data$c-get-of-<fn>
    (implies (and (equal key (svtv-data$c-field-fix k))
                  (not (equal key :namemap))
                  (not (equal key :namemap-validp))
                  (not (equal key :user-names))
                  (not (equal key :pipeline-validp)))
             (equal (svtv-data$c-get k new-svtv-data)
                    (svtv-data$c-get key svtv-data))))

  (defret svtv-data$c->namemap-validp-of-<fn>
    (implies (not err)
             (equal (svtv-data$c->namemap-validp new-svtv-data)
                    t)))

  (defret svtv-data$c->user-names-of-<fn>
    (implies (not err)
             (equal (svtv-data$c->user-names new-svtv-data)
                    (svtv-namemap-fix user-names)))))

         
