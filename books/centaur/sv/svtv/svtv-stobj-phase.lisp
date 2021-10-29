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
(include-book "design-fsm")

(define svtv-data-compute-phase-fsm (svtv-data)
  :guard (and (svtv-data->flatnorm-validp svtv-data)
              (not (svtv-data->cycle-fsm-validp svtv-data)))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable svtv-data$ap))))
  :returns new-svtv-data
  (b* ((svtv-data (update-svtv-data->phase-fsm (svtv-compose-assigns/delays
                                                (svtv-data->flatnorm svtv-data)
                                                (svtv-data->phase-fsm-setup svtv-data))
                                               svtv-data)))
    (update-svtv-data->phase-fsm-validp t svtv-data))
  ///
  (defret svtv-data$c-get-of-<fn>
    (implies (and (equal key (svtv-data$c-field-fix k))
                  (not (equal key :phase-fsm))
                  (not (equal key :phase-fsm-validp)))
             (equal (svtv-data$c-get k new-svtv-data)
                    (svtv-data$c-get key svtv-data))))

  (defret phase-fsm-validp-of-<fn>
    (svtv-data$c->phase-fsm-validp new-svtv-data)))

(define svtv-data-maybe-compute-phase-fsm (svtv-data
                                           (setup phase-fsm-config-p))
  :guard (svtv-data->flatnorm-validp svtv-data)
  :returns new-svtv-data
  (if (and (svtv-data->phase-fsm-validp svtv-data)
           (equal (phase-fsm-config-fix setup)
                  (svtv-data->phase-fsm-setup svtv-data)))
      svtv-data
    (b* ((svtv-data (update-svtv-data->cycle-fsm-validp nil svtv-data))
         (svtv-data (update-svtv-data->phase-fsm-validp nil svtv-data))
         (svtv-data (update-svtv-data->phase-fsm-setup setup svtv-data)))
      (svtv-data-compute-phase-fsm svtv-data)))
  ///
  (defret svtv-data$c-get-of-<fn>
    (implies (and (equal key (svtv-data$c-field-fix k))
                  (not (equal key :phase-fsm-validp))
                  (not (equal key :phase-fsm-setup))
                  (not (equal key :cycle-fsm-validp))
                  (not (equal key :phase-fsm)))
             (equal (svtv-data$c-get k new-svtv-data)
                    (svtv-data$c-get key svtv-data))))

  (defret phase-fsm-setup-of-<fn>
    (equal (svtv-data$c->phase-fsm-setup new-svtv-data)
           (phase-fsm-config-fix setup)))

  (defret phase-fsm-validp-of-<fn>
    (svtv-data$c->phase-fsm-validp new-svtv-data)))
  
