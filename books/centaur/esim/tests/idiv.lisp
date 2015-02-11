; Copyright David Rager, 2013

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

(in-package "ACL2")

(include-book "common" :ttags :all)

(defmodules *divide-modules*
  (vl2014::make-vl-loadconfig
   :start-files (list "idiv.v")))

(defconst *divide-translation*
  (vl2014::vl-design->mods
   (vl2014::vl-translation->good *DIVIDE-MODULES*)))

; (vl2014::vl-modulelist-flat-warnings
;  (vl2014::vl-translation->failmods *divide-modules*))

(defconst *divide-module*
  (vl2014::vl-module->esim
   (vl2014::vl-find-module "udivider_v5"
                       *divide-translation*)))

(defstv divide-test-vector
  :mod *divide-module*
  :inputs '(("iDIVIDEND" dividend) ("iDIVISOR" divisor) ("iDIVVLD" divvld)
            ("iRESET" reset) ("CLK" 0 ~))
  :outputs '(("oQUOTIENT" _ quot) ("oREMAINDER" _ rem) ("oDONE" _ done)))

(def-gl-thm divide-resets-quotient
  :hyp (and (divide-test-vector-autohyps)
            (equal reset 1))
  :concl (equal (let* ((in-alist (divide-test-vector-autoins))
                       (out-alist (stv-run (divide-test-vector)
                                           in-alist))
                       (quot (cdr (assoc 'quot out-alist))))
                  quot)
                0)
  :g-bindings '((dividend (:g-number (11 12 13 14 15 16 17 18 19)))
                (divisor (:g-number (6 7 8 9 10)))
                (divvld (:g-number (0 1)))
                (reset (:g-number (4 5)))))

(def-gl-thm divide-resets-everything
  :hyp (and (divide-test-vector-autohyps)
            (equal reset 1))
  :concl (let* ((in-alist (divide-test-vector-autoins))
                       (out-alist (stv-run (divide-test-vector) in-alist))
                       (quot (cdr (assoc 'quot out-alist)))
                       (rem (cdr (assoc 'rem out-alist)))
                       (done (cdr (assoc 'done out-alist))))
           (and (equal quot 0)
                (equal rem 0)
                (equal done 0)))

  :g-bindings '((dividend (:g-number (11 12 13 14 15 16 17 18 19)))
                (divisor (:g-number (6 7 8 9 10)))
                (divvld (:g-number (0 1)))
                (reset (:g-number (4 5)))))

