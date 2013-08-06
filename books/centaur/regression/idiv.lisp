; Copyright David Rager, 2013

; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

(in-package "ACL2")

(include-book "common")

(defmodules *divide-modules*
  (vl::make-vl-loadconfig
   :start-files (list "idiv.v")))

(defconst *divide-translation*
  (VL::VL-TRANSLATION->MODS *DIVIDE-MODULES*))

; (vl::vl-modulelist-flat-warnings
;  (vl::vl-translation->failmods *divide-modules*))

(defconst *divide-module*
  (vl::vl-module->esim
   (vl::vl-find-module "udivider_v5"
                       *divide-translation*)))

(defstv divide-test-vector
  :mod *divide-module*
  :inputs '(("iDIVIDEND" dividend) ("iDIVISOR" divisor) ("iDIVVLD" divvld)
            ("iRESET" reset) ("CLK" clk))
  :outputs '(("oQUOTIENT" quot) ("oREMAINDER" rem) ("oDONE" done)))

(def-gl-thm divide-resets-quotient
  :hyp (and (divide-test-vector-autohyps)
            (equal reset -1))
  :concl (equal (let* ((in-alist (divide-test-vector-autoins))
                       (out-alist (stv-run (divide-test-vector)
                                           in-alist))
                       (quot (cdr (assoc 'quot out-alist))))
                  quot)
                0)
  :g-bindings '((dividend (:g-number (11 12 13 14 15 16 17 18 19)))
                (divisor (:g-number (6 7 8 9 10)))
                (divvld (:g-number (0 1)))
                (clk (:g-number (2 3)))
                (reset (:g-number (4 5)))))

(def-gl-thm divide-resets-everything
  :hyp (and (divide-test-vector-autohyps)
            (equal reset -1))
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
                (clk (:g-number (2 3)))
                (reset (:g-number (4 5)))))
