; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")
(include-book "range-tools")
(include-book "modnamespace")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))


(define vl-find-net/reg-range ((name   stringp)
                               (mod    vl-module-p)
                               (ialist (equal ialist (vl-make-moditem-alist mod))))
  :returns (mv successp maybe-range)
  :enabled t
  :hooks ((:fix :args ((mod vl-module-p))))
  :guard-hints(("Goal" :in-theory (enable vl-slow-find-net/reg-range
                                          vl-find-moduleitem)))
  (mbe :logic (vl-slow-find-net/reg-range name mod)
       :exec
       (b* ((find (vl-fast-find-moduleitem name mod ialist))
            ((unless (and find
                          (eq (tag find) :vl-vardecl)
                          (vl-simplevar-p find)))
             (mv nil nil)))
         (mv t (vl-simplevar->range find)))))
