; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "base")
(include-book "../ranges")

(defmacro test-range (&key input range (successp 't))
  `(assert! (let ((tokens (make-test-tokens ,input)))
              (mv-let (erp val tokens warnings)
                (vl-parse-range :tokens tokens
                                :warnings nil
                                :config *vl-default-loadconfig*)
                (declare (ignore tokens))
                (if erp
                    (prog2$ (cw "ERP is ~x0.~%" erp)
                            (not ,successp))
                  (prog2$ (cw "VAL is ~x0.~%" val)
                          (and ,successp
                               (vl-range-p val)
                               (not warnings)
                               (equal ',range (vl-pretty-range val)))))))))

(test-range :input "[7:0]"
            :range (range 7 0))

(test-range :input "[3:6]"
            :range (range 3 6))

(test-range :input "[7 : 0]"
            :range (range 7 0))

(test-range :input "[foo : bar]"
            :range (range (id "foo") (id "bar")))

(test-range :input "[foo : ]"
            :successp nil)

(test-range :input "[foo]"
            :successp nil)