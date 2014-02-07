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
(include-book "../strengths")

(defmacro test-drive/charge-strength (&key input expect (successp 't))
  `(assert! (let ((tokens (make-test-tokens ,input))
                  (warnings nil)
                  (config *vl-default-loadconfig*))
              (mv-let (erp val tokens warnings)
                (vl-parse-drive-strength-or-charge-strength)
                (declare (ignore tokens))
                (if erp
                    (prog2$
                     (cw "ERP is ~x0.~%" erp)
                     (not ,successp))
                  (prog2$
                   (cw "VAL is ~x0.~%" val)
                   (debuggable-and ,successp
                                   (equal val ,expect)
                                   (not warnings))))))))

(test-drive/charge-strength :input "(supply0, pull1)"
                            :expect (make-vl-gatestrength
                                     :zero :vl-supply
                                     :one :vl-pull))

(test-drive/charge-strength :input "(weak1, highz0)"
                            :expect (make-vl-gatestrength
                                     :zero :vl-highz
                                     :one :vl-weak))

(test-drive/charge-strength :input "(strong0, pull1)"
                            :expect (make-vl-gatestrength
                                     :zero :vl-strong
                                     :one :vl-pull))

(test-drive/charge-strength :input "(strong0, weak0)"
                            :successp nil)

(test-drive/charge-strength :input "(highz0, highz1)"
                            :successp nil)

(test-drive/charge-strength :input "(supply0, supply1, weak0, weak1)"
                            :successp nil)

(test-drive/charge-strength :input "(small)"
                            :expect :vl-small)

(test-drive/charge-strength :input "(medium)"
                            :expect :vl-medium)

(test-drive/charge-strength :input "(large)"
                            :expect :vl-large)

(test-drive/charge-strength :input "(huge)"
                            :successp nil)

(test-drive/charge-strength :input "(supply0)"
                            :successp nil)
