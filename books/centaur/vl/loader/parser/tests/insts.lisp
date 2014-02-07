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
(include-book "../insts")

(defmacro test-parse-modinst-args (&key input (successp 't) expect remainder)
  `(with-output
     :off summary
     (assert! (mv-let (erp val tokens warnings)
                (vl-parse-udp-or-module-instantiation
                 nil
                 :tokens (make-test-tokens ,input)
                 :warnings 'warnings
                 :config *vl-default-loadconfig*)
                (if ,successp
                    (and (prog2$ (cw "Erp: ~x0.~%" erp)
                                 (not erp))
                         (prog2$ (cw "VAL: ~x0.~%" val)
                                 (and (vl-modinstlist-p val)
                                      (equal (len val) 1)))
                         (let* ((inst (first val))
                                (args (vl-modinst->portargs inst)))
                           (and
                            (prog2$ (cw "ARGS: ~x0.~%" (vl-pretty-arguments args))
                                    (equal (vl-pretty-arguments args) ',expect))
                            (prog2$ (cw "Atts: ~x0.~%" (vl-modinst->atts inst))
                                    (equal (vl-modinst->atts inst) nil))
                            (prog2$ (cw "Tokens: ~x0.~%" tokens)
                                    (equal tokens ,remainder))
                            (prog2$ (cw "Warnings: ~x0.~%" warnings)
                                    (equal warnings 'warnings)))))
                  ;; Otherwise, we expect it to fail.
                  (prog2$ (cw "Erp: ~x0.~%" erp)
                          erp))))))

(test-parse-modinst-args
 :input "foo inst (a, b, c);"
 :expect (:PLAINARGS ((ID "a") (ID "b") (ID "c"))))

(test-parse-modinst-args
 :input "foo inst ();"
 :expect (:PLAINARGS ()))

(test-parse-modinst-args
 :input "foo inst (a,);"
 :expect (:PLAINARGS ((ID "a") :blank)))

(test-parse-modinst-args
 :input "foo inst (,a);"
 :expect (:PLAINARGS (:blank (ID "a"))))

(test-parse-modinst-args
 :input "foo inst (,);"
 :expect (:PLAINARGS (:blank :blank)))

(test-parse-modinst-args
 :input "foo inst (,,);"
 :expect (:PLAINARGS (:blank :blank :blank)))

(test-parse-modinst-args
 :input "foo inst (,,,);"
 :expect (:PLAINARGS (:blank :blank :blank :blank)))

(test-parse-modinst-args
 :input "foo inst (a,,c);"
 :expect (:PLAINARGS ((ID "a") :blank (ID "c"))))

(test-parse-modinst-args
 :input "foo inst (, a, , c);"
 :expect (:PLAINARGS (:blank (ID "a") :blank (ID "c"))))

(test-parse-modinst-args
 :input "foo inst (.a(1), .b(2));"
 :expect (:NAMEDARGS (("a" <-- 1) ("b" <-- 2))))

(test-parse-modinst-args
 :input "foo inst (.a(1), .b(2), );"
 :successp nil)

(test-parse-modinst-args
 :input "foo inst (.a(1), );"
 :successp nil)

(test-parse-modinst-args
 :input "foo inst (, .a(1));"
 :successp nil)