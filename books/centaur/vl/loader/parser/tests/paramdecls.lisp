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
(include-book "../paramdecls")






(defun test-paramdecls-fn (params type localp range atts names exprs)
  (if (atom params)
      (and (atom names)
           (atom exprs))
    (debuggable-and
     (consp names)
     (consp exprs)
     (not (cw "Inspecting ~x0.~%" (car params)))
     (vl-paramdecl-p (car params))
     (equal type          (vl-paramdecl->type   (car params)))
     (equal localp        (vl-paramdecl->localp (car params)))
     (equal atts          (vl-paramdecl->atts   (car params)))
     (equal range         (and (vl-paramdecl->range (car params))
                               (vl-pretty-range (vl-paramdecl->range (car params)))))
     (equal (car names)   (vl-paramdecl->name   (car params)))
     (equal (car exprs)   (vl-pretty-expr (vl-paramdecl->expr (car params))))
     (test-paramdecls-fn (cdr params) type localp range atts (cdr names) (cdr exprs)))))

(defmacro test-parse-param-declaration
  (&key input type localp range atts names exprs (successp 't))
  `(assert!
    (let ((tokens (make-test-tokens ,input))
          (warnings 'blah-warnings)
          (config   *vl-default-loadconfig*))
      (mv-let (erp val tokens warnings)
        (vl-parse-param-or-localparam-declaration ',atts
                                                  '(:vl-kwd-parameter
                                                    :vl-kwd-localparam))
        (declare (ignore tokens))
        (if erp
            (prog2$ (cw "ERP is ~x0.~%" erp)
                    (and (equal warnings 'blah-warnings)
                         (not ,successp)))
          (prog2$ (cw "VAL is ~x0.~%" val)
                  (and ,successp
                       (equal warnings 'blah-warnings)
                       (test-paramdecls-fn val ',type ',localp ',range
                                           ',atts ',names ',exprs))))))))

(test-parse-param-declaration :input "parameter a = 1"
                              :names ("a")
                              :exprs (1)
                              :range nil
                              :type :vl-plain
                              :atts (("some") ("atts")))

(test-parse-param-declaration :input "parameter a = 1 : 2 : 3"
                              :names ("a")
                              :exprs ((:vl-mintypmax nil 1 2 3))
                              :range nil
                              :type :vl-plain
                              :atts (("some") ("atts")))

(test-parse-param-declaration :input "localparam a = 1 : 2 : 3"
                              :names ("a")
                              :exprs ((:vl-mintypmax nil 1 2 3))
                              :localp t
                              :range nil
                              :type :vl-plain
                              :atts (("some") ("atts")))

(test-parse-param-declaration :input "parameter a = 1, b = 1 : 2 : 3"
                              :names ("a" "b")
                              :exprs (1   (:vl-mintypmax nil 1 2 3))
                              :range nil
                              :type :vl-plain
                              :atts (("some") ("atts")))

(test-parse-param-declaration :input "parameter signed a = 1, b = 1 : 2 : 3"
                              :names ("a" "b")
                              :exprs (1   (:vl-mintypmax nil 1 2 3))
                              :range nil
                              :type :vl-signed
                              :atts (("some") ("atts")))

(test-parse-param-declaration :input "parameter signed [7:8] a = 1, b = 1 : 2 : 3"
                              :names ("a" "b")
                              :exprs (1   (:vl-mintypmax nil 1 2 3))
                              :range (range 7 8)
                              :type :vl-signed
                              :atts (("some") ("atts")))

(test-parse-param-declaration :input "parameter [7:8] a = 1, b = 1 : 2 : 3"
                              :names ("a" "b")
                              :exprs (1   (:vl-mintypmax nil 1 2 3))
                              :range (range 7 8)
                              :type :vl-plain
                              :atts (("some") ("atts")))

(test-parse-param-declaration :input "parameter integer a = 1, b = 1 : 2 : 3"
                              :names ("a" "b")
                              :exprs (1   (:vl-mintypmax nil 1 2 3))
                              :range nil
                              :type :vl-integer
                              :atts (("some") ("atts")))

(test-parse-param-declaration :input "parameter real a = 1, b = 1 : 2 : 3"
                              :names ("a" "b")
                              :exprs (1   (:vl-mintypmax nil 1 2 3))
                              :range nil
                              :type :vl-real
                              :atts (("some") ("atts")))

(test-parse-param-declaration :input "parameter time a = 1, b = 1 : 2 : 3"
                              :names ("a" "b")
                              :exprs (1   (:vl-mintypmax nil 1 2 3))
                              :range nil
                              :type :vl-time
                              :atts (("some") ("atts")))

(test-parse-param-declaration :input "parameter realtime a = 1, b = 1 : 2 : 3"
                              :names ("a" "b")
                              :exprs (1   (:vl-mintypmax nil 1 2 3))
                              :range nil
                              :type :vl-realtime
                              :atts (("some") ("atts")))

;; can only use ranges on signed and plain
(test-parse-param-declaration :input "parameter time [7:0] a = 1, b = 1 : 2 : 3"
                              :successp nil)

(test-parse-param-declaration :input "localparam realtime a = 1, b = 1 : 2 : 3"
                              :names ("a" "b")
                              :exprs (1   (:vl-mintypmax nil 1 2 3))
                              :range nil
                              :localp t
                              :type :vl-realtime
                              :atts (("some") ("atts")))

