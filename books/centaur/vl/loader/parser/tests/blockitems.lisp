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
(include-book "../blockitems")

(defun test-vardecls-fn (vars ; produced by the parser
                         constp
                         varp
                         lifetime
                         type
                         atts
                         names
                         dims
                         initvals)
  (b* (((when (atom vars))
        (and (atom names)
             (atom dims)
             (atom initvals)))
       (v1 (car vars))
       ((unless (vl-vardecl-p v1))
        (cw "Not even a valid variable decl: ~x0." v1))
       ((vl-vardecl v1) v1))
    (debuggable-and
     (consp names)
     (consp dims)
     (consp initvals)
     (not (cw "Inspecting ~x0.~%" (car vars)))
     (equal (car names)    v1.name)
     (equal (car dims)     (vl-pretty-packeddimensionlist v1.dims))
     (equal (car initvals) (and v1.initval (vl-pretty-expr v1.initval)))
     (equal constp         v1.constp)
     (equal varp           v1.varp)
     (equal lifetime       v1.lifetime)
     (equal type           (vl-pretty-datatype v1.vartype))
     (equal atts           v1.atts)
     (test-vardecls-fn (cdr vars)
                       constp varp lifetime type atts
                       (cdr names)
                       (cdr dims)
                       (cdr initvals)))))

(defmacro test-parse-integer-declaration
  (&key input atts names dims initvals (successp 't))
  `(assert!
    (let ((tokens (make-test-tokens ,input))
          (warnings 'blah-warnings)
          (config   *vl-default-loadconfig*))
      (mv-let (erp val tokens warnings)
        (vl-parse-integer-declaration ',atts)
        (declare (ignore tokens))
        (if erp
            (prog2$ (cw "ERP is ~x0.~%" erp)
                    (and (not ,successp)
                         (equal warnings 'blah-warnings)))
          (prog2$ (cw "VAL is ~x0.~%" val)
                  (and ,successp
                       (equal warnings 'blah-warnings)
                       (test-vardecls-fn val
                                         nil ; constp
                                         nil ; varp
                                         nil ; lifetime
                                         '(:vl-integer signed)
                                         ',atts
                                         ',names
                                         ',dims
                                         ',initvals))))))))

(defmacro test-parse-real-declaration
  (&key input atts names dims initvals (successp 't))
  `(assert!
    (let ((tokens (make-test-tokens ,input))
          (warnings 'blah-warnings)
          (config   *vl-default-loadconfig*))
      (mv-let (erp val tokens warnings)
        (vl-parse-real-declaration ',atts)
        (declare (ignore tokens))
        (if erp
            (prog2$ (cw "ERP is ~x0.~%" erp)
                    (and (not ,successp)
                         (equal warnings 'blah-warnings)))
          (prog2$ (cw "VAL is ~x0.~%" val)
                  (and ,successp
                       (equal warnings 'blah-warnings)
                       (test-vardecls-fn val
                                         nil ; constp
                                         nil ; varp
                                         nil ; lifetime
                                         '(:vl-real unsigned)
                                         ',atts
                                         ',names
                                         ',dims
                                         ',initvals))))))))

(defmacro test-parse-time-declaration
  (&key input atts names dims initvals (successp 't))
  `(assert!
    (let ((tokens (make-test-tokens ,input))
          (warnings 'blah-warnings)
          (config   *vl-default-loadconfig*))
      (mv-let (erp val tokens warnings)
        (vl-parse-time-declaration ',atts)
        (declare (ignore tokens))
        (if erp
            (prog2$ (cw "ERP is ~x0.~%" erp)
                    (and (not ,successp)
                         (equal warnings 'blah-warnings)))
          (prog2$ (cw "VAL is ~x0.~%" val)
                  (and ,successp
                       (equal warnings 'blah-warnings)
                       (test-vardecls-fn val
                                         nil ; constp
                                         nil ; varp
                                         nil ; lifetime
                                         '(:vl-time unsigned)
                                         ',atts
                                         ',names
                                         ',dims
                                         ',initvals))))))))

(defmacro test-parse-realtime-declaration
  (&key input atts names dims initvals (successp 't))
  `(assert!
    (let ((tokens (make-test-tokens ,input))
          (warnings 'blah-warnings)
          (config   *vl-default-loadconfig*))
      (mv-let (erp val tokens warnings)
        (vl-parse-realtime-declaration ',atts)
        (declare (ignore tokens))
        (if erp
            (prog2$ (cw "ERP is ~x0.~%" erp)
                    (and (not ,successp)
                         (equal warnings 'blah-warnings)))
          (prog2$ (cw "VAL is ~x0.~%" val)
                  (and ,successp
                       (equal warnings 'blah-warnings)
                       (test-vardecls-fn val
                                         nil ; constp
                                         nil ; varp
                                         nil ; lifetime
                                         '(:vl-realtime unsigned)
                                         ',atts
                                         ',names
                                         ',dims
                                         ',initvals))))))))

(test-parse-integer-declaration :input "integer a, ; "
                                :successp nil)

(test-parse-integer-declaration :input "integer ; "
                                :successp nil)

(test-parse-integer-declaration :input "integer a = "
                                :successp nil)

(test-parse-integer-declaration :input "integer a = ; "
                                :successp nil)

(test-parse-integer-declaration :input "integer a ; "
                                :atts (("some") ("atts"))
                                :names ("a")
                                :dims (nil)
                                :initvals (nil))

(test-parse-integer-declaration :input "integer a, b, c; "
                                :atts (("some") ("atts"))
                                :names ("a" "b" "c")
                                :dims (nil nil nil)
                                :initvals (nil nil nil))

(test-parse-integer-declaration :input "integer a[1:2], b, c; "
                                :atts (("some") ("atts"))
                                :names ("a" "b" "c")
                                :dims (((range 1 2)) nil nil)
                                :initvals (nil nil nil))

(test-parse-integer-declaration :input "integer a[1:2][3:4], b, c; "
                                :atts (("some") ("atts"))
                                :names ("a" "b" "c")
                                :dims (((range 1 2) (range 3 4)) nil nil)
                                :initvals (nil nil nil))

(test-parse-integer-declaration :input "integer a[1:2][3:4], b = 5, c = 17 + 8; "
                                :atts (("some") ("atts"))
                                :names ("a" "b" "c")
                                :dims (((range 1 2) (range 3 4)) nil nil)
                                :initvals (nil 5 (:vl-binary-plus nil 17 8)))

;; Not allowed to have a range plus initial value.
(test-parse-integer-declaration :input "integer a[1:2] = 17 ; "
                                :successp nil)






(test-parse-real-declaration :input "real a, ; "
                             :successp nil)

(test-parse-real-declaration :input "real ; "
                             :successp nil)

(test-parse-real-declaration :input "real a = "
                             :successp nil)

(test-parse-real-declaration :input "real a = ; "
                             :successp nil)

(test-parse-real-declaration :input "real a ; "
                             :atts (("some") ("atts"))
                             :names ("a")
                             :dims (nil)
                             :initvals (nil))

(test-parse-real-declaration :input "real a, b, c; "
                             :atts (("some") ("atts"))
                             :names ("a" "b" "c")
                             :dims (nil nil nil)
                             :initvals (nil nil nil))

(test-parse-real-declaration :input "real a[1:2], b, c; "
                             :atts (("some") ("atts"))
                             :names ("a" "b" "c")
                             :dims (((range 1 2)) nil nil)
                             :initvals (nil nil nil))

(test-parse-real-declaration :input "real a[1:2][3:4], b, c; "
                             :atts (("some") ("atts"))
                             :names ("a" "b" "c")
                             :dims (((range 1 2) (range 3 4)) nil nil)
                             :initvals (nil nil nil))

(test-parse-real-declaration :input "real a[1:2][3:4], b = 5, c = 17 + 8; "
                             :atts (("some") ("atts"))
                             :names ("a" "b" "c")
                             :dims (((range 1 2) (range 3 4)) nil nil)
                             :initvals (nil 5 (:vl-binary-plus nil 17 8)))

;; Not allowed to have a range plus initial value.
(test-parse-real-declaration :input "real a[1:2] = 17 ; "
                             :successp nil)






(test-parse-time-declaration :input "time a, ; "
                             :successp nil)

(test-parse-time-declaration :input "time ; "
                             :successp nil)

(test-parse-time-declaration :input "time a = "
                             :successp nil)

(test-parse-time-declaration :input "time a = ; "
                             :successp nil)

(test-parse-time-declaration :input "time a ; "
                             :atts (("some") ("atts"))
                             :names ("a")
                             :dims (nil)
                             :initvals (nil))

(test-parse-time-declaration :input "time a, b, c; "
                             :atts (("some") ("atts"))
                             :names ("a" "b" "c")
                             :dims (nil nil nil)
                             :initvals (nil nil nil))

(test-parse-time-declaration :input "time a[1:2], b, c; "
                             :atts (("some") ("atts"))
                             :names ("a" "b" "c")
                             :dims (((range 1 2)) nil nil)
                             :initvals (nil nil nil))

(test-parse-time-declaration :input "time a[1:2][3:4], b, c; "
                             :atts (("some") ("atts"))
                             :names ("a" "b" "c")
                             :dims (((range 1 2) (range 3 4)) nil nil)
                             :initvals (nil nil nil))

(test-parse-time-declaration :input "time a[1:2][3:4], b = 5, c = 17 + 8; "
                             :atts (("some") ("atts"))
                             :names ("a" "b" "c")
                             :dims (((range 1 2) (range 3 4)) nil nil)
                             :initvals (nil 5 (:vl-binary-plus nil 17 8)))

;; Not allowed to have a range plus initial value.
(test-parse-time-declaration :input "time a[1:2] = 17 ; "
                             :successp nil)





(test-parse-realtime-declaration :input "realtime a, ; "
                                 :successp nil)

(test-parse-realtime-declaration :input "realtime ; "
                                 :successp nil)

(test-parse-realtime-declaration :input "realtime a = "
                                 :successp nil)

(test-parse-realtime-declaration :input "realtime a = ; "
                                 :successp nil)

(test-parse-realtime-declaration :input "realtime a ; "
                                 :atts (("some") ("atts"))
                                 :names ("a")
                                 :dims (nil)
                                 :initvals (nil))

(test-parse-realtime-declaration :input "realtime a, b, c; "
                                 :atts (("some") ("atts"))
                                 :names ("a" "b" "c")
                                 :dims (nil nil nil)
                                 :initvals (nil nil nil))

(test-parse-realtime-declaration :input "realtime a[1:2], b, c; "
                                 :atts (("some") ("atts"))
                                 :names ("a" "b" "c")
                                 :dims (((range 1 2)) nil nil)
                                 :initvals (nil nil nil))

(test-parse-realtime-declaration :input "realtime a[1:2][3:4], b, c; "
                                 :atts (("some") ("atts"))
                                 :names ("a" "b" "c")
                                 :dims (((range 1 2) (range 3 4)) nil nil)
                                 :initvals (nil nil nil))

(test-parse-realtime-declaration :input "realtime a[1:2][3:4], b = 5, c = 17 + 8; "
                                 :atts (("some") ("atts"))
                                 :names ("a" "b" "c")
                                 :dims (((range 1 2) (range 3 4)) nil nil)
                                 :initvals (nil 5 (:vl-binary-plus nil 17 8)))

;; Not allowed to have a range plus initial value.
(test-parse-realtime-declaration :input "realtime a[1:2] = 17 ; "
                                 :successp nil)


;; (defun test-regdecls-fn
;;   (regs atts signedp range names arrdims initvals)
;;   (if (atom regs)
;;       (and (atom names)
;;            (atom arrdims)
;;            (atom initvals))
;;     (debuggable-and
;;      (consp names)
;;      (consp arrdims)
;;      (consp initvals)
;;      (not (cw "Inspecting ~x0.~%" (car regs)))
;;      (vl-vardecl-p (car regs))
;;      (equal (vl-vardecl->type (car regs)) :vl-reg)
;;      (equal atts          (vl-vardecl->atts (car regs)))
;;      (equal signedp       (vl-vardecl->signedp (car regs)))
;;      (equal range         (vl-pretty-maybe-range (vl-vardecl->range (car regs))))
;;      (equal (car names)   (vl-vardecl->name (car regs)))
;;      (equal (car arrdims) (vl-pretty-range-list (vl-vardecl->arrdims (car regs))))
;;      (if (car initvals)
;;          (debuggable-and (vl-vardecl->initval (car regs))
;;                          (equal (car initvals)
;;                                 (vl-pretty-expr (vl-vardecl->initval (car regs)))))
;;        (not (vl-vardecl->initval (car regs))))
;;      (test-regdecls-fn (cdr regs) atts signedp range
;;                        (cdr names) (cdr arrdims) (cdr initvals)))))

(defmacro test-parse-reg-declaration
  (&key input atts type names dims initvals (successp 't))
  `(assert!
    (let ((tokens (make-test-tokens ,input))
          (warnings 'blah-warnings)
          (config   *vl-default-loadconfig*))
      (mv-let (erp val tokens warnings)
        (vl-parse-reg-declaration ',atts)
        (declare (ignore tokens))
        (if erp
            (prog2$ (cw "ERP is ~x0.~%" erp)
                    (and (not ,successp)
                         (equal warnings 'blah-warnings)))
          (prog2$ (cw "VAL is ~x0.~%" val)
                  (and ,successp
                       (equal warnings 'blah-warnings)
                       (test-vardecls-fn val
                                         nil ; constp
                                         nil ; varp
                                         nil ; lifetime
                                         ',type
                                         ',atts
                                         ',names
                                         ',dims
                                         ',initvals))))))))

(test-parse-reg-declaration :input "reg a, ; "
                            :successp nil)

(test-parse-reg-declaration :input "reg ; "
                            :successp nil)

(test-parse-reg-declaration :input "reg a = "
                            :successp nil)

(test-parse-reg-declaration :input "reg a = ; "
                            :successp nil)

(test-parse-reg-declaration :input "reg a ; "
                            :atts (("some") ("atts"))
                            :type (:vl-reg unsigned)
                            :names ("a")
                            :dims (nil)
                            :initvals (nil))

(test-parse-reg-declaration :input "reg signed a ; "
                            :atts (("some") ("atts"))
                            :type (:vl-reg signed)
                            :names ("a")
                            :dims (nil)
                            :initvals (nil))

(test-parse-reg-declaration :input "reg [1:3] a ; "
                            :atts (("some") ("atts"))
                            :type (:vl-reg unsigned (range 1 3))
                            :names ("a")
                            :dims (nil)
                            :initvals (nil))

(test-parse-reg-declaration :input "reg signed [1:3] a ; "
                            :atts (("some") ("atts"))
                            :type (:vl-reg signed (range 1 3))
                            :names ("a")
                            :dims (nil)
                            :initvals (nil))

(test-parse-reg-declaration :input "reg signed [1:3] a, b, c; "
                            :atts (("some") ("atts"))
                            :type (:vl-reg signed (range 1 3))
                            :names ("a" "b" "c")
                            :dims (nil nil nil)
                            :initvals (nil nil nil))

(test-parse-reg-declaration :input "reg a[1:2], b, c; "
                            :atts (("some") ("atts"))
                            :names ("a" "b" "c")
                            :type (:vl-reg unsigned)
                            :dims (((range 1 2)) nil nil)
                            :initvals (nil nil nil))

(test-parse-reg-declaration :input "reg signed a[1:2][3:4], b, c; "
                            :atts (("some") ("atts"))
                            :names ("a" "b" "c")
                            :type (:vl-reg signed)
                            :dims (((range 1 2) (range 3 4)) nil nil)
                            :initvals (nil nil nil))

(test-parse-reg-declaration :input "reg [7:0] a[1:2][3:4], b = 5, c = 17 + 8; "
                            :atts (("some") ("atts"))
                            :names ("a" "b" "c")
                            :type (:vl-reg unsigned (range 7 0))
                            :dims (((range 1 2) (range 3 4)) nil nil)
                            :initvals (nil 5 (:vl-binary-plus nil 17 8)))

;; Not allowed to have a range plus initial value.
(test-parse-reg-declaration :input "reg a[1:2] = 17 ; "
                            :successp nil)




(defun test-eventdecls-fn (events atts names arrdims)
  (if (atom events)
      (and (atom names)
           (atom arrdims))
    (debuggable-and
     (consp names)
     (consp arrdims)
     (not (cw "Inspecting ~x0.~%" (car events)))
     (vl-eventdecl-p (car events))
     (equal atts          (vl-eventdecl->atts (car events)))
     (equal (car names)   (vl-eventdecl->name (car events)))
     (equal (car arrdims) (vl-pretty-range-list (vl-eventdecl->arrdims (car events))))
     (test-eventdecls-fn (cdr events) atts (cdr names) (cdr arrdims)))))

(defmacro test-parse-event-declaration
  (&key input atts names arrdims (successp 't))
  `(assert!
    (let ((tokens (make-test-tokens ,input))
          (warnings 'blah-warnings)
          (config   *vl-default-loadconfig*))
      (mv-let (erp val tokens warnings)
        (vl-parse-event-declaration ',atts)
        (declare (ignore tokens))
        (if erp
            (prog2$ (cw "ERP is ~x0.~%" erp)
                    (and (equal warnings 'blah-warnings)
                         (not ,successp)))
          (prog2$ (cw "VAL is ~x0.~%" val)
                  (and ,successp
                       (equal warnings 'blah-warnings)
                       (test-eventdecls-fn val ',atts ',names ',arrdims))))))))


(test-parse-event-declaration :input "event a, ; "
                              :successp nil)

(test-parse-event-declaration :input "event ; "
                              :successp nil)

(test-parse-event-declaration :input "event a = "
                              :successp nil)

(test-parse-event-declaration :input "event a = 1;"
                              :successp nil)

(test-parse-event-declaration :input "event a ; "
                              :atts (("some") ("atts"))
                              :names ("a")
                              :arrdims (nil))

(test-parse-event-declaration :input "event a, b, c ; "
                              :atts (("some") ("atts"))
                              :names ("a" "b" "c")
                              :arrdims (nil nil nil))

(test-parse-event-declaration :input "event a[3:4][5:6], b[1:2], c ; "
                              :atts (("some") ("atts"))
                              :names ("a" "b" "c")
                              :arrdims (((range 3 4) (range 5 6))
                                        ((range 1 2))
                                        nil))





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

