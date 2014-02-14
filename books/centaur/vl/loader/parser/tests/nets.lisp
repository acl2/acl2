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
(include-book "../nets")
(program)

(defun test-assign-aux (assigns lvalues exprs str rise fall high atts)
  (if (atom assigns)
      (debuggable-and (atom lvalues)
                      (atom exprs))
    (debuggable-and
     (consp lvalues)
     (consp exprs)
     (not (cw "Inspecting ~x0.~%" (car assigns)))
     (not (cw "Lvalue: ~x0.~%" (car lvalues)))
     (not (cw "Expr: ~x0.~%" (car exprs)))
     (vl-assign-p (car assigns))
     (equal (car lvalues) (vl-pretty-expr (vl-assign->lvalue (car assigns))))
     (equal (car exprs) (vl-pretty-expr (vl-assign->expr (car assigns))))
     (equal str (vl-assign->strength (car assigns)))
     (equal atts (vl-assign->atts (car assigns)))
     (equal rise (and (vl-assign->delay (car assigns))
                      (vl-pretty-expr
                       (vl-gatedelay->rise (vl-assign->delay (car assigns))))))
     (equal fall (and (vl-assign->delay (car assigns))
                      (vl-pretty-expr
                       (vl-gatedelay->fall (vl-assign->delay (car assigns))))))
     (equal high (and (vl-assign->delay (car assigns))
                      (vl-gatedelay->high (vl-assign->delay (car assigns)))
                      (vl-pretty-expr
                       (vl-gatedelay->high (vl-assign->delay (car assigns))))))
     (test-assign-aux (cdr assigns) (cdr lvalues) (cdr exprs)
                      str rise fall high atts))))

(defmacro test-assign
  (&key input lvalues exprs str rise fall high atts (successp 't))
  `(assert!
    (let ((tokens (make-test-tokens ,input))
          (warnings 'blah-warnings)
          (config   *vl-default-loadconfig*))
      (mv-let (erp val tokens warnings)
        (vl-parse-continuous-assign ',atts)
        (declare (ignorable tokens warnings))
        (if erp
            (prog2$ (cw "ERP: ~x0.~%" erp)
                    (not ,successp))
          (debuggable-and
           ,successp
           (test-assign-aux val ',lvalues ',exprs ,str
                            ',rise ',fall ',high ',atts)))))))

(test-assign :input "assign w = 1 ; "
             :lvalues ((id "w"))
             :exprs   (1)
             :atts (("some") ("atts"))
             :str nil
             :rise nil
             :fall nil
             :high nil)

(test-assign :input "assign w = 1, v = 2 ; "
             :lvalues ((id "w") (id "v"))
             :exprs   (1        2)
             :atts (("some") ("atts"))
             :str nil
             :rise nil
             :fall nil
             :high nil)

(test-assign :input "assign {x, y, z} = 1, v = 2 ; "
             :lvalues ((:vl-concat nil (id "x") (id "y") (id "z"))
                       (id "v"))
             :exprs   (1 2)
             :atts (("some") ("atts"))
             :str nil
             :rise nil
             :fall nil
             :high nil)

(test-assign :input "assign #36 a[0] = 1 ; "
             :lvalues ((:vl-index nil (id "a") 0))
             :exprs   (1)
             :atts (("some") ("atts"))
             :str nil
             :rise 36
             :fall 36
             :high 36)

(test-assign :input "assign (small) #36 a[0] = 1 ; "
             :successp nil)

(test-assign :input "assign (strong0, pull1) #36 a[7:0] = 1 ; "
             :lvalues ((:vl-partselect-colon nil (id "a") 7 0))
             :exprs   (1)
             :atts (("some") ("atts"))
             :str (make-vl-gatestrength :zero :vl-strong
                                        :one :vl-pull)
             :rise 36
             :fall 36
             :high 36)

(test-assign :input "assign #36 (strong0, pull1) a[7:0] = 1 ; "
             :successp nil)

(test-assign :input "assign #(5,10,1:2:3) w = 1, v = 2, a = w & v ; "
             :lvalues ((id "w") (id "v") (id "a"))
             :exprs   (1        2        (:vl-binary-bitand nil (id "w") (id "v")))
             :atts (("some") ("atts"))
             :str nil
             :rise 5
             :fall 10
             :high (:vl-mintypmax nil 1 2 3))




(defun test-decls-aux (decls ids type range arrdims vectoredp scalaredp signedp rise
                             fall high cstrength)
  (if (atom decls)
      (debuggable-and (not arrdims)
                      (not ids))
    (debuggable-and
     (consp arrdims)
     (consp ids)
     (not (cw "Inspecting Decl: ~x0.~%" (car decls)))
     (vl-netdecl-p (car decls))
     (equal (car ids) (vl-netdecl->name (car decls)))
     (equal type (vl-netdecl->type (car decls)))
     (equal range (vl-pretty-maybe-range (vl-netdecl->range (car decls))))
     (equal (car arrdims) (vl-pretty-range-list (vl-netdecl->arrdims (car decls))))
     (equal vectoredp (vl-netdecl->vectoredp (car decls)))
     (equal scalaredp (vl-netdecl->scalaredp (car decls)))
     (equal signedp (vl-netdecl->signedp (car decls)))
     (equal rise (and (vl-netdecl->delay (car decls))
                      (vl-pretty-expr (vl-gatedelay->rise (vl-netdecl->delay (car decls))))))
     (equal fall (and (vl-netdecl->delay (car decls))
                      (vl-pretty-expr (vl-gatedelay->fall (vl-netdecl->delay (car decls))))))
     (equal high (and (vl-netdecl->delay (car decls))
                      (vl-gatedelay->high (vl-netdecl->delay (car decls)))
                      (vl-pretty-expr (vl-gatedelay->high (vl-netdecl->delay (car decls))))))
     (equal cstrength (vl-netdecl->cstrength (car decls)))
     (test-decls-aux (cdr decls) (cdr ids)  type range (cdr arrdims) vectoredp scalaredp
                     signedp rise fall high cstrength))))

(defmacro test-netdecl (&key input atts
                             ;; stuff for assignments
                             lvalues exprs str assign-rise assign-fall assign-high
                             ;; stuff for decl parts
                             ids type range arrdims vectoredp scalaredp signedp decl-rise decl-fall decl-high cstrength
                             (successp 't))
  `(assert!
    (let ((tokens (make-test-tokens ,input)))
      (mv-let (erp val tokens warnings)
        (vl-parse-net-declaration ',atts
                                  :tokens tokens
                                  :warnings nil
                                  :config *vl-default-loadconfig*)
        (declare (ignorable tokens warnings))
        (if erp
            (prog2$ (cw "ERP: ~x0.~%" erp)
                    (not ,successp))
          (debuggable-and
           ,successp
           (implies (not (car val))
                    (debuggable-and (not ',lvalues)
                                    (not ',exprs)))
           (test-assign-aux (car val) ',lvalues ',exprs ,str ',assign-rise ',assign-fall ',assign-high ',atts)
           (test-decls-aux (cdr val) ',ids ',type ',range ',arrdims ',vectoredp
                           ',scalaredp ',signedp ',decl-rise ',decl-fall ',decl-high
                           ',cstrength)))))))

(test-netdecl :input "wire w ; "
              :ids ("w")
              :lvalues nil
              :exprs nil
              :str nil
              :assign-rise nil
              :assign-fall nil
              :assign-high nil
              :decl-rise nil
              :decl-fall nil
              :decl-high nil
              :type :vl-wire
              :atts (("some") ("atts"))
              :arrdims (nil)
              :range (no-range)
              :vectoredp nil
              :scalaredp nil
              :signedp nil
              :cstrength nil)

(test-netdecl :input "triand signed w1, w2 ; "
              :ids ("w1" "w2")
              :lvalues nil
              :exprs nil
              :str nil
              :assign-rise nil
              :assign-fall nil
              :assign-high nil
              :decl-rise nil
              :decl-fall nil
              :decl-high nil
              :type :vl-triand
              :atts (("some") ("atts"))
              :arrdims (nil nil)
              :range (no-range)
              :vectoredp nil
              :scalaredp nil
              :signedp t
              :cstrength nil)

(test-netdecl :input "wor scalared [4:0] #(3, 4, 5) w1, w2 ; "
              :ids ("w1" "w2")
              :lvalues nil
              :exprs nil
              :str nil
              ;; This delay is for the decls, since there are no assigns.
              :assign-rise nil
              :assign-fall nil
              :assign-high nil
              :decl-rise 3
              :decl-fall 4
              :decl-high 5
              :type :vl-wor
              :atts (("some") ("atts"))
              :arrdims (nil nil)
              :range (range 4 0)
              :vectoredp nil
              :scalaredp t
              :signedp nil
              :cstrength nil)

(test-netdecl :input "uwire vectored signed [4:0] #3 w1 [3:0][4:1][5:2], w2 ; "
              :ids ("w1" "w2")
              :lvalues nil
              :exprs nil
              :str nil
              ;; This delay is for the decls, since there are no assigns.
              :assign-rise nil
              :assign-fall nil
              :assign-high nil
              :decl-rise 3
              :decl-fall 3
              :decl-high 3
              :type :vl-uwire
              :atts (("some") ("atts"))
              :arrdims (((range 3 0) (range 4 1) (range 5 2)) nil)
              :range (range 4 0)
              :vectoredp t
              :scalaredp nil
              :signedp t
              :cstrength nil)

;; Need a semicolon
(test-netdecl :input "wire w1 "
              :successp nil)

;; Not allowed to use vectored without a range.
(test-netdecl :input "wire vectored signed w1 [3:0][4:1][5:2], w2 ; "
              :successp nil)

;; Not allowed to use scalared without a range
(test-netdecl :input "wire scalared w1; "
              :successp nil)

;; Not allowed to have a charge strength on a non-trireg
(test-netdecl :input "wire (small) w ; "
              :successp nil)

;; Not allowed to have a strength without assignments
(test-netdecl :input "wire (supply0, pull1) w1; "
              :successp nil)

(test-netdecl :input "trireg (small) w ; "
              :ids ("w")
              :lvalues nil
              :exprs nil
              :str nil
              :decl-rise nil
              :decl-fall nil
              :decl-high nil
              :assign-rise nil
              :assign-fall nil
              :assign-high nil
              :type :vl-trireg
              :atts (("some") ("atts"))
              :arrdims (nil)
              :range (no-range)
              :vectoredp nil
              :scalaredp nil
              :signedp nil
              :cstrength :vl-small)

(test-netdecl :input "wire w = 1 ; "
              :ids ("w")
              :lvalues ((id "w"))
              :exprs   (1)
              :str nil
              :decl-rise nil
              :decl-fall nil
              :decl-high nil
              :assign-rise nil
              :assign-fall nil
              :assign-high nil
              :type :vl-wire
              :atts (("some") ("atts"))
              :arrdims (nil)
              :range (no-range)
              :vectoredp nil
              :scalaredp nil
              :signedp nil
              :cstrength nil)

;; no arrays with assignments
(test-netdecl :input "wire w [1] = 1 ; "
              :successp nil)

;; no mixing assignments and plain decls
(test-netdecl :input "wire w, a = 1 ; "
              :successp nil)

(test-netdecl :input "wire (supply1,strong0) vectored signed [4:0] #(3) w1 = 1, w2 = 2 ; "
              :ids ("w1" "w2")
              :lvalues ((id "w1") (id "w2"))
              :exprs   (1 2)
              :str (make-vl-gatestrength :zero :vl-strong
                                         :one :vl-supply)
              ;; The delay is for the assignments, since there are assignments.
              :assign-rise 3
              :assign-fall 3
              :assign-high 3
              :decl-rise nil
              :decl-fall nil
              :decl-high nil
              :type :vl-wire
              :atts (("some") ("atts"))
              :arrdims (nil nil)
              :range (range 4 0)
              :vectoredp t
              :scalaredp nil
              :signedp t
              :cstrength nil)

