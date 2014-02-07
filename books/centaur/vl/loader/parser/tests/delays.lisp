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
(include-book "../delays")

(defmacro test-delay3 (&key input rise fall high (successp 't))
  `(assert!
    (let ((tokens (make-test-tokens ,input))
          (warnings 'blah-warnings)
          (config   *vl-default-loadconfig*))
      (mv-let (erp val tokens warnings)
        (vl-parse-delay3)
        (declare (ignore tokens))
        (if erp
            (prog2$ (cw "ERP is ~x0.~%" erp)
                    (and (equal warnings 'blah-warnings)
                         (not ,successp)))
          (prog2$ (cw "VAL is ~x0.~%" val)
                  (and ,successp
                       (equal warnings 'blah-warnings)
                       (vl-gatedelay-p val)
                       (prog2$ (cw "Rise = ~x0.~%" (vl-pretty-expr (vl-gatedelay->rise val)))
                               (equal (vl-pretty-expr (vl-gatedelay->rise val)) ',rise))
                       (prog2$ (cw "Fall = ~x0.~%" (vl-pretty-expr (vl-gatedelay->fall val)))
                               (equal (vl-pretty-expr (vl-gatedelay->fall val)) ',fall))
                       (prog2$ (cw "High = ~x0.~%"
                                   (and (vl-gatedelay->high val)
                                        (vl-pretty-expr (vl-gatedelay->high val))))
                               (if (vl-gatedelay->high val)
                                   (equal (vl-pretty-expr (vl-gatedelay->high val)) ',high)
                                 (not ',high))))))))))

(test-delay3 :input "#5"
             :rise 5
             :fall 5
             :high 5)

(test-delay3 :input "#2 0"
             :rise 2
             :fall 2
             :high 2)

(test-delay3 :input "#3.4"
             :rise (real "3.4")
             :fall (real "3.4")
             :high (real "3.4"))

(test-delay3 :input "#foo"
             :rise (id "foo")
             :fall (id "foo")
             :high (id "foo"))

(test-delay3 :input "#'sd15"
             :successp nil)

(test-delay3 :input "#('sd15)"
             :rise 15
             :fall 15
             :high 15)

(test-delay3 :input "#(5, foo)"
             :rise 5
             :fall (id "foo")
             :high nil)

(test-delay3 :input "#(5, 20, 55)"
             :rise 5
             :fall 20
             :high 55)

(test-delay3 :input "#(1:2:3, 4:5:6, 7:8:9)"
             :rise (:vl-mintypmax nil 1 2 3)
             :fall (:vl-mintypmax nil 4 5 6)
             :high (:vl-mintypmax nil 7 8 9))

(test-delay3 :input "#(1:2:3, 4:5:6)"
             :rise (:vl-mintypmax nil 1 2 3)
             :fall (:vl-mintypmax nil 4 5 6)
             :high nil)
