; VL Verilog Toolkit - Clocking Block Parsing
; Copyright (C) 2016 Apple, Inc.
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
; Original author: Jared Davis

(in-package "VL")
(include-book "base")
(include-book "../clocking")

(defparser-top vl-parse-normal-clocking-declaration
  :guard (vl-atts-p atts))

(defparser-top vl-parse-global-clocking-declaration
  :guard (vl-atts-p atts))

(define vl-pretty-clkskew ((x vl-clkskew-p))
  (b* (((vl-clkskew x)))
    (append (if x.delay
                (list (vl-pretty-expr x.delay))
              nil)
            (if (not (eq x.edge :vl-noedge))
                (list x.edge)
              nil))))

(define vl-pretty-clkassign ((x vl-clkassign-p))
  (b* (((vl-clkassign x)))
    (append (if x.inputp '(:input) '(:output))
           (and x.skew (vl-pretty-clkskew x.skew))
           (list x.name)
           (if x.rhs (list := (vl-pretty-expr x.rhs)) nil))))

(define vl-pretty-clkassignlist ((x vl-clkassignlist-p))
  (if (atom x)
      nil
    (cons (vl-pretty-clkassign (car x))
          (vl-pretty-clkassignlist (cdr x)))))

(define vl-pretty-clkdecl ((x vl-clkdecl-p))
  :guard-debug t
  (b* (((vl-clkdecl x)))
    (append (list :clocking)
            (if x.defaultp (list :default) nil)
            (if x.name (list x.name) nil)
            (cons :event (vl-pretty-evatomlist x.event))
            (cons :assigns (vl-pretty-clkassignlist x.clkassigns))
            (if (consp x.properties)
                (list :propeties (len x.properties))
              nil)
            (if (consp x.sequences)
                (list :sequences (len x.sequences))
              nil))))


