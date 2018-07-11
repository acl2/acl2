; VL Verilog Toolkit - Timeunits Parsing
; Copyright (C) 2017 Apple, Inc.
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

(in-package "VL")
(include-book "utils")
(include-book "../../parsetree")

(defsection parse-timeunits
  :parents (parser)
  :short "Functions for parsing SystemVerilog @('timeunit') and
  @('timeprecision') declarations."

  :long "<p>The optional @('timeunits_declaration') comes after the module
  header.  It is defined in a gross way to allow either a timeunit,
  timeprecision, or both in either order:</p>

  @({
      timeunits_declaration ::=
       'timeunit' time_literal [ '/' time_literal ] ';'
     | 'timeprecision' time_literal ';'
     | 'timeunit' time_literal [ '/' time_literal ] ';' 'timeprecision' time_literal ';'
     | 'timeprecision' time_literal ';' 'timeunit' time_literal [ '/' time_literal ] ';'
  })")

(local (xdoc::set-default-parents parse-timeunits))

(defparser vl-parse-timeliteral ()
  :short "Match a @('time_literal')."
  :long "<p>A time_literal is handled by the lexer as a @(see vl-timetoken) and
         contains a quantity just as a string and a @(see vl-timeunit-p), which
         is just what we need for our @(see vl-timeliteral) structures.</p>"
  :result (vl-timeliteral-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (lit := (vl-match-token :vl-timetoken))
       (return (make-vl-timeliteral :quantity (vl-timetoken->quantity lit)
                                    :units (vl-timetoken->units lit)))))

(defparser vl-parse-timeunitdecl ()
  :short "Matches @(' 'timeunit' time_literal [ '/' time_literal ] ';' ')."
  :result (vl-timeunitdecl-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (kwd := (vl-match-token :vl-kwd-timeunit))
       (numerator := (vl-parse-timeliteral))
       (when (vl-is-token? :vl-div)
         (:= (vl-match))
         (denominator := (vl-parse-timeliteral)))
       (:= (vl-match-token :vl-semi))
       (return (make-vl-timeunitdecl :loc (vl-token->loc kwd)
                                     :numerator numerator
                                     :denominator denominator))))

(defparser vl-parse-timeprecisiondecl ()
  :short "Matches @(' 'timeprecision' time_literal ';' ')."
  :result (vl-timeprecisiondecl-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (kwd := (vl-match-token :vl-kwd-timeprecision))
       (precision := (vl-parse-timeliteral))
       (:= (vl-match-token :vl-semi))
       (return (make-vl-timeprecisiondecl :loc (vl-token->loc kwd)
                                          :precision precision))))

(defparser vl-parse-optional-timeunits-declaration ()
  :short "Matches @('[timeunits_declaration]')."
  :result (and (consp val)
               (vl-maybe-timeunitdecl-p (car val))
               (vl-maybe-timeprecisiondecl-p (cdr val)))
  :fails gracefully
  :count weak
  (seq tokstream
       (when (vl-is-token? :vl-kwd-timeunit)
         (unit1 := (vl-parse-timeunitdecl)))
       (when (vl-is-token? :vl-kwd-timeprecision)
         (prec := (vl-parse-timeprecisiondecl)))
       (when (and (not unit1)
                  (vl-is-token? :vl-kwd-timeunit))
         (unit2 := (vl-parse-timeunitdecl)))
       (return (cons (or unit1 unit2) prec))))

