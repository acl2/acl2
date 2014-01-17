; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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
(include-book "lexer/tokens")
(include-book "../mlib/fmt")

(defsection vl-report-parse-error

; This is a truly horrific use of memoization to avoid printing the same errors
; multiple times.
;
; We put this in its own file so that the rest of the parser doesn't have to
; depend on the writer.


  (defund vl-actually-report-parse-error (err context)
    (declare (xargs :guard (stringp context)))
    (if (not err)
        nil
      (vl-cw-ps-seq
       (vl-ps-update-autowrap-col 68)
       (if (and (consp err)
                (stringp (car err)))
           (vl-cw-obj (car err) (cdr err))
         (vl-cw "Malformed error object: ~x0." err))
       (vl-println context)
       (vl-println ""))))

  (memoize 'vl-actually-report-parse-error)

  (defund vl-report-parse-error (err tokens)
    (declare (xargs :guard (vl-tokenlist-p tokens)))
    (if (not err)
        nil
      (let ((context (cat "  Near: \""
                          (vl-tokenlist->string-with-spaces
                           (take (min 4 (len tokens))
                                 (redundant-list-fix tokens)))
                          (if (> (len tokens) 4) "..." "")
                          "\"")))
        (vl-actually-report-parse-error
         ;; Have to hons the arguments for the memoization to work correctly.
         ;; Fortunately they're usually very small.
         (hons-copy err)
         (hons-copy context))))))