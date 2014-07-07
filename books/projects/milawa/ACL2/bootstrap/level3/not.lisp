; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "hacks")
(include-book "iff")
(%interactive)

;(local (%disable default LOGIC.FUNCTION-OF-CONS-WITH-DEFECTIVELY-MERGED-CONSTANT))

(%autoadmit definition-of-not)

(%deftheorem theorem-not-when-nil)
;; (%defderiv build.negative-lit-from-pequal-nil)  ;; Not used anywhere.
(%defderiv build.disjoined-negative-lit-from-pequal-nil)


(%deftheorem theorem-not-when-not-nil)
;; (%defderiv build.pequal-nil-from-negative-lit)  ;; Not used anywhere.
(%defderiv build.negative-lit-from-not-pequal-nil :omit-okp t) ;; Only used in %use hints.
(%defderiv build.disjoined-pequal-nil-from-negative-lit)

(%deftheorem theorem-not-of-not)
(%deftheorem theorem-not-of-not-under-iff)
(%deftheorem theorem-iff-when-not-nil)

;; (%defderiv build.iff-when-not-nil) ;; Not used anywhere.

(encapsulate
 ()
 (local (%enable default bust-up-cdr-of-logic.function-args-expensive))
 (%defderiv build.disjoined-iff-when-not-nil))
