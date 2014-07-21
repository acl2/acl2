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
(include-book "axioms")
(%interactive)

(%defderiv build.reflexivity)
(%defderiv build.equality :omit-okp t)

(%deftheorem theorem-commutativity-of-pequal)
(%defderiv build.commute-pequal)
(%defderiv build.disjoined-commute-pequal)
(%defderiv build.commute-not-pequal)
(%defderiv build.disjoined-commute-not-pequal)

(%deftheorem theorem-substitute-into-not-pequal)
(%defderiv build.substitute-into-not-pequal)
(%defderiv build.disjoined-substitute-into-not-pequal-lemma-1 :omit-okp t)
(%defderiv build.disjoined-substitute-into-not-pequal)

(%deftheorem theorem-transitivity-of-pequal)
(%defderiv build.transitivity-of-pequal)
(%defderiv build.disjoined-transitivity-of-pequal-lemma-1 :omit-okp t)
(%defderiv build.disjoined-transitivity-of-pequal)

(%deftheorem theorem-not-t-or-not-nil)
(%defderiv build.not-nil-from-t)
(%defderiv build.disjoined-not-nil-from-t)
(%defderiv build.not-t-from-nil)
(%defderiv build.disjoined-not-t-from-nil)

