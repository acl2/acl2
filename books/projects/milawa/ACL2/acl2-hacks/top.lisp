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

(include-book "assume")
(include-book "car-cdr-untranslate")
;(include-book "compact-write-file")
(include-book "debug-guards")
;(include-book "defthm")
(include-book "defthms-flag")
(include-book "defun")
(include-book "force")
(include-book "info")
(include-book "io")
(include-book "ls")
(include-book "mksym")
(include-book "no-fertilize")
;; Do not include redef-okp until it's needed; it's unsound
(include-book "redef-notinline")
(include-book "str")
;; (include-book "widescreen")

(defmacro defsection (name &rest args)
  ;; This is just a "named encapsulate nil."  It doesn't really do anything
  ;; except group some commands into a local scope.  But it prints a lot better
  ;; with :pbt than hundreds of encapsulate nils.
  (declare (ignore name))
  `(encapsulate () ,@args))

