; Lemmas about intern-in-package-of-symbol
; Copyright (C) 2005-2006 Kookamara LLC
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
;
; intern-in-package-of-symbol.lisp
; This file was originally part of the Unicode library.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(defsection std/basic/intern-in-package-of-symbol
  :parents (std/basic intern-in-package-of-symbol)
  :short "Lemmas about @(see intern-in-package-of-symbol) available in the
  @(see std/basic) library."

  (local (defthm intern-in-package-of-symbol-lemma
           (implies (and (stringp a)
                         (stringp b)
                         (symbolp in-pkg)
                         (not (equal a b)))
                    (not (equal (intern-in-package-of-symbol a in-pkg)
                                (intern-in-package-of-symbol b in-pkg))))
           :hints(("Goal"
                   :use ((:instance symbol-name-intern-in-package-of-symbol
                          (s a) (any-symbol in-pkg))
                         (:instance symbol-name-intern-in-package-of-symbol
                          (s b) (any-symbol in-pkg)))))))

  (defthm equal-of-intern-in-package-of-symbols
    (implies (and (stringp a)
                  (stringp b)
                  (symbolp in-pkg))
             (equal (equal (intern-in-package-of-symbol a in-pkg)
                           (intern-in-package-of-symbol b in-pkg))
                    (equal a b)))))
