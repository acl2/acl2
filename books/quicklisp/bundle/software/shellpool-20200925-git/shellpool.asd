; Shellpool - Interface from Common Lisp to External Programs
; Copyright (C) 2014-2015 Kookamara LLC
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

;; BOZO this seems to cause problems for allegro?
;; Ah, pjb says that the .asd file shouldn't have an in-package form.
;; (in-package :asdf-user)

#-(or ccl sbcl cmucl allegro abcl lispworks)
(error "~%~%Error: Shellpool has not yet been ported to this Lisp; patches welcome.~%~%")

#+(and sbcl (not sb-thread))
(error "~%~%Error: Shellpool requires an SBCL compiled with --with-sb-thread.~%~%")

(defsystem "shellpool"
  :description "A library for running external programs from Common Lisp. (https://github.org/jaredcdavis/shellpool)"
  :version "0.0.3"
  :author "Jared Davis <jared@kookamara.com>, Kookamara LLC"
  :license "An MIT/X11-style license; see the file LICENSE."
  :depends-on (:trivial-features
               :cl-fad
               :bordeaux-threads
               :bt-semaphore
               )
  :components ((:file "src/packages")
               (:file "src/main"))
  :serial t)

