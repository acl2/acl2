; ACL2 Sidekick
; Copyright (C) 2014 Kookamara LLC
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

(in-package "ACL2")
(include-book "std/portcullis" :dir :system)
(include-book "centaur/bridge/portcullis" :dir :system)
(include-book "centaur/vl/portcullis" :dir :system)

(defpkg "SIDEKICK"
  (union-eq-exec
   (union-eq-exec '(include-raw
                    std::def-primitive-aggregate
                    std::defval ;; bozo not in std-exports?
                    bridge::json-encode
                    ;; for integrating documentation
                    sidekick

                    str::cat
                    str::nat-to-dec-string

                    ;; acl2 stuff we want access to
                    ens
                    er-decode-cd
                    access-command-tuple-number
                    make-ldds-command-sequence
                    er-let*
                    access
                    ldd-status

                    ;; other handy functions
                    maybe-natp
                    maybe-stringp

                    ;; interactive sidekick commands
                    home
                    show
                    session
                    lint
                    )
                  std::*std-exports*)
   *std-pkg-symbols*))
