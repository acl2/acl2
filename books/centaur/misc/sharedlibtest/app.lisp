; Shared Library Relocation Test
; Copyright (C) 2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "oslib/ls" :dir :system)
(include-book "oslib/file-types" :dir :system)
(include-book "../sharedlibs")
(set-state-ok t)

(define file-kinds ((paths string-listp)
                    &key
                    ((follow-symlinks booleanp) 't)
                    (state 'state))
  :returns (mv (errmsg "NIL on success, or an error @(see msg) on failure.")
               (ans    true-listp)
               (state  state-p1 :hyp (state-p1 state)))
  (b* (((when (atom paths))
        (mv nil nil state))

       ((mv errmsg1 kind1 state)
        (oslib::file-kind (car paths) :follow-symlinks follow-symlinks))
       ((when errmsg1)
        (mv errmsg1 nil state))

       ((mv errmsg2 kinds2 state)
        (file-kinds (cdr paths) :follow-symlinks follow-symlinks))
       ((when errmsg2)
        (mv errmsg2 nil state)))
    (mv nil (cons kind1 kinds2) state)))

(defund my-app (state)
  (b* (((mv errmsg paths state) (oslib::ls-files "."))

       ((when errmsg)
        (cw "Listing files failed: ~@0~%" errmsg)
        (exit 1)
        state)

       ((mv errmsg kinds state) (file-kinds paths))
       ((when errmsg)
        (cw "File kind failed: ~@0.~%" errmsg)
        (exit 1)
        state))

    (cw "~x0~%" (pairlis$ paths kinds))
    (exit 0)
    state))

