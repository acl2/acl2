; OSLIB -- Operating System Utilities
; Copyright (C) 2013-2014 Centaur Technology
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

(in-package "OSLIB")
(include-book "../ls")
(include-book "../mkdir")
(include-book "../rmtree")
(include-book "std/util/defconsts" :dir :system)
(include-book "std/osets/top" :dir :system)

(local (defthm true-listp-when-string-listp
         (implies (string-listp x)
                  (true-listp x))))

#||
(acl2::with-redef
  (defun mkdir-fn (dir state)
    (declare (ignorable dir)
             (xargs :stobjs state))
    (mv t state)))
||#

(define basic-mkdir-test ((new-dir-name stringp) &key (state 'state))
  :returns (state state-p1 :hyp (state-p1 state))
  (b* (((mv okp state) (rmtree new-dir-name))
       ((unless okp)
        (raise "Error removing directory ~x0." new-dir-name)
        state)
       ((mv errp orig-dirs state) (ls-subdirs "."))
       ((when errp)
        (raise "Error listing new subdirectories.")
        state)
       ((mv okp state) (mkdir new-dir-name))
       ((unless okp)
        (raise "Error making directory ~x0." new-dir-name)
        state)
       ((mv errp new-dirs state) (ls-subdirs "."))
       ((when errp)
        (raise "Error listing new subdirectories.")
        state)
       ((unless (and (not (member-equal new-dir-name orig-dirs))
                     (member-equal new-dir-name new-dirs)))
        (cw "Prev dirs: ~x0." orig-dirs)
        (cw "New dirs: ~x0." new-dirs)
        (raise "New directory ~x0 didn't get created." new-dir-name)
        state)
       ((mv okp state) (rmtree new-dir-name))
       ((unless okp)
        (raise "Error removing directory ~x0." new-dir-name)
        state)
       ((mv errp new-dirs state) (ls-subdirs "."))
       ((when errp)
        (raise "Error listing new subdirectories.")
        state)
       ((when (member-equal new-dir-name new-dirs))
        (cw "Prev dirs: ~x0." orig-dirs)
        (cw "New dirs: ~x0." new-dirs)
        (raise "New directory didn't get deleted?")
        state))
    state))

(defconsts state (basic-mkdir-test "tmpdir1"))
(defconsts state (basic-mkdir-test "tmpdir2"))
(defconsts state (basic-mkdir-test "tmpdir3"))
