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
(include-book "utilities-4")
(%interactive)



(%autoadmit firstn)

(%autoprove firstn-of-zero
            (%restrict default firstn (equal n ''0)))

(%autoprove true-listp-of-firstn
            (%autoinduct firstn)
            (%restrict default firstn (equal n 'n)))

(%autoprove consp-of-firstn
            (%autoinduct firstn)
            (%restrict default firstn (or (equal n 'n) (equal n ''1))))

(%autoprove firstn-under-iff
            (%restrict default firstn (equal n 'n)))

(%autoprove firstn-of-list-fix
            (%autoinduct firstn)
            (%restrict default firstn (equal n 'n)))

(%autoprove firstn-of-len
            (%cdr-induction x)
            (%restrict default firstn (equal n '(+ '1 (len x2)))))

(%autoprove len-of-firstn
            (%autoinduct firstn)
            (%restrict default firstn (or (equal n 'n) (equal n ''1))))

(%autoprove firstn-of-too-many
            (%autoinduct firstn)
            (%restrict default firstn (equal n 'n)))

(defsection firstn-of-too-many-replacement
  ;; BOZO fix acl2 to limit this
  ;;        -- NO, wait! First check if we need to do that now that we
  ;;           have our cache working
  (%prove (%rule firstn-of-too-many-replacement
                 :hyps (list (%hyp (< (len x) n) :limit 1))
                 :lhs (firstn n x)
                 :rhs (list-fix x)))
  (%auto)
  (%qed)
  (%disable default firstn-of-too-many)
  (%enable default firstn-of-too-many-replacement))

(%autoprove firstn-of-app
            ;; BOZO check if we still need this disable with our cache
            (%autoinduct firstn)
            (%disable default len-when-tuplep trichotomy-of-< antisymmetry-of-<)
            (%restrict default firstn (equal n 'n)))

(%autoprove subsetp-of-firstn-when-in-range
            (%autoinduct firstn)
            (%restrict default firstn (equal n 'n)))
