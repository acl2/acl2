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
(include-book "fast-image")


(%autoprove rw.ftrace->rhs-of-rw.fast-crewrite-core
            (%disable default rw.trace-fast-image-of-rw.crewrite-core)
            (%use (%instance (%thm rw.trace-fast-image-of-rw.crewrite-core))))


#||

;; this shouldn't be needed anymore

(%autoadmit rw.aux-fast-crewrite)

(%autoprove rw.ftracep-of-rw.aux-fast-crewrite
            (%autoinduct rw.aux-fast-crewrite)
            (%restrict default rw.aux-fast-crewrite (equal n 'n)))

(%autoprove rw.trace-fast-image-of-rw.aux-crewrite
            (%autoinduct rw.aux-crewrite)
            (%restrict default rw.aux-crewrite (equal n 'n))
            (%restrict default rw.aux-fast-crewrite (equal n 'n)))

||#

(%autoadmit rw.fast-crewrite)

(%autoprove rw.ftracep-of-rw.fast-crewrite
            (%enable default rw.fast-crewrite))

(%autoprove rw.trace-fast-image-of-rw.crewrite
            (%enable default rw.crewrite rw.fast-crewrite))

(%autoprove rw.ftrace->rhs-of-rw.fast-crewrite
            (%disable default rw.trace-fast-image-of-rw.crewrite)
            (%use (%instance (%thm rw.trace-fast-image-of-rw.crewrite))))

(%autoprove rw.ftrace->fgoals-of-rw.fast-crewrite
            (%disable default rw.trace-fast-image-of-rw.crewrite)
            (%use (%instance (%thm rw.trace-fast-image-of-rw.crewrite))))
