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
(include-book "aux-split")
(%interactive)


(local (%disable default
                 type-set-like-rules
                 expensive-arithmetic-rules
                 expensive-arithmetic-rules-two
                 expensive-term/formula-inference
                 expensive-subsetp-rules
                 unusual-consp-rules))

(%autoadmit clause.aux-limsplit)

(%autoprove true-listp-of-clause.aux-limsplit
            (%autoinduct clause.aux-limsplit)
            (%restrict default clause.aux-limsplit (memberp todo '(todo 'nil))))

;; (%autoprove consp-of-clause.aux-limsplit
;;             (%autoinduct clause.aux-limsplit)
;;             (%restrict default clause.aux-limsplit (memberp todo '(todo 'nil))))

;; (%autoprove clause.aux-limsplit-under-iff
;;             (%autoinduct clause.aux-limsplit)
;;             (%restrict default clause.aux-limsplit (memberp todo '(todo 'nil))))

(%autoprove forcing-term-list-listp-of-clause.aux-limsplit
            (%autoinduct clause.aux-limsplit)
            (%restrict default clause.aux-limsplit (memberp todo '(todo 'nil))))

(%autoprove forcing-term-list-list-atblp-of-clause.aux-limsplit
            (%autoinduct clause.aux-limsplit)
            (%restrict default clause.aux-limsplit (memberp todo '(todo 'nil))))

(%autoprove forcing-cons-listp-of-clause.aux-limsplit
            (%autoinduct clause.aux-limsplit)
            (%restrict default clause.aux-limsplit (memberp todo '(todo 'nil))))





;; (%autoprove clause.aux-limsplit-when-double-negative
;;             (%restrict default clause.aux-limsplit (equal todo '(cons a x))))

;; (%autoprove clause.aux-limsplit-when-negative-1
;;             (%restrict default clause.aux-limsplit (equal todo '(cons a x))))

;; (%autoprove clause.aux-limsplit-when-negative-2
;;             (%restrict default clause.aux-limsplit (equal todo '(cons a x))))

;; (%autoprove clause.aux-limsplit-when-negative-3
;;             (%restrict default clause.aux-limsplit (equal todo '(cons a x))))

;; (%autoprove clause.aux-limsplit-when-negative-4
;;             (%restrict default clause.aux-limsplit (equal todo '(cons a x))))

;; (%autoprove clause.aux-limsplit-when-positive-1
;;             (%restrict default clause.aux-limsplit (equal todo '(cons a x))))

;; (%autoprove clause.aux-limsplit-when-positive-2
;;             (%restrict default clause.aux-limsplit (equal todo '(cons a x))))

;; (%autoprove clause.aux-limsplit-when-positive-3
;;             (%restrict default clause.aux-limsplit (equal todo '(cons a x))))

;; (%autoprove clause.aux-limsplit-when-positive-4
;;             (%restrict default clause.aux-limsplit (equal todo '(cons a x))))

;; (%autoprove clause.aux-limsplit-when-not-consp
;;             (%restrict default clause.aux-limsplit (equal todo 'todo)))

;; (%autoprove clause.aux-limsplit-when-zp
;;             (%restrict default clause.aux-limsplit (equal todo 'todo)))

;; (%create-theory clause.aux-limsplit-openers)
;; (%enable clause.aux-limsplit-openers
;;          clause.aux-limsplit-when-double-negative
;;          clause.aux-limsplit-when-negative-1
;;          clause.aux-limsplit-when-negative-1
;;          clause.aux-limsplit-when-negative-2
;;          clause.aux-limsplit-when-negative-3
;;          clause.aux-limsplit-when-negative-4
;;          clause.aux-limsplit-when-positive-1
;;          clause.aux-limsplit-when-positive-2
;;          clause.aux-limsplit-when-positive-3
;;          clause.aux-limsplit-when-positive-4
;;          clause.aux-limsplit-when-not-consp
;;          clause.aux-limsplit-when-zp)

