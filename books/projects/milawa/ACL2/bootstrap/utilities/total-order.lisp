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
(include-book "primitives")
(%interactive)


(defsection consp-when-nothing-else-cheap
  (%prove (%rule consp-when-nothing-else-cheap
                 :hyps (list (%hyp (not (natp x)) :limit 0)
                             (%hyp (not (symbolp x)) :limit 0))
                 :lhs (consp x)
                 :rhs t))
  (%use (build.axiom (axiom-closed-universe)))
  (%auto)
  (%qed)
  (%enable default consp-when-nothing-else-cheap))

(%autoadmit <<)

(defmacro %<<-induction (x y)
  `(%induct (rank x)
            ((natp x) nil)
            ((natp y) nil)
            ((symbolp x) nil)
            ((symbolp y) nil)
            ((and (consp x)
                  (consp y))
             (((,x (car ,x)) (,y (car ,y)))
              ((,x (cdr ,x)) (,y (cdr ,y)))))))

(%autoprove booleanp-of-<<
            (%<<-induction x y)
            (%restrict default << (equal x 'x)))

(%autoprove irreflexivity-of-<<
            (%induct (rank x)
                     ((natp x) nil)
                     ((symbolp x) nil)
                     ((consp x)
                      (((x (car x)))
                       ((x (cdr x))))))
            (%restrict default << (equal x 'x)))

(%autoprove asymmetry-of-<<
            (%<<-induction x y)
            (%restrict default << (or (equal x 'x)
                                      (equal x 'y))))

(%autoprove transitivity-of-<<
            (%induct (rank x)
                     ((not (consp x))
                      nil)
                     ((consp x)
                      (((x (car x)) (y (car y)) (z (car z)))
                       ((x (cdr x)) (y (cdr y)) (z (cdr z))))))
            (%auto :strategy (cleanup split crewrite))
            (%restrict default << (or (equal x 'x)
                                      (equal x 'y)))
            (%auto :strategy (cleanup split crewrite elim)))

(%autoprove forcing-trichotomy-of-<<
            (%<<-induction x y)
            (%restrict default << (or (equal x 'x)
                                      (equal x 'y))))

(%ensure-exactly-these-rules-are-missing "../../utilities/total-order")

