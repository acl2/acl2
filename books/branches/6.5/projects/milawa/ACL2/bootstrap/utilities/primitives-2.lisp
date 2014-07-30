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
(include-book "primitives-1")
(%interactive)


;; BOZO reorganize these properly

(%autoprove natp-of-nfix
            (%enable default nfix))

(%autoprove nfix-when-natp-cheap
            (%enable default nfix))

(%autoprove nfix-when-not-natp-cheap
            (%enable default nfix))

(%autoprove equal-of-nfix-of-self)

(defsection [outside]equal-of-nfix-of-self-alt
  ;; Can't rely on term-order for outside-in.
  (%prove (%rule [outside]equal-of-nfix-of-self-alt
                 :type outside
                 :lhs (equal (nfix x) x)
                 :rhs (natp x)))
  (%auto)
  (%qed)
  (%enable default [outside]equal-of-nfix-of-self-alt))

(%autoprove equal-of-zero-and-nfix
            (%enable default nfix zp))

(defsection [outside]equal-of-zero-and-nfix-alt
  ;; Can't rely on term-order for outside-in.
  (%prove (%rule [outside]equal-of-zero-and-nfix-alt
                 :type outside
                 :lhs (equal (nfix x) 0)
                 :rhs (zp x)))
  (%auto)
  (%qed)
  (%enable default [outside]equal-of-zero-and-nfix-alt))

(%autoprove zp-when-natp-cheap
            (%enable default zp))

(%autoprove zp-when-not-natp-cheap
            (%enable default zp))

(%autoprove zp-of-nfix
            (%enable default nfix))

(%autoprove nfix-of-nfix)

(%autoprove natp-when-not-zp-cheap)

(%autoprove natp-when-zp-cheap)

(%autoprove nfix-when-zp-cheap)

(%autoprove equal-of-nfix-with-positive-constant
            (%enable default nfix))



;; Addition.

(%autoprove natp-of-plus
            (%use (build.axiom (axiom-natp-of-plus))))

(%autoprove plus-under-iff
            (%disable default natp-of-plus [outside]natp-of-plus)
            (%use (%thm natp-of-plus)))

(%autoprove commutativity-of-+
            (%use (build.axiom (axiom-commutativity-of-+))))

(%autoprove associativity-of-+
            (%use (build.axiom (axiom-associativity-of-+))))

(%disable default [outside]associativity-of-+) ;; Interferes with constant gathering

(%autoprove commutativity-of-+-two
            (%use (%instance (build.axiom (axiom-commutativity-of-+)) (b (+ b c)))))

(%autoprove gather-constants-from-plus-of-plus)



(%autoprove plus-completion-left
            (%use (build.axiom (axiom-plus-when-not-natp-left)))
            (%use (build.instantiation (build.axiom (axiom-plus-of-zero-when-natural))
                                       (list (cons 'a 'b))))
            (%use (build.axiom (axiom-plus-when-not-natp-left)))
            (%use (build.instantiation (build.axiom (axiom-plus-when-not-natp-left))
                                       (list (cons 'a 'b)
                                             (cons 'b ''0)))))

(%autoprove plus-completion-right
            (%disable default nfix plus-completion-left)
            (%use (%instance (%thm plus-completion-left) (a b) (b a))))

(%autoprove plus-of-zero-right
            (%enable default plus-completion-right)
            (%use (build.axiom (axiom-plus-of-zero-when-natural))))

(%autoprove plus-of-zero-left
            (%use (%instance (%thm commutativity-of-+) (a 0) (b a))))

(%autoprove plus-when-zp-left-cheap
            (%use (%thm plus-completion-left)))

(%autoprove plus-when-zp-right-cheap
            (%use (%thm plus-completion-right)))

(%autoprove plus-of-nfix-left
            (%enable default nfix))

(%autoprove plus-of-nfix-right
            (%enable default nfix))




;; Less-Than Relation.

(%autoprove booleanp-of-<
            (%use (build.axiom (axiom-<-nil-or-t))))

(%autoprove irreflexivity-of-<
            (%use (build.axiom (axiom-irreflexivity-of-<))))

(%autoprove less-of-zero-right
            (%use (build.axiom (axiom-less-of-zero-right))))

(%autoprove less-completion-right
            (%use (build.axiom (axiom-less-completion-right))))

(%autoprove less-when-zp-right-cheap
            (%use (%thm less-completion-right)))

(%autoprove less-of-zero-left
            (%use (build.axiom (axiom-less-of-zero-left-when-natp))))

(%autoprove less-completion-left
            (%use (build.axiom (axiom-less-completion-left))))

(%autoprove less-when-zp-left-cheap
            (%use (%thm less-completion-left)))

(%autoprove less-of-nfix-left
            (%enable default nfix))

(%autoprove less-of-nfix-right
            (%enable default nfix))

(%autoprove transitivity-of-<
            (%use (build.axiom (axiom-transitivity-of-<))))

(%autoprove antisymmetry-of-<
            (%disable default transitivity-of-<)
            (%use (%instance (%thm transitivity-of-<) (a a) (b b) (c a))))

(%autoprove trichotomy-of-<
            (%use (build.axiom (axiom-trichotomy-of-<-when-natp))))

(%autoprove one-plus-trick
            (%use (build.axiom (axiom-one-plus-trick))))

(%autoprove less-of-one-right
            (%use (build.axiom (axiom-natural-less-than-one-is-zero))))

(%autoprove less-of-one-left
            (%enable default zp))

(%autoprove transitivity-of-<-two
            (%enable default nfix)
            (%disable default trichotomy-of-<)
            (%use (%instance (%thm trichotomy-of-<) (a b) (b c))))

(%autoprove transitivity-of-<-three)

(%autoprove transitivity-of-<-four)


