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
(include-book "utilities-1")
(%interactive)

(defsection equal-of-cdr-and-self
  ;; BOZO I don't have this rule in ACL2.  Maybe I should add it?
  ;; BOZO Move this to primitives somewhere
  (%prove (%rule equal-of-cdr-and-self
                 :lhs (equal x (cdr x))
                 :rhs (not x)))
  (local (%disable default rank-of-cdr [outside]rank-of-cdr))
  (%use (%instance (%thm rank-of-cdr)))
  (%auto)
  (%qed)
  (%enable default equal-of-cdr-and-self))

(%autoadmit app)

(%autoprove app-when-not-consp
            (%restrict default app (equal x 'x)))

(%autoprove app-of-cons
            (%restrict default app (equal x '(cons a x))))

(%autoprove app-of-list-fix-one
            (%cdr-induction x))

(%autoprove app-of-list-fix-two
            (%cdr-induction x))

(%autoprove app-when-not-consp-two
            (%cdr-induction x))

(%autoprove app-of-singleton-list-cheap)

(%autoprove true-listp-of-app
            (%cdr-induction x))

(%autoprove app-of-app
            (%cdr-induction x))

(%autoprove memberp-of-app
            (%cdr-induction x))

(%autoprove consp-of-app)

(%autoprove app-under-iff)

(%autoprove len-of-app
            (%cdr-induction x))

(%autoprove subsetp-of-app-one
            (%cdr-induction x))

(%autoprove subsetp-of-app-two
            (%use (%instance (%thm subsetp-badguy-membership-property) (x x) (y (app x y)))))

(%autoprove subsetp-of-app-three
            (%use (%instance (%thm subsetp-badguy-membership-property) (x y) (y (app x y)))))

(%autoprove subsetp-of-app-when-subsets
            (%use (%instance (%thm subsetp-badguy-membership-property) (x (app x w)) (y (app y z)))))

(%autoprove subsetp-of-symmetric-apps
            (%use (%instance (%thm subsetp-badguy-membership-property) (x (app x y)) (y (app y x)))))

(%autoprove weirdo-rule-for-subsetp-of-app-one)
(%autoprove weirdo-rule-for-subsetp-of-app-two)

(%autoprove cdr-of-app-when-x-is-consp)
(%autoprove car-of-app-when-x-is-consp)
(%autoprove memberp-of-app-onto-singleton)

(%autoprove subsetp-of-app-onto-singleton-with-cons
            (%use (%instance (%thm subsetp-badguy-membership-property) (x (app x (list a))) (y (cons a x)))))

(%autoprove subsetp-of-cons-with-app-onto-singleton
            (%use (%instance (%thm subsetp-badguy-membership-property) (x (cons a x)) (y (app x (list a))))))

(%autoprove subsetp-of-cons-of-app-of-app-one
            (%use (%instance (%thm subsetp-badguy-membership-property) (x x) (y (cons b (app y (app x z)))))))

(%autoprove subsetp-of-cons-of-app-of-app-two
            (%use (%instance (%thm subsetp-badguy-membership-property) (x x) (y (cons a (app y (app z x)))))))

(%autoprove subsetp-of-app-of-app-when-subsetp-one
            (%use (%instance (%thm subsetp-badguy-membership-property) (x x) (y (app a (app y b))))))

(%autoprove subsetp-of-app-of-app-when-subsetp-two
            (%use (%instance (%thm subsetp-badguy-membership-property) (x x) (y (app a (app b y))))))

(%autoprove app-of-cons-of-list-fix-right
            (%cdr-induction x))

(%autoprove app-of-cons-when-not-consp-right
            (%cdr-induction x))

(%autoprove equal-of-app-and-app-when-equal-lens
            (%cdr-cdr-induction a c))

(%autoprove lemma-for-equal-of-app-and-self
            (%cdr-induction x))

(%autoprove equal-of-app-and-self
            (%cdr-induction x)
            (%enable default lemma-for-equal-of-app-and-self)
            (%auto :strategy (cleanup urewrite split crewrite)) ;; elim uglies it up
            (%use (%instance (%thm len-of-app)))
            (%use (%instance (%thm len-of-app) (x (cdr x))))
            (%disable default len-of-app [outside]len-of-app))

