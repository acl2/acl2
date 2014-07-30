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


;; BOZO move this stuff to ACL2 utilities file

(defthmd equal-of-2-and-len
  ;; BOZO move this to ACL2 utilities
  (equal (equal 2 (len x))
         (and (consp x)
              (consp (cdr x))
              (not (consp (cdr (cdr x)))))))

(defthmd equal-of-3-and-len
  (equal (equal 3 (len x))
         (and (consp x)
              (consp (cdr x))
              (consp (cdr (cdr x)))
              (not (consp (cdr (cdr (cdr x))))))))

(defthm consp-when-consp-of-cdr-cheap
  (implies (consp (cdr x))
           (equal (consp x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))





(%autoadmit len)

(%autoprove len-when-not-consp
            (%restrict default len (equal x 'x)))

(%autoprove len-of-cons
            (%restrict default len (equal x '(cons a x))))

(%autoprove natp-of-len
            (%cdr-induction x))

(%autoprove natp-of-len-free)

(%autoprove len-under-iff
            (%use (%instance (%thm natp-of-len)))
            (%disable default natp-of-len natp-of-len-free [outside]natp-of-len))

(%autoprove |(< 0 (len x))|)

(%autoprove |(< 1 (len x))|)

(%autoprove decrement-len-when-consp)

(%autoprove equal-of-len-and-zero)

(defsection [outside]equal-of-len-and-zero-alt
  (%prove (%rule [outside]equal-of-len-and-zero-alt
                 :type outside
                 :lhs (equal (len x) 0)
                 :rhs (not (consp x))))
  (%auto)
  (%qed)
  (%enable default [outside]equal-of-len-and-zero-alt))

(%autoprove consp-of-cdr-when-len-two-cheap)


;; We can solve (consp (cdr ... (cdr x))) when we know the length of x.

(%autoprove consp-of-cdr-with-len-free)
(%autoprove consp-of-cdr-of-cdr-with-len-free)
(%autoprove consp-of-cdr-of-cdr-of-cdr-with-len-free)


;; We can solve (cdr ... (cdr x)) under iff when we know the length of x.

(%autoprove cdr-under-iff-with-len-free-in-bound)
(%autoprove cdr-of-cdr-under-iff-with-len-free-in-bound)
(%autoprove cdr-of-cdr-of-cdr-under-iff-with-len-free-in-bound)
(%autoprove cdr-of-cdr-with-len-free-past-the-end)
(%autoprove cdr-of-cdr-of-cdr-with-len-free-past-the-end)

(%autoprove len-2-when-not-cdr-of-cdr)

(%autoprove equal-when-length-different)

(%autoprove equal-of-2-and-len)

(%autoprove equal-of-3-and-len
            (%restrict default len (memberp x '(x (cdr x) (cdr (cdr x))))))

(%autoprove consp-when-consp-of-cdr-cheap)






(%autoadmit fast-len)

(%autoprove fast-len-removal
            (%autoinduct fast-len)
            (%restrict default fast-len (equal x 'x)))

(%autoadmit same-lengthp)

(%autoprove same-lengthp-removal
            (%cdr-cdr-induction x y)
            (%restrict default same-lengthp (equal x 'x)))


(%autoadmit true-listp)

(%autoprove true-listp-when-not-consp
            (%restrict default true-listp (equal x 'x)))

(%autoprove true-listp-of-cons
            (%restrict default true-listp (equal x '(cons a x))))

(%autoprove booleanp-of-true-listp
            (%cdr-induction x))

(%autoprove true-listp-of-cdr)

(%autoprove consp-when-true-listp-cheap)

(%autoprove list-of-first-and-second-when-len-2)
(%autoprove list-of-first-and-second-and-third-when-len-3)

(%autoprove cdr-when-true-listp-with-len-free-past-the-end)
(%autoprove cdr-of-cdr-when-true-listp-with-len-free-past-the-end)
(%autoprove cdr-of-cdr-of-cdr-when-true-listp-with-len-free-past-the-end)

(%autoprove cdr-under-iff-when-true-listp-with-len-free)
(%autoprove cdr-of-cdr-under-iff-when-true-listp-with-len-free)
(%autoprove cdr-of-cdr-of-cdr-under-iff-when-true-listp-with-len-free)

(defsection less-of-len-of-cdr-and-len
  ;; BOZO add to ACL2 file
  (%prove (%rule less-of-len-of-cdr-and-len
                 :lhs (< (len (cdr x)) (len x))
                 :rhs (consp x)))
  (%auto)
  (%qed)
  (%enable default less-of-len-of-cdr-and-len))




(%autoadmit list-fix)

(%autoprove list-fix-when-not-consp
            (%restrict default list-fix (equal x 'x)))

(%autoprove list-fix-of-cons
            (%restrict default list-fix (equal x '(cons a x))))

(%autoprove car-of-list-fix)
(%autoprove cdr-of-list-fix)

(%autoprove consp-of-list-fix)

(%autoprove list-fix-under-iff)

(%autoprove len-of-list-fix
            (%cdr-induction x))

(%autoprove true-listp-of-list-fix
            (%cdr-induction x))

(%autoprove list-fix-when-true-listp
            (%cdr-induction x))

(%autoprove cdr-of-list-fix-under-iff)

(%autoprove equal-of-list-fix-and-self
            (%cdr-induction x))









(%autoadmit memberp)

(%autoprove memberp-when-not-consp
            (%restrict default memberp (equal x 'x)))

(%autoprove memberp-of-cons
            (%restrict default memberp (equal x '(cons b x))))

(%autoprove booleanp-of-memberp
            (%cdr-induction x))

(%autoprove memberp-of-list-fix
            (%cdr-induction x))

(%autoprove memberp-when-memberp-of-cdr)

(%autoprove memberp-of-car)

(%autoprove memberp-of-second)

(%autoprove car-when-memberp-of-singleton-list-cheap)

(%autoprove car-when-memberp-and-not-memberp-of-cdr-cheap)

(%autoprove consp-when-memberp-cheap)

(%autoprove consp-of-cdr-when-memberp-not-car-cheap)

(%autoprove rank-when-memberp
            (%cdr-induction x))

(%autoprove rank-when-memberp-weak
            (%cdr-induction x))



(%autoadmit subsetp)

(%autoprove subsetp-when-not-consp
            (%restrict default subsetp (equal x 'x)))

(%autoprove subsetp-of-cons
            (%restrict default subsetp (equal x '(cons a x))))

(%autoprove booleanp-of-subsetp
            (%cdr-induction x))

(%autoprove subsetp-when-not-consp-two
            (%cdr-induction x))

(%autoprove subsetp-of-cons-two
            (%cdr-induction x))

(%autoprove subsetp-of-list-fix-one
            (%cdr-induction x))

(%autoprove subsetp-of-list-fix-two
            (%cdr-induction x))

(%autoprove subsetp-of-cdr)

(%autoprove in-superset-when-in-subset-one
            (%cdr-induction x))

(%autoprove in-superset-when-in-subset-two)

(%autoprove not-in-subset-when-not-in-superset-one)

(%autoprove not-in-subset-when-not-in-superset-two)

(%autoprove consp-when-nonempty-subset-cheap)

(%autoprove subsetp-reflexive
            (%cdr-induction x))

(%autoprove subsetp-transitive-one
            (%cdr-induction x))

(%autoprove subsetp-transitive-two)



(%autoadmit subsetp-badguy)

(%autoprove subsetp-badguy-membership-property
            (%cdr-induction x)
            (%restrict default subsetp-badguy (equal x 'x)))

(%autoprove subsetp-badguy-under-iff
            (%cdr-induction x)
            (%restrict default subsetp (equal x 'x))
            (%restrict default subsetp-badguy (equal x 'x)))

