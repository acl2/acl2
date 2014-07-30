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


(%autoadmit mapp)

(%autoprove mapp-when-not-consp
            (%restrict default mapp (equal x 'x)))

(%autoprove mapp-of-cons
            (%restrict default mapp (equal x '(cons a x))))

(%autoprove booleanp-of-mapp
            (%cdr-induction x))

(%autoprove mapp-of-list-fix
            (%cdr-induction x))

(%autoprove mapp-of-app
            (%cdr-induction x))



(%autoadmit cons-fix)

(%autoprove cons-fix-when-not-consp
            (%restrict default cons-fix (equal x 'x)))

(%autoprove cons-fix-when-consp
            (%restrict default cons-fix (equal x 'x)))

(%autoprove consp-of-cons-fix
            (%car-cdr-elim x))

(%autoprove cons-fix-under-iff
            (%car-cdr-elim x))

(%autoprove cons-fix-of-cons)

(%autoprove car-of-cons-fix)

(%autoprove cdr-of-cons-fix)



(%autoadmit lookup)

(%autoprove lookup-when-not-consp
            (%restrict default lookup (equal x 'x)))

(%autoprove lookup-of-cons
            (%restrict default lookup (equal x '(cons b x))))

(%autoprove lookup-of-list-fix
            (%cdr-induction x))

(%autoprove lookup-of-app
            (%cdr-induction x))

(%autoprove car-of-lookup-when-found
            (%cdr-induction map))

(%autoprove consp-of-lookup-under-iff
            (%cdr-induction x))



(%autoadmit update)

(%autoprove car-of-update
            (%enable default update))

(%autoprove cdr-of-update
            (%enable default update))

(%autoprove consp-of-update
            (%enable default update))

(%autoprove update-of-list-fix
            (%enable default update))

(%autoprove mapp-of-update-when-mapp
            ;; BOZO I think this should be forced
            (%enable default update))

(%autoprove lookup-of-update
            (%enable default update))



(%autoadmit domain)

(%autoprove domain-when-not-consp
            (%restrict default domain (equal x 'x)))

(%autoprove domain-of-cons
            (%restrict default domain (equal x '(cons a x))))

(%autoprove domain-of-list-fix
            (%cdr-induction x))

(%autoprove consp-of-domain)

(%autoprove true-listp-of-domain
            (%cdr-induction x))

(%autoprove domain-of-app
            (%cdr-induction x))

(%autoprove domain-of-update
            (%enable default update))

(%autoprove memberp-of-domain-when-memberp
            (%cdr-induction x))

(%autoprove memberp-of-domain-when-memberp-of-subset-domain
            (%cdr-induction x))

(%autoprove subsetp-of-domains
            (%use (%instance (%thm subsetp-badguy-membership-property)
                             (x (domain x))
                             (y (domain y)))))

(%autoprove uniquep-when-uniquep-of-domain
            (%cdr-induction x))

(%autoprove memberp-of-domain-under-iff
            (%cdr-induction x))

(%autoprove rev-of-domain
            (%cdr-induction x))

(%autoprove domain-of-rev)



(%autoadmit fast-domain$)

(%autoprove fast-domain$-when-not-consp
            (%restrict default fast-domain$ (equal x 'x)))

(%autoprove fast-domain$-of-cons
            (%restrict default fast-domain$ (equal x '(cons a x))))

(%autoprove forcing-fast-domain$-removal
            (%autoinduct fast-domain$)
            (%enable default fast-domain$-when-not-consp fast-domain$-of-cons))



(%autoadmit range)

(%autoprove range-when-not-consp
            (%restrict default range (equal x 'x)))

(%autoprove range-of-cons
            (%restrict default range (equal x '(cons a x))))

(%autoprove range-of-list-fix
            (%cdr-induction x))

(%autoprove true-listp-of-range
            (%cdr-induction x))

(%autoprove len-of-range
            (%cdr-induction x))

(%autoprove range-of-app
            (%cdr-induction x))



(%autoadmit fast-range$)

(%autoprove fast-range$-when-not-consp
            (%restrict default fast-range$ (equal x 'x)))

(%autoprove fast-range$-of-cons
            (%restrict default fast-range$ (equal x '(cons a x))))

(%autoprove forcing-fast-range$-removal
            (%autoinduct fast-range$)
            (%enable default fast-range$-when-not-consp fast-range$-of-cons))

