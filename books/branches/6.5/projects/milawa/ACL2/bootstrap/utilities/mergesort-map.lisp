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
(include-book "mergesort")
(%interactive)


(%autoadmit ordered-mapp)

(%autoprove ordered-mapp-when-not-consp
            (%restrict default ordered-mapp (equal x 'x)))

(%autoprove ordered-mapp-when-not-consp-of-cdr
            (%restrict default ordered-mapp (equal x 'x)))

(%autoprove ordered-mapp-of-cons
            (%restrict default ordered-mapp (equal x '(cons a x))))

(%autoprove booleanp-of-ordered-mapp
            (%cdr-induction x))

(%autoprove ordered-mapp-of-cdr-when-ordered-mapp)

(%autoprove lemma-for-uniquep-when-ordered-mapp
            (%cdr-induction x))

(%autoprove uniquep-of-domain-when-ordered-mapp
            (%cdr-induction x)
            (%enable default lemma-for-uniquep-when-ordered-mapp))



(%autoadmit merge-maps)

(%autoprove merge-maps-when-not-consp-left
            (%restrict default merge-maps (and (equal x 'x) (equal y 'y))))

(%autoprove merge-maps-when-not-consp-right
            (%restrict default merge-maps (and (equal x 'x) (equal y 'y))))

(%autoprove merge-maps-of-cons-and-cons
            (%restrict default merge-maps (and (or (equal x '(cons a x))
                                                   (equal x '(cons b x)))
                                               (or (equal y '(cons a y))
                                                   (equal y '(cons b y))))))

(%autoprove consp-of-merge-maps
            (%restrict default merge-maps (and (equal x 'x) (equal y 'y))))

(%autoprove lookup-of-first-of-first)

(%autoprove lookup-when-not-first-of-first)

(%autoprove smaller-than-merge-maps
            (%autoinduct merge-maps)
            (%restrict default merge-maps (and (equal x 'x) (equal y 'y))))

(%autoprove ordered-mapp-of-merge-maps
            (%autoinduct merge-maps x y)
            (%restrict default merge-maps (and (equal x 'x) (equal y 'y))))

(%autoprove mapp-of-merge-maps
            (%autoinduct merge-maps x y)
            (%restrict default merge-maps (and (equal x 'x) (equal y 'y))))

(%autoprove lookup-of-merge-maps
            (%autoinduct merge-maps x y)
            (%restrict default merge-maps (and (equal x 'x) (equal y 'y)))
            (%enable default
                     lemma-2-for-ordered-list-subsetp-property
                     lemma-for-uniquep-when-ordered-mapp))



(%autoadmit mergesort-map)

(%autoprove mergesort-map-when-not-consp
            (%restrict default mergesort-map (equal x 'x)))

(%autoprove mergesort-map-when-not-consp-of-cdr
            (%restrict default mergesort-map (equal x 'x)))

(%autoprove mapp-of-mergesort-map
            (%autoinduct mergesort-map)
            (%restrict default mergesort-map (equal x 'x)))

(%autoprove ordered-mapp-of-mergesort-map
            (%autoinduct mergesort-map)
            (%restrict default mergesort-map (equal x 'x)))

(verify-guards mergesort-map)

(%autoprove uniquep-of-domain-of-mergesort-map)

(%autoprove lemma-1-for-lookup-of-mergesort-map
            (%use (%instance (%thm halve-list-lookup-property))))

(%autoprove lemma-2-for-lookup-of-mergesort-map
            (%use (%instance (%thm halve-list-lookup-property))))

(%autoprove lookup-of-mergesort-map
            (%autoinduct mergesort-map)
            (%restrict default mergesort-map (equal x 'x))
            (%enable default lemma-1-for-lookup-of-mergesort-map
                             lemma-2-for-lookup-of-mergesort-map))

(%autoprove submapp-of-mergesort-map-and-self-left
            (%use (%instance (%thm submapp-badguy-membership-property)
                             (x (mergesort-map x))
                             (y x))))

(%autoprove submapp-of-mergesort-map-and-self-right
            (%use (%instance (%thm submapp-badguy-membership-property)
                             (y (mergesort-map x))
                             (x x))))

(%autoprove submapp-of-mergesort-map-left)

(%autoprove submapp-of-mergesort-map-right)



(%autoadmit ordered-map-submapp)

(%autoprove ordered-map-submapp-when-not-consp-left
            (%restrict default ordered-map-submapp (and (equal x 'x) (equal y 'y))))

(%autoprove ordered-map-submapp-when-not-consp-right
            (%restrict default ordered-map-submapp (and (equal x 'x) (equal y 'y))))

(%autoprove ordered-map-submapp-of-cons-and-cons
            (%restrict default ordered-map-submapp (and (or (equal x '(cons a x))
                                                            (equal x '(cons b x)))
                                                        (or (equal y '(cons a y))
                                                            (equal y '(cons b y))))))

(%autoprove booleanp-of-ordered-map-submapp
            (%autoinduct ordered-map-submapp x y))

(%autoprove lemma-1-for-ordered-map-submapp-property)

(%autoprove lemma-2-for-ordered-map-submapp-property
            (%enable default submapp))

(%autoprove lemma-3-for-ordered-map-submapp-property
            (%disable default equal-of-lookups-when-submapp)
            (%use (%instance (%thm equal-of-lookups-when-submapp)
                             (x x)
                             (y y)
                             (a (car (car x))))))

(%autoprove lemma-4-for-ordered-map-submapp-property-aux
            (%autoinduct submapp1 dom x y)
            (%restrict default submapp1 (equal domain 'dom)))

(%autoprove lemma-4-for-ordered-map-submapp-property
            (%enable default
                     lemma-4-for-ordered-map-submapp-property-aux
                     lemma-for-uniquep-when-ordered-mapp
                     submapp))

(%autoprove lemma-5-for-ordered-map-submapp-property
            (%disable default lemma-for-uniquep-when-ordered-mapp)
            (%use (%instance (%thm lemma-for-uniquep-when-ordered-mapp)
                             (a (first (first x)))
                             (x y))))

(%autoprove lemma-6-for-ordered-map-submapp-property
            (%disable default equal-of-lookups-when-submapp)
            (%use (%instance (%thm equal-of-lookups-when-submapp)
                             (a (first (first x)))
                             (x x)
                             (y y)))
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default lookup (or (equal x 'x) (equal y 'y))))

(%autoprove lemma-7-for-ordered-map-submapp-property-aux
            (%autoinduct submapp1 dom x y)
            (%restrict default submapp1 (equal domain 'dom)))

(%autoprove lemma-7-for-ordered-map-submapp-property
            (%enable default
                     submapp
                     lemma-for-uniquep-when-ordered-mapp)
            (%use (%instance (%thm lemma-7-for-ordered-map-submapp-property-aux)
                             (dom (domain x)))))


(%autoprove ordered-map-submapp-property
            (%autoinduct ordered-map-submapp x y)
            (%enable default lemma-for-uniquep-when-ordered-mapp
                     lemma-1-for-ordered-map-submapp-property
                             lemma-2-for-ordered-map-submapp-property
                             lemma-3-for-ordered-map-submapp-property
                             lemma-4-for-ordered-map-submapp-property
                             lemma-5-for-ordered-map-submapp-property
                             lemma-6-for-ordered-map-submapp-property
                             lemma-7-for-ordered-map-submapp-property))

(%autoprove lemma-for-ordered-listp-when-ordered-mapp
            (%restrict default << (and (equal x 'a) (equal y 'b))))

(%autoprove ordered-listp-when-ordered-mapp
            (%cdr-induction x)
            (%enable default lemma-for-ordered-listp-when-ordered-mapp))

(%autoprove ordered-listp-of-mergesort-map)

(%ensure-exactly-these-rules-are-missing "../../../utilities/mergesort")

