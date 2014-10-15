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
(include-book "utilities")
(include-book "total-order")
(%interactive)


(%autoprove mapp-of-rev
            (%cdr-induction x))

(%autoadmit halve-list-aux)

(%autoadmit halve-list)

(%autoprove halve-list-aux-when-not-consp
            (%autoinduct halve-list-aux)
            (%restrict default halve-list-aux (equal x 'x)))

(%autoprove halve-list-aux-when-not-consp-of-cdr
            (%autoinduct halve-list-aux)
            (%restrict default halve-list-aux (equal x 'x)))

(%autoprove halve-list-aux-append-property
            (%autoinduct halve-list-aux)
            (%restrict default halve-list-aux (equal x 'x)))

(%autoprove halve-list-aux-len-1
            (%autoinduct halve-list-aux)
            (%restrict default halve-list-aux (equal x 'x)))

(%autoprove halve-list-aux-len-2
            (%autoinduct halve-list-aux)
            (%restrict default halve-list-aux (equal x 'x)))

(%autoprove halve-list-correct
            (%enable default halve-list))

(%autoprove halve-list-len-1
            (%enable default halve-list)
            (%disable default halve-list-aux-len-1)
            (%use (%instance (%thm halve-list-aux-len-1)
                             (mid x) (x x) (acc nil))))

(%autoprove halve-list-len-2
            (%enable default halve-list))

(%autoprove halve-list-membership-property
            (%disable default memberp-of-app)
            (%use (%instance (%thm memberp-of-app)
                             (x (rev (car (halve-list x))))
                             (y (cdr (halve-list x))))))

(%autoprove halve-list-lookup-property
            (%disable default lookup-of-app)
            (%use (%instance (%thm lookup-of-app)
                             (x (rev (car (halve-list x))))
                             (y (cdr (halve-list x))))))

(%autoprove mapp-of-first-of-halve-list-aux-1
            (%autoinduct halve-list-aux)
            (%restrict default halve-list-aux (equal x 'x)))

(%autoprove mapp-of-first-of-halve-list-aux-2
            (%autoinduct halve-list-aux)
            (%restrict default halve-list-aux (equal x 'x)))

(%autoprove mapp-of-first-of-halve-list-1
            (%enable default halve-list))

(%autoprove mapp-of-first-of-halve-list-2
            (%enable default halve-list))


(%autoadmit ordered-listp)

(%autoprove ordered-listp-when-not-consp
            (%restrict default ordered-listp (equal x 'x)))

(%autoprove ordered-listp-when-not-consp-of-cdr
            (%restrict default ordered-listp (equal x 'x)))

(%autoprove ordered-listp-of-cons
            (%restrict default ordered-listp (equal x '(cons a x))))

(%autoprove booleanp-of-ordered-listp
            (%cdr-induction x))

(%autoprove lemma-for-uniquep-when-ordered-listp
            (%cdr-induction x))

(%autoprove uniquep-when-ordered-listp
            (%cdr-induction x)
            (%enable default lemma-for-uniquep-when-ordered-listp))


(%autoadmit merge-lists)

(%autoprove merge-lists-when-not-consp-left
            (%restrict default merge-lists (and (equal x 'x) (equal y 'y))))

(%autoprove merge-lists-when-not-consp-right
            (%restrict default merge-lists (and (equal x 'x) (equal y 'y))))

(%autoprove merge-lists-of-cons-and-cons
            (%restrict default merge-lists (and (or (equal x '(cons a x))
                                                    (equal x '(cons b x)))
                                                (or (equal y '(cons a y))
                                                    (equal y '(cons b y))))))

(%autoprove consp-of-merge-lists
            (%autoinduct merge-lists)
            (%restrict default merge-lists (and (equal x 'x) (equal y 'y))))

(%autoprove smaller-than-merge-lists
            (%autoinduct merge-lists)
            (%restrict default merge-lists (and (equal x 'x) (equal y 'y))))

(%autoprove ordered-listp-of-merge-lists
            (%autoinduct merge-lists)
            (%restrict default merge-lists (and (equal x 'x) (equal y 'y))))

(%autoprove memberp-of-merge-lists
            (%autoinduct merge-lists)
            (%restrict default merge-lists (and (equal x 'x) (equal y 'y))))


(%autoadmit mergesort)

(%autoprove mergesort-when-not-consp
            (%restrict default mergesort (equal x 'x)))

(%autoprove mergesort-when-not-consp-of-cdr
            (%restrict default mergesort (equal x 'x)))

(%autoprove ordered-listp-of-mergesort
            (%autoinduct mergesort)
            (%restrict default mergesort (equal x 'x)))

(%autoprove uniquep-of-mergesort
            (%enable default uniquep-when-ordered-listp))

(%autoprove lemma-for-memberp-of-mergesort
            (%use (%instance (%thm halve-list-membership-property))))

(%autoprove lemma-2-for-memberp-of-mergesort
            (%use (%instance (%thm halve-list-membership-property))))

(%autoprove memberp-of-mergesort
            (%autoinduct mergesort)
            (%restrict default mergesort (equal x 'x))
            (%auto :strategy (cleanup split urewrite crewrite))
            (%enable default
                     lemma-for-memberp-of-mergesort
                     lemma-2-for-memberp-of-mergesort))

(%autoprove subsetp-of-mergesort-left
            (%use (%instance (%thm subsetp-badguy-membership-property)
                             (x (mergesort x))
                             (y y)))
            (%use (%instance (%thm subsetp-badguy-membership-property)
                             (x x)
                             (y y))))

(%autoprove subsetp-of-mergesort-right
            (%use (%instance (%thm subsetp-badguy-membership-property)
                             (x x)
                             (y (mergesort y)))))



(%autoadmit ordered-list-subsetp)

(%autoprove booleanp-of-ordered-list-subsetp
            (%autoinduct ordered-list-subsetp)
            (%restrict default ordered-list-subsetp (and (equal x 'x) (equal y 'y))))

(%autoprove lemma-1-for-ordered-list-subsetp-property)

(%autoprove lemma-2-for-ordered-list-subsetp-property)

(%autoprove lemma-3-for-ordered-list-subsetp-property
            (%cdr-induction x)
            (%enable default
                     lemma-2-for-ordered-list-subsetp-property
                     lemma-for-uniquep-when-ordered-listp))

(%autoprove lemma-4-for-ordered-list-subsetp-property
            (%autoinduct ordered-listp x)
            (%enable default
                     lemma-1-for-ordered-list-subsetp-property
                     lemma-2-for-ordered-list-subsetp-property
                     lemma-3-for-ordered-list-subsetp-property))

(%autoprove ordered-list-subsetp-property
            (%autoinduct ordered-list-subsetp x y)
            (%restrict default ordered-list-subsetp (and (equal x 'x) (equal y 'y)))
            (%enable default
                     lemma-1-for-ordered-list-subsetp-property
                     lemma-2-for-ordered-list-subsetp-property
                     lemma-3-for-ordered-list-subsetp-property
                     lemma-4-for-ordered-list-subsetp-property))


