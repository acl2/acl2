((:FILES
"
.:
Makefile
Readme.lsp
bsort.lisp
convert-perm-to-how-many.lisp
equisort.lisp
equisort2.lisp
equisort3.lisp
isort.lisp
msort.lisp
no-dups-qsort.lisp
ordered-perms.lisp
perm.lisp
qsort.lisp
script.lsp
sorts-equivalent.lisp
sorts-equivalent2.lisp
sorts-equivalent3.lisp
")
 (:TITLE    "Sorting")
 (:AUTHOR/S 
  "J Moore"
  )
 (:KEYWORDS ; non-empty list of keywords, case-insensitive
   "sorting"
   )
 (:ABSTRACT "
We prove several sort algorithms equivalent, by proving them correct.  Perm is
handled by conversion to how-many.  We take three approaches to package
everything up.  To see samples of the final results (e.g., by approach 3) see
sorts-equivalent3.lisp.

To prove two sort algorithms equal it is sufficient, by the results in
ordered-perms, to show that they both return ordered true-lists that are
perms of each other.  

Some sorts always return true-lists, while other sorts return true-lists only
on true-lists.

We take  three different approaches, essentially coded in
equisort
equisort2
equisort3

In equisort we use constrained functions and set up a ``strong equivalence''
and a ``weak equivalence''.  Instantiating these for a given sort function,
sort, generates either a (true-listp (sort x)) or a (implies (true-listp x)
(true-listp (sort x))).  The wart in this is that we have to have two
independent sets of constrained functions, one constrained always to be a
true-list and the other constrained only to preserve true-lists.

The beauty of using constrained functions is that instantiating the equisort
theorem generates clean and beautiful theorems to prove about your sort
algorithm.  You just have to know whether to instantiate the weak or the
strong version and you have to know the names of the constrained functions
used in each of those.

In equisort2, we have only one set of constrained functions but add another
constrained function, sorthyp, which can be selected to be either (the
constant function) t or true-listp.  

So equisort2 shares with equisort the beauty of generating nice theorems.
But it is better because you only need to know one scheme and can choose to
use the hyp function to handle the true-listp problem.

Finally, equisort3 avoids constrained functions and just uses rewrite rules.
It rewrites (equal a b) to t and forces the hyps its needs.

This is nice because you don't mess with instantiations.  But rewriting
(equal a b) is dangerous, so you have to enable this rule.  Furthermore, if
you're not careful it rewrites equalities it finds in the bodies of the two
sorts and forces irrelevant things.  So you're best if you disable the two
sort functions, as in the bsort case.  

We could, of course, make macros that just hide all these details.  In that
case it might be good to go the equisort2 route.
"
)
 (:PERMISSION
  "Sorting
 Copyright (C) 2001, Regents of the University of Texas
 Written by J Moore <moore@cs.utexas.edu>

 License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
"))
