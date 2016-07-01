; Centaur AIG Library
; Copyright (C) 2012 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "std/util/define" :dir :system)
(include-book "std/basic/defs" :dir :system)
(include-book "std/osets/top" :dir :system)
(include-book "centaur/vl/util/cwtime" :dir :system)

(defsection best-aig
  :parents (aig-other)
  :short "Algorithms for choosing \"better\" (smaller) AIGs."

  :long "<p>Given two AIGs, A and B, we say that A is \"better\" than B if:</p>

<ul>
 <li>A has fewer unique AND nodes than B, or</li>
 <li>A,B have the same number of unique AND nodes, but A has fewer
       total nodes than B.</li>
</ul>

<p>We provide two main functions for choosing good AIGs:</p>

<ul>

<li>@(see aig-list-best) chooses the best AIG from a non-empty list of
AIGs.</li>

<li>@(see aig-list-list-best) is given a list of non-empty AIG Lists, say
@('(L1 L2 ... Ln)'), and returns @('(B1 B2 ... Bn)'), where each @('Bi') is the
best AIG from the corresponding @('Li').</li>

</ul>

<p>You could just implement @(see aig-list-list-best) as an ordinary \"map\" or
projection of @(see aig-list-best).  But @('aig-list-list-best') is written in
a slightly smarter way than this, so that it can share the labels and
memoization results across all of the AIGs in all of the lists.</p>

<h3>Implementation</h3>

<p>It is tricky to directly count \"unique nodes\" in a memoized way, but there
is a very easy way to do it indirectly.</p>

<p>First, we assign a number to every unique AIG node in sight, which (assuming
constant-time hashing) is linear in the sizes of the input AIGs.  We call these
numbers labels.</p>

<p>Next, we can write memoized functions to gather the sets of labels for all
of the AND nodes within an AIG, and similarly for all of the nodes.  We just
use regular ordered sets to represent these sets.  Importantly, these
collection functions can be easily memoized.</p>

<p>Finally, to count the number of ANDs (or all nodes) in an AIG, we just
collect the labels for its ANDs (or all nodes) and see how many labels were
found.</p>

<p>BOZO it would probably be much better to use @(see sbitsets) to represent
label sets.  If we ever need to speed this up, that's probably the first thing
to try.</p>")

(define aig-label-nodes
  :parents (best-aig)
  :short "Assign unique numbers (labels) to the nodes of an AIG."
  ((x    "A single AIG to traverse")
   (free "Smallest label that hasn't been assigned to any node, yet."
         natp)
   (map  "Fast alist from AIG nodes to labels (which we're constructing)."))
  :returns (mv (free "Updated free index" natp :rule-classes :type-prescription)
               (map  "Updated map."))
  :verify-guards nil
  (b* (((when (atom x))
        (mv (lnfix free) map))
       ((when (hons-get x map))
        (mv (lnfix free) map))
       ((mv free map) (aig-label-nodes (car x) free map))
       ((mv free map) (aig-label-nodes (cdr x) free map))
       (map           (hons-acons x free map))
       (free          (+ 1 free)))
    (mv free map))
  ///
  (verify-guards aig-label-nodes))

(define aig-list-label-nodes
  :parents (best-aig)
  :short "Extends @(see aig-label-nodes) to an AIG list."
  ((x "AIG list to traverse.")
   (free natp)
   map)
  :returns (mv (free natp :rule-classes :type-prescription)
               map)
  (b* (((when (atom x))
        (mv (nfix free) map))
       ((mv free map) (aig-label-nodes (car x) free map)))
    (aig-list-label-nodes (cdr x) free map)))

(define aig-list-list-label-nodes
  :parents (best-aig)
  :short "Extends @(see aig-label-nodes) to an AIG list list."
  ((x "AIG list list to traverse.")
   (free natp)
   map)
  :returns (mv (free natp :rule-classes :type-prescription)
               map)
  (b* (((when (atom x))
        (mv (nfix free) map))
       ((mv free map) (aig-list-label-nodes (car x) free map)))
    (aig-list-list-label-nodes (cdr x) free map)))



(define aig-collect-andnode-labels
  :parents (best-aig)
  :short "Collect the labels for AND nodes in an AIG.  (memoized)"
  ((x   "A single AIG")
   (map "Mapping of AIG nodes to labels."))
  :returns (label-set "Ordered set of labels for all AND nodes in X."
                      set::setp)
  (b* (((when (atom x))
        nil)
       ((unless (cdr x))
        (aig-collect-andnode-labels (car x) map))
       (x-label    (cdr (hons-get x map)))
       (car-labels (aig-collect-andnode-labels (car x) map))
       (cdr-labels (aig-collect-andnode-labels (cdr x) map)))
    (set::insert x-label (set::union car-labels cdr-labels)))
  ///
  (memoize 'aig-collect-andnode-labels :condition '(and (consp x) (cdr x))))

(define aig-count-andnode-labels
  :parents (best-aig)
  ((x   "A single AIG.")
   (map "Mapping of AIG nodes to labels."))
  :returns (count natp :rule-classes :type-prescription)
  (set::cardinality (aig-collect-andnode-labels x map)))


(define aig-collect-labels
  :parents (best-aig)
  :short "Collect the labels of ALL nodes in an AIG.  (memoized)"
  ((x   "A single AIG")
   (map "Mapping of AIG nodes to labels."))
  :returns (label-set "Ordered set of labels for all nodes in X."
                      set::setp)
  (b* (((when (atom x))
        nil)
       (x-label    (cdr (hons-get x map)))
       (car-labels (aig-collect-labels (car x) map))
       (cdr-labels (aig-collect-labels (cdr x) map)))
    (set::insert x-label
                  (set::union car-labels cdr-labels)))
  ///
  (memoize 'aig-collect-labels :condition '(and (consp x) (cdr x))))

(define aig-count-labels
  :parents (best-aig)
  ((x   "A single AIG.")
   (map "Mapping of AIG nodes to labels."))
  :returns (count natp :rule-classes :type-prescription)
  (set::cardinality (aig-collect-labels x map)))



(define aig-list-best-aux1
  :parents (best-aig)
  :short "Main loop for finding the best AIG."
  ((x         "An AIG list.")
   (best      "Best AIG we've seen so far.")
   (best-ands "How many unique AND nodes in our best AIG so far."
              natp)
   (map       "Mapping of AIG nodes to labels."))
  :returns
  (new-best "Best AIG in X, or @('best') it's better than everything in X.")
  (b* (((when (atom x))
        best)
       (ands (aig-count-andnode-labels (car x) map))
       ((when (or (< ands best-ands)
                  (and (= best-ands ands)
                       (< (aig-count-labels (car x) map)
                          (aig-count-labels best map)))))
        ;; The car is better than best.
        (aig-list-best-aux1 (cdr x) (car x) ands map)))
    ;; Best is better than the car.
    (aig-list-best-aux1 (cdr x) best best-ands map)))

(define aig-list-best-aux
  :parents (best-aig)
  ((x   "A non-empty list of AIGs.")
   (map "Mapping of AIG nodes to labels."))
  :returns (best "Best AIG in X.")
  (if (atom x)
      ;; BOZO this is kind of a lousy thing to do.
      (raise "Expected at least one aig.")
    (aig-list-best-aux1 (cdr x)
                        (car x)
                        (aig-count-andnode-labels (car x) map)
                        map)))

(define aig-list-list-best-aux
  :parents (best-aig)
  ((x   "An AIG List List.  Shouldn't contain any empty lists.")
   (map "Mapping of AIG nodes to labels."))
  :returns
  (best-list "A list containing the best AIG from each list in @('x').")
  (if (atom x)
      nil
    (cons (aig-list-best-aux (car x) map)
          (aig-list-list-best-aux (cdr x) map))))

(define aig-list-best
  :parents (best-aig)
  :short "Top level function for choosing the best AIG out of a list."
  ((x "An AIG List, which should be non-empty."))
  :returns (best "The best AIG in @('x').")
  :long "<p>This is easy to use: it handles all of the details of freeing the
         fast alists and memo tables it uses.</p>"
  (b* (((mv ?free map) (cwtime (aig-list-label-nodes x 0 nil)
                               :mintime 1/2))
       (ret (cwtime (aig-list-best-aux x map)
                    :mintime 1/2)))
    (fast-alist-free map)
    (clear-memoize-table 'aig-collect-andnode-labels)
    (clear-memoize-table 'aig-collect-labels)
    ret))

(define aig-list-list-best
  :parents (best-aig)
  :short "Top-level function for choosing the best AIGs from a list of AIG
          lists."
  ((x "An AIG List List, say @('(L1 L2 ... Ln)').  These should each be
       non-empty."))
  :returns (best "An AIG List, say @('(B1 B2 ... Bn)'), where each @('Bi') is
                  the best AIG from the corresponding @('Li').")
  :long "<p>This is easy to use: it handles all of the details of freeing the
         fast alists and memo tables it uses.</p>"
  (b* (((mv ?free map) (cwtime (aig-list-list-label-nodes x 0 nil)
                               :mintime 1))
       (ret (cwtime (aig-list-list-best-aux x map)
                    :mintime 1)))
    (fast-alist-free map)
    (clear-memoize-table 'aig-collect-andnode-labels)
    (clear-memoize-table 'aig-collect-labels)
    ret))
