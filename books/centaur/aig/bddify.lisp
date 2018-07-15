; Centaur AIG Library
; Copyright (C) 2008-2011 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

; This file contains the algorithm for converting an AIG into a BDD
; given a size limitation for the BDDs produced during this processs.

; In this file there are also a few notes that relate to a paper
; describing some aspects of this development.  We make a note of
; such with a comment that starts a line like the line just below:

;!PAPER-NOTE:

(in-package "ACL2")

(include-book "aig-base")
(include-book "faig-base")
(include-book "std/util/bstar" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(include-book "tools/include-raw" :dir :system)
(include-book "misc/hons-help2" :dir :system)
(include-book "centaur/ubdds/extra-operations" :dir :system)
(include-book "centaur/misc/memory-mgmt-logic" :dir :system)

(defxdoc bddify
  :parents (aig)
  :short "An verified algorithm for converting @(see aig)s into @(see ubdds)."

  :long "<p>The @('bddify') algorithm can convert AIGs into BDDs.  This can be
used, for instance, to solve satisfiability problems without reaching out to an
external SAT solver.</p>

<p>The algorithm uses two methods to simplify an input AIG using BDDs of
limited size; it repeatedly applies these methods while varying the BDD size
limit. One method is similar to dynamic weakening in that it replaces oversized
BDDs by a conservative approximation; the other method introduces fresh
variables to represent oversized BDDs.</p>

<p>While we have not documented the algorithm with @(see xdoc), a description
of its operation and verification can be found in:</p>

<box>
<p>Sol Swords and Warren A. Hunt, Jr.  <a
href='http://dx.doi.org/10.1007/978-3-642-14052-5_30'>A Mechanically Verified
AIG to BDD Conversion Algorithm</a>.  In ITP 2010.  Springer LNCS 6172, pages
435-449.</p>
</box>

<p><a
href='https://www.cs.utexas.edu/users/kaufmann/itp-2010/session6/swords-itp.pdf'>Slides</a>
from the ITP presentation are also available.</p>")


;; AIG-Q-COMPOSE builds a BDD from an AIG; each AIG variable must be
;; mapped to a BDD in the alist argument or it will be assigned the
;; value NIL.  Naive method: not to be used for real problems.

;!PAPER-NOTE:  this function called A2B.

(defn aig-q-compose (x fal)
  (aig-cases
   x
   :true t
   :false nil
   :var (aig-alist-lookup x fal)
   :inv (q-not (aig-q-compose (car x) fal))
   :and (let ((a (aig-q-compose (car x) fal)))
          (and a (q-and a (aig-q-compose (cdr x) fal))))))

(defn bdd-eval-alst (al vals)
  (if (atom al)
      nil
      (if (consp (car al))
          (cons (cons (caar al)
                      (eval-bdd (cdar al) vals))
                (bdd-eval-alst (cdr al) vals))
        (bdd-eval-alst (cdr al) vals))))

(defthm hons-assoc-equal-commutes-bdd-eval-alist-to-eval-bdd
    (equal (cdr (hons-assoc-equal x (bdd-eval-alst al vars)))
           (eval-bdd (cdr (hons-assoc-equal x al)) vars)))

(defthm bdd-eval-alst-hons-assoc-equal-iff
  (iff (hons-assoc-equal x (bdd-eval-alst al vals))
       (hons-assoc-equal x al)))

(defthm aig-q-compose-correct
    (equal (eval-bdd (aig-q-compose x al) vals)
           (aig-eval x (bdd-eval-alst al vals))))

(add-bdd-fn 'aig-q-compose)



(defn faig-q-compose-pat (pat fpat fal)
  (if pat
      (if (atom pat)
          (hons (aig-q-compose (ec-call (car fpat)) fal)
                (aig-q-compose (ec-call (cdr fpat)) fal))
        (cons (faig-q-compose-pat (car pat) (ec-call (car fpat)) fal)
              (faig-q-compose-pat (cdr pat) (ec-call (cdr fpat)) fal)))
    nil))

(defn faig-q-compose-list (lst fal)
  (if (atom lst)
      nil
    (cons (cons (aig-q-compose (ec-call (car (car lst))) fal)
                (aig-q-compose (ec-call (cdr (car lst))) fal))
          (faig-q-compose-list (cdr lst) fal))))

(defn aig-q-compose-list (lst fal)
  (if (atom lst)
      nil
    (cons (aig-q-compose (car lst) fal)
          (aig-q-compose-list (cdr lst) fal))))

(memoize 'aig-q-compose :condition '(consp x))

; COUNT-BDD-BRANCHES may be obsolete...

(defun count-bdd-branches (x n acc)
  (declare (xargs :guard (integerp n)
                  :verify-guards nil))
  (cond ((atom x)     (mv n acc))
        ((hons-get x acc)  (mv n acc))
        ((hqual (car x) (cdr x))
         (count-bdd-branches (car x) n (hut x t acc)))
        ((<= n 0)       (mv nil acc))
        (t (mv-let (n acc)
             (count-bdd-branches (cdr x) (1- n) (hut x t acc))
             (if n
                 (count-bdd-branches (car x) n acc)
               (mv n acc))))))


(defthm integerp-count-bdd-branches-0
  (implies (and (integerp n)
                (mv-nth 0 (count-bdd-branches x n acc)))
           (integerp (mv-nth 0 (count-bdd-branches x n acc)))))

(verify-guards count-bdd-branches)


(defn count-branches-to (x n)

; This has an under-the-hood definition (see the ttag below) to increase its
; performance.  It's only used heuristically, so even if it returns the wrong
; answer we're okay logically as far as the aig-bddify functions.  However, we
; of course need to trust that the under-the-hood definition doesn't mess up
; the memory somehow.

;!paper-note:  Specifically mentioned in the paper.

  (declare (xargs :guard-hints
                  (("goal"
                    :in-theory
                    (disable count-bdd-branches integerp-count-bdd-branches-0)
                    :use ((:instance integerp-count-bdd-branches-0
                                     (n (nfix n))
                                     (acc 'number-bdd-branches)))))))
  (mv-let (rem acc)
    (count-bdd-branches x (nfix n) 'number-bdd-branches)
    (ansfl (if rem (- (nfix n) rem) nil)
           acc)))

(defttag count-branches-to)
;; (depends-on "count-branches-fast.lsp")
(include-raw "count-branches-fast.lsp")
(defttag nil)

(defthm integerp-count-bdd-branches-to
  (implies (and (integerp n)
                (count-branches-to x n))
           (integerp (count-branches-to x n)))
  :hints (("goal"
           :in-theory
           (disable count-bdd-branches integerp-count-bdd-branches-0)
           :use ((:instance integerp-count-bdd-branches-0
                            (n (nfix n))
                            (acc 'number-bdd-branches))))))

(in-theory (disable count-branches-to))




;; Set this to NIL to disable warnings about missing bindings.
(defconst *aig-bddify-warn-missing-binding* t)




;; AIG-BDDIFY-X-WEAKENING tries to simplify an AIG and produce its BDD
;; representation given an alist mapping AIG variables to BDDs.  It uses a
;; weakening strategy that effectively replaces too-large BDDs by Xes (in our
;; implementation we use upper and lower bounds instead of onset and offset,
;; but the outcome is the same.) using BDDs and keeping track of upper
;; and lower bounds.  If the upper and lower bounds are equal, then this is the
;; exact BDD representation of the AIG.

;; Given HI and LO bdds from two subtrees, AND them together, simplifying in
;; the cases where one subtree is redundant.  Return the new HI and LO bdds,
;; the new simplified AIG, and upper bounds on the BDD sizes
;; (i.e. number-subtrees+1.)
(defn merge-hi-lo (hi1 hi2 lo1 lo2 a1 a2 hc1 hc2 lc1 lc2)
  (declare (xargs :guard (and (integerp hc1) (integerp hc2)
                              (integerp lc1) (integerp lc2))))
  ;; Concept!!!  Checking to see whether an AND is really equal to one
  ;; of the conjuncts.
  (cond ((hqual hi1 (q-and hi1 lo2))
         (mv hi1 lo1 a1 hc1 lc1))
        ((hqual hi2 (q-and hi2 lo1))
         (mv hi2 lo2 a2 hc2 lc2))
        (t (mv (q-and hi1 hi2)
               (q-and lo1 lo2)
               (aig-and a1 a2)
               (* hc1 hc2)
               (* lc1 lc2)))))

;; Compare a calculated upper bound on a BDD node count to a threshold.  If the
;; upper bound is greater, find the actual count using number-subtrees. If that
;; is okay, keep the BDD and return the new node count; otherwise, return a
;; default value, which should be a Boolean.
(defun prune-by-count (b cnt max-nodes default)
  ;; Checking a result BDD to see whether it's too large.
  (if (<= cnt max-nodes)
      (mv b cnt)
    (let* ((cnt (count-branches-to b max-nodes))
           (cnt (and cnt (1+ cnt))))
      (if (and cnt (<= cnt max-nodes))
          (mv b cnt)
        ;; Prune less aggressively?
        (mv default 1)))))

;; Given upper and lower bound BDDs, simplified AIGs, and node-count bounds for
;; each BDD of two subtrees, produce the same for the AND of the two subtrees.
(defun and-bddify-x-weakening (hi1 hi2 lo1 lo2 a1 a2 hc1 hc2 lc1 lc2 max-nodes)
  (b* (((mv hi lo a hc lc)
        (merge-hi-lo hi1 hi2 lo1 lo2 a1 a2 hc1 hc2 lc1 lc2)))
    (if (or (and (eq hi t) (eq lo t))
            (and (eq hi nil) (eq lo nil)))
        (mv hi hi hi 1 1)
      (b* (((mv hi hc)
            (prune-by-count hi hc max-nodes t))
           ((mv lo lc)
            (prune-by-count lo lc max-nodes nil)))
        (mv hi lo a hc lc)))))


(defun apqs-memo-lookup (x fmemo memo)
  (let ((m (hons-get x fmemo)))
    (if m
        (b* (((list* bdd a count) (cdr m)))
          (mv t bdd bdd a count count))
      (let ((m (hons-get x memo)))
        (if m
            (b* (((list* hi lo a hc lc) (cdr m)))
              (mv t hi lo a hc lc))
          (mv nil nil nil nil nil nil))))))

(defun apqs-memo-cache (x hi lo a hc lc fmemo memo)
  (if (hqual hi lo)
      (mv (hut x (list* hi a hc)
               (if (hons-get a fmemo)
                   fmemo
                 (hut a (list* hi a hc) fmemo)))
          memo)
    (mv fmemo (hut x (list* hi lo a hc lc) memo))))

(defun apqs-memo-lookup-aig (x fmemo memo)
  ;; for visibility -- map x to its new version in fmemo or memo
  (let ((m (hons-get x fmemo)))
    (if m
        (mv t (third m))
      (let ((m (hons-get x memo)))
        (if m
            (mv t (fourth m))
          (mv nil nil))))))

;!paper-note:  AIG-BDDIFY-X-WEAKENING is called BOUND-METHOD.

;; Six return values:
;; - an upper bound on the logical value of x under BDD substitution AL
;; - a lower bound
;; - a simplified version of x, which is equivalent to x under AL
;; - an upper bound on the size of the upper bound BDD
;; - a lower bound on the size of the lower bound BDD
;; - fmemo: final memoized results
;; - memo: memoized results for this max-nodes level
(defun aig-bddify-x-weakening (x al max-nodes fmemo memo)
  ;; Concept !!!
  ;; In this function, when we see a BDD that's too big, we replace it
  ;; by T (if it's an upper bound) or NIL (if it's a lower bound.)  So
  ;; we lose all in formation about that particular result.
  ;; The proof of correctness is in "aig-lemmas.lisp".
  (aig-cases
   x
   :true (mv t t t 1 1 fmemo memo)
   :false (mv nil nil nil 1 1 fmemo memo)
   :var (b* ((val (aig-alist-lookup x al))
             (count (count-branches-to val max-nodes))
             (count (and count (1+ count))))
          (if count
              (if (booleanp val)
                  (mv val val val count count fmemo memo)
                (mv val val x count count fmemo memo))
            (mv t nil x 1 1 fmemo memo)))
   :inv (b* (((mv hi lo a hc lc fmemo memo)
              (aig-bddify-x-weakening (car x) al max-nodes fmemo memo)))
          (mv (q-not lo) (q-not hi) (aig-not a) lc hc fmemo memo))
   :and (b* (((mv ok hi lo a hc lc)
              (apqs-memo-lookup x fmemo memo)))
          (if ok
              (mv hi lo a hc lc fmemo memo)
            (b* (((mv hi1 lo1 a1 hc1 lc1 fmemo memo)
                  (aig-bddify-x-weakening (car x) al max-nodes fmemo memo)))
              (if (and (eq hi1 nil) (eq lo1 nil))
                  (mv nil nil nil 1 1 fmemo memo)
                (b* (((mv hi2 lo2 a2 hc2 lc2 fmemo memo)
                      (aig-bddify-x-weakening (cdr x) al max-nodes fmemo memo))
                     ((mv hi lo a hc lc)
                      (and-bddify-x-weakening
                       hi1 hi2 lo1 lo2 a1 a2 hc1 hc2 lc1 lc2 max-nodes))
                     ((mv fmemo memo)
                      (apqs-memo-cache x hi lo a hc lc fmemo memo)))
                  (mv hi lo a hc lc fmemo memo))))))))


(defun aig-bddify-list-x-weakening (lst al max-nodes fmemo memo)
  (if (atom lst)
      (mv nil nil fmemo memo t)
    (b* (((mv hi lo a & & fmemo memo)
          (aig-bddify-x-weakening
           (car lst) al max-nodes fmemo memo))
         ((mv rbdds ras fmemo memo exact)
          (aig-bddify-list-x-weakening
           (cdr lst) al max-nodes fmemo memo)))
      (mv (cons hi rbdds)
          (cons a ras)
          fmemo memo
          (and (hqual hi lo) exact)))))


(defun apqs-memo-aig-map (map   ;; current map from original subtrees to previously normalized versions
                          fmemo ;; latest fmemo
                          memo  ;; latest memo
                          acc)

  ;; for visibility -- take the current mapping from original AIG subtrees to
  ;; rewritten ones, rewrite them further with the latest fmemo/memo.
  (b* (((when (atom map)) acc)
       ((when (atom (car map))) (apqs-memo-aig-map (cdr map) fmemo memo acc))
       ((cons key val) (car map))
       ((mv ok new-val) (apqs-memo-lookup-aig val fmemo memo))
       (new-val (if ok new-val val))
       (acc (cons (cons key new-val) acc)))
    (apqs-memo-aig-map (cdr map) fmemo memo acc)))


;; AIG-BDDIFY-VAR-WEAKENING tries to simplify an AIG and produce its BDD
;; representation given an alist mapping AIG variables to BDDs.  It uses a
;; weakening strategy that replaces too-large BDDs by fresh BDD variables.  If
;; the final BDD representation only uses variables that were in the original
;; alist, then this is the exact BDD representation for the AIG.

(defn aig-bddify-var-weakening-var (x al max-count)
  (b* ((val (aig-alist-lookup x al)))
    (if (booleanp val)
        (mv val val 1)
      (let* ((c (count-branches-to val max-count))
             (count (and c (1+ c))))
        (mv val x count)))))

(defun aig-bddify-var-weakening-cache-lookup (x fmemo memo)
  (let ((fmem (hons-get x fmemo)))
    (if fmem
        (mv t (cadr fmem) (caddr fmem) (cdddr fmem) t)
      (let ((mem (hons-get x memo)))
        (if mem
            (mv t (cadr mem) (caddr mem) (cdddr mem) nil)
          (mv nil nil nil nil nil))))))

(defun aig-bddify-var-weakening-lookup-aig (x fmemo memo)
  (let ((look (or (hons-get x fmemo)
                  (hons-get x memo))))
    (if look
        (mv t (third look))
      (mv nil nil))))

(defun aig-bddify-var-weakening-aig-map (map   ;; current map from original subtrees to previously normalized versions
                                         fmemo ;; latest fmemo
                                         memo  ;; latest memo
                                         acc)

  ;; for visibility -- take the current mapping from original AIG subtrees to
  ;; rewritten ones, rewrite them further with the latest fmemo/memo.
  (b* (((when (atom map)) acc)
       ((when (atom (car map))) (aig-bddify-var-weakening-aig-map (cdr map) fmemo memo acc))
       ((cons key val) (car map))
       ((mv ok new-val) (aig-bddify-var-weakening-lookup-aig val fmemo memo))
       (new-val (if ok new-val val))
       (acc (cons (cons key new-val) acc)))
    (aig-bddify-var-weakening-aig-map (cdr map) fmemo memo acc)))


(defun and-bddify-var-weakening (bdd1 aig1 count1 exact1 bdd2 aig2 count2 exact2
                                  max-count bdd-al nxtbdd)
  (b* ((bdd (q-and bdd1 bdd2))
       ((mv aig count exact)
        ;; Concept!!! Checking whether the AND can be replaced by one
        ;; of the conjuncts.
        (cond ((eq bdd nil)     (mv nil 1 t))
              ((hqual bdd bdd1) (mv aig1 count1 exact1))
              ((hqual bdd bdd2) (mv aig2 count2 exact2))
              (t (mv (aig-and aig1 aig2)
                     (and count1 count2 (* count1 count2))
                     (and exact1 exact2)))))
       ((mv bdd count bdd-al nxtbdd exact)
        (b* (((when (and count (<= count max-count)))
              (mv bdd count bdd-al nxtbdd exact))
             (c (count-branches-to bdd max-count))
             (count (and c (1+ c)))
            ;; Concept!!! Checking to see whether the result BDD is
            ;; too big and must be replaced by a variable.
             ((when (and count (<= count max-count)))
              (mv bdd count bdd-al nxtbdd exact))
             (b (hons-get bdd bdd-al))
             ((when b)
              (mv (cadr b) (cddr b) bdd-al nxtbdd nil))
             (n (count-branches-to nxtbdd max-count))
             (n (and n (1+ n))))
          (mv nxtbdd n
              (hut bdd (cons nxtbdd n) bdd-al)
              (hons nxtbdd nxtbdd)
              nil))))
    (mv bdd aig count bdd-al nxtbdd exact)))


(defn aig-bddify-var-weakening-cache-insert (exact x aig c-ans fmemo memo)
  (if exact
      (mv (hut x c-ans
               (if (hons-get aig fmemo)
                   fmemo
                 (hut aig c-ans fmemo)))
          memo)
    (mv fmemo (hut x c-ans memo))))


;!paper-note:  AIG-BDDIFY-VAR-WEAKENING is called SUBST-METHOD.

(defun aig-bddify-var-weakening (x al max-count fmemo memo bdd-al nxtbdd)
  ;; Concept!!! In this function, if we see an oversized BDD, we
  ;; replace it by a variable.  If this BDD has an entry in BDD-AL, it
  ;; already has a variable assigned to it and we use that.
  ;; Otherwise, we assign it a fresh variable.
  ;; The proof of correctness is in "aig-bddify-var-weakening-correct.lisp".
  (aig-cases
   x
   :true (mv x x 1 fmemo memo bdd-al nxtbdd t)
   :false (mv x x 1 fmemo memo bdd-al nxtbdd t)
   :var
   (mv-let (bdd aig count)
     (aig-bddify-var-weakening-var x al max-count)
     (mv bdd aig count fmemo memo bdd-al nxtbdd t))
   :inv
   (b* (((mv bdd aig count fmemo memo bdd-al nxtbdd exact)
         (aig-bddify-var-weakening
          (car x) al max-count fmemo memo bdd-al nxtbdd)))
     (mv (q-not bdd) (aig-not aig) count fmemo memo bdd-al nxtbdd
         exact))
   :and
   (mv-let (cached bdd aig count exact)
     (aig-bddify-var-weakening-cache-lookup x fmemo memo)
     (if cached
         (mv bdd aig count fmemo memo bdd-al nxtbdd exact)
       (b* (((mv bdd aig count fmemo memo bdd-al nxtbdd exact)
             (mv-let (bdd1 aig1 count1 fmemo memo bdd-al nxtbdd exact1)
               (aig-bddify-var-weakening
                (car x) al max-count fmemo memo bdd-al nxtbdd)
               (if (eq bdd1 nil)
                   (mv nil nil 1 fmemo memo bdd-al nxtbdd t)
                 (b* (((mv bdd2 aig2 count2 fmemo memo bdd-al nxtbdd exact2)
                       (aig-bddify-var-weakening
                        (cdr x) al max-count fmemo memo bdd-al nxtbdd))
                      ((mv bdd aig count bdd-al nxtbdd exact)
                       (and-bddify-var-weakening bdd1 aig1 count1 exact1 bdd2
                                                 aig2 count2 exact2 max-count
                                                 bdd-al nxtbdd)))
                   (mv bdd aig count fmemo memo bdd-al nxtbdd exact)))))
            (c-ans (list* bdd aig count))
            ((mv fmemo memo)
             (aig-bddify-var-weakening-cache-insert exact x aig
                                                    c-ans fmemo memo)))
         (mv bdd aig count fmemo memo bdd-al nxtbdd exact))))))


;; FMEMO contains "exact" entries and MEMO contains "inexact" ones, but some
;; exact entries may have slipped into MEMO since we don't check on the fly
;; whether the BDDs depend on new variables or not.  This looks through the AIG
;; and finds any MEMO entries that should be put in FMEMO instead.
(defun abs-recheck-exactness (x fmemo memo done var-depth)
  (aig-cases
   x
   :true (mv fmemo done)
   :false (mv fmemo done)
   :var (mv fmemo done)
   :inv (abs-recheck-exactness (car x) fmemo memo done var-depth)
   :and (if (hons-get x done)
            (mv fmemo done)
          (let ((done (hut x t done)))
            (if (hons-get x fmemo)
                (mv fmemo done)
              (let* ((mm (hons-get x memo)))
                ;; mm should be guaranteed to exist, but...
                (if (and mm (<= (max-depth (cadr mm)) var-depth))
                    (mv (hut (caddr mm) (cdr mm) fmemo) done)
                  (mv-let (fmemo done)
                    (abs-recheck-exactness
                     (car x) fmemo memo done var-depth)
                    (abs-recheck-exactness (cdr x) fmemo memo done
                                           var-depth)))))))))


(defun abs-recheck-exactness-top (x fmemo memo var-depth)
  (b* (((mv fmemo done)
        (abs-recheck-exactness x fmemo memo 'done var-depth))
       (- (flush-hons-get-hash-table-link done))
       (m (hons-get x fmemo)))
    (mv fmemo (consp m) (and (consp m) (cadr m)))))




(defun aig-bddify-list-var-weakening
  (lst al max-nodes fmemo memo bdd-al nxtbdd var-depth)
  (if (atom lst)
      (progn$ ;; (flush-hons-get-hash-table-link memo)
              (flush-hons-get-hash-table-link bdd-al)
              (mv nil nil fmemo memo t))
    (b* ((x (car lst))
         ((mv & aig1 & fmemo memo bdd-al1 nxtbdd1 &)
          (aig-bddify-var-weakening x al max-nodes fmemo memo
                                bdd-al nxtbdd))
         ((mv fmemo exact1 bdd1)
          (abs-recheck-exactness-top x fmemo memo
                                     var-depth))
         ((mv rbdds ras fmemo memo exact)
          (aig-bddify-list-var-weakening
           (cdr lst) al max-nodes fmemo memo bdd-al1 nxtbdd1 var-depth)))
      (mv (cons bdd1 rbdds)
          (cons aig1 ras)
          fmemo memo
          (and exact1 exact)))))




;; This attempts to simplify a list of AIGs and find their BDD representations
;; by interleaving the AIG-BDDIFY-X-WEAKENING and AIG-BDDIFY-VAR-WEAKENING
;; strategies as specified in TRIES.  Each entry in TRIES is a list of length
;; two, three, or four; the entries are:
;; 1. either of the symbols XES or VARS, giving the weakening strategy,
;; 2. a positive integer giving the BDD size threshold,
;; 3. (optional) a message to print before the try,
;; 4. (optional) a message to print when the try is completed.

(defun posfix (x)
  (if (and (integerp x) (< 0 x))
      x
    1))

(defthm posfix-type
  (posp (posfix x))
  :rule-classes (:rewrite :type-prescription))

(defthm posfix-linear
  (< 0 (posfix x))
  :rule-classes :linear)

(in-theory (disable posfix))

;!paper-note:  AIG-BDDIFY-LIST-ITER1 is called AIG-TO-BDD.

;; Set this to T to compute the AIG map at each iteration so that you can map
;; original AIG subtrees to their current simplified forms after extracting
;; things from the backtrace...
(defconst *aig-bddify-map-subtrees* nil)


(defun aig-bddify-list-iter1 (tries x al fmemo nxtbdd var-depth maybe-wash-args map)
  ;; map is just for visibility-debugging: maps subtrees of original AIG to
  ;; their most current crunched-down versions.
  (declare (xargs :measure (len tries))
           (ignorable maybe-wash-args))
  (if (atom tries)
      (prog2$ (flush-hons-get-hash-table-link fmemo)
              (mv nil x nil))
    (b* (((list type threshold start-msg end-msg) (car tries))
         (threshold (posfix threshold))
         (- (and start-msg (cw "~@0" start-msg)))
         (- (and maybe-wash-args
                 (if (consp maybe-wash-args)
                     (maybe-wash-memory (car maybe-wash-args)
                                        (cadr maybe-wash-args))
                   (maybe-wash-memory maybe-wash-args nil))))
         ((mv bdds x fmemo exact map)
          (cond ((eq type 'xes)
                 (b* (((mv bdds x fmemo memo exact)
                       (aig-bddify-list-x-weakening x al threshold fmemo 'memo))
                      (new-map (and *aig-bddify-map-subtrees*
                                    (apqs-memo-aig-map map fmemo memo nil))))
                   (fast-alist-free memo)
                   (mv bdds x fmemo exact new-map)))
                ((eq type 'vars)
                 (b* (((mv bdds x fmemo memo exact)
                       (aig-bddify-list-var-weakening x al threshold fmemo 'memo
                                                      'bdd-al nxtbdd var-depth))
                      (new-map (and *aig-bddify-map-subtrees*
                                    (aig-bddify-var-weakening-aig-map map fmemo memo nil))))
                   (fast-alist-free memo)
                   (mv bdds x fmemo exact new-map)))
                (t (prog2$ (er hard 'aig-bddify-list-iter1
                               "~x0: unrecognized strategy identifier~%"
                               type)
                           (mv nil x fmemo nil map)))))
         (- (and end-msg (cw "~@0" end-msg)))
         ((when (or exact (atom (cdr tries))))
          (prog2$ (flush-hons-get-hash-table-link fmemo)
                  (mv bdds x exact))))
      (aig-bddify-list-iter1 (cdr tries) x al fmemo nxtbdd var-depth
                             maybe-wash-args map))))


;; makes a fast, honsed alist consisting of the pairs of x whose cdrs are boolean
(defun bddify-extract-bool-alist (x full last)
  (declare (Xargs :guard t))
  (if (atom x)
      last
    (if (atom (car x))
        (bddify-extract-bool-alist (cdr x) full last)
      (let ((pair (hons-get (caar x) full)))
        (if (and pair (booleanp (cdr pair)))
            (hons-acons! (caar x) (cdr pair)
                         (bddify-extract-bool-alist (cdr x) full last))
          (bddify-extract-bool-alist (cdr x) full last))))))


;!paper-note:  AL-MAX-DEPTH is called TABLE-MAX-VAR.

(defn al-max-depth (al)
  (if (atom al)
      0
    (max (max-depth (ec-call (cdr (car al))))
         (al-max-depth (cdr al)))))

(defthm al-max-depth-hons-assoc-equal
  (implies (<= (al-max-depth al) n)
           (<= (max-depth (cdr (hons-assoc-equal x al))) n))
  :rule-classes (:rewrite :linear))

(defun aig-initial-self-map (x acc)
  (b* (((when (booleanp x)) acc)
       ((when (and (not (aig-atom-p x)) (not (cdr x))))
        (aig-initial-self-map (car x) acc))
       ((when (hons-get x acc)) acc)
       (acc (hons-acons x x acc))
       ((when (aig-atom-p x)) acc)
       (acc (aig-initial-self-map (car x) acc)))
    (aig-initial-self-map (cdr x) acc)))

(defun aiglist-initial-self-map (x acc)
  (if (atom x)
      acc
    (aiglist-initial-self-map (cdr x) (aig-initial-self-map (car x) acc))))
                    


(defun aig-bddify-list (tries x al maybe-wash-args)
  (b* ((var-depth (al-max-depth al))
       (bool-al (bddify-extract-bool-alist al al 'bddify-tmp-bool-alist))
       (x (hons-copy x))
       (reduced-x (if (consp bool-al)
                      (aig-restrict-list x bool-al)
                    x))
       (- (fast-alist-free bool-al))
       (init-map (and *aig-bddify-map-subtrees*
                      (fast-alist-free (aiglist-initial-self-map reduced-x nil)))))
    (aig-bddify-list-iter1 tries reduced-x al 'fmemo (qv var-depth)
                           var-depth maybe-wash-args init-map)))




(defun bddify-mk-old-style-tries (start-thresh incr times vars-thresh)
  (declare (xargs :measure (nfix times)
                  :ruler-extenders (cons)))
  (cons (list 'xes start-thresh
              (msg "Bddify with x-weakening, threshold ~x0 ..." start-thresh)
              " done~%")
        (if (<= (nfix times) 1)
            nil
          (let ((thresh (ceiling (* incr start-thresh) 1)))
            (append
             (if (<= vars-thresh thresh)
                 (list (list 'vars thresh
                             (msg "Bddify with var-weakening, threshold ~x0 ..."
                                  thresh)
                             " done~%"))
               nil)
             (bddify-mk-old-style-tries
              (ceiling (* incr thresh) 1)
              incr (1- times) vars-thresh))))))

(defconst *bddify-default-tries*
  (bddify-mk-old-style-tries 256 2 20 2048))

(table evisc-table *bddify-default-tries* "*bddify-default-tries*")




;; There are many variations such as FAIG-BDDIFY-LIST, AIG-BDDIFY-PAT,
;; FAIG-BDDIFY-PAT, FAIG-BDDIFY-ALIST, AIG-BDDIFY-ALIST, etc which we may want
;; to support.  Here we write a few functions for transitioning from/to these
;; formats to/from the simple list of AIGs which we support above.

(defun faig-list-to-aig-list (x)
  (if (atom x)
      nil
    (let ((x1 (faig-fix (car x))))
      (list* (car x1) (cdr x1)
             (faig-list-to-aig-list (cdr x))))))

(defun aig-list-to-faig-list (x)
  (if (atom x)
      nil
    (cons (cons (car x) (cadr x))
          (aig-list-to-faig-list (cddr x)))))



(defun pat-to-aig-list (pat x acc)
  (if pat
      (if (atom pat)
          (cons x acc)
        (pat-to-aig-list
         (car pat) (car x)
         (pat-to-aig-list
          (cdr pat) (cdr x) acc)))
    acc))

(defun aig-list-to-pat (pat x)
  (if pat
      (if (atom pat)
          (mv (car x) (cdr x))
        (mv-let (car rest)
          (aig-list-to-pat (car pat) x)
          (mv-let (cdr rest)
            (aig-list-to-pat (cdr pat) rest)
            (mv (cons car cdr) rest))))
    (mv nil x)))







(defn strip-pair-cars (al)
  (if (atom al)
      nil
    (if (consp (car al))
        (cons (caar al) (strip-pair-cars (cdr al)))
      (strip-pair-cars (cdr al)))))

(defn strip-pair-cdrs (al)
  (if (atom al)
      nil
    (if (consp (car al))
        (cons (cdar al) (strip-pair-cdrs (cdr al)))
      (strip-pair-cdrs (cdr al)))))



(defun def-with-bddify-fn (fn world)
  (let* ((formals (fgetprop fn 'formals nil world))
         (fn-symbol (intern-in-package-of-symbol
                     (concatenate 'string
                                  (symbol-name fn) "-WITH-BDDIFY")
                     fn))
         (thm-symbol (intern-in-package-of-symbol
                      (concatenate 'string
                                   (symbol-name fn) "-IN-TERMS-OF-WITH-BDDIFY")
                      fn)))
    `(progn
       (defun ,fn-symbol (,@formals tries mwa)
         (declare (ignore tries mwa))
         (,fn . ,formals))
       (defthm ,thm-symbol
         (equal (,fn . ,formals)
                (,fn-symbol ,@formals *bddify-default-tries* nil))
         :hints (("goal" :in-theory (disable ,fn)))
         :rule-classes nil))))


(defmacro def-with-bddify (fn)
  `(make-event (def-with-bddify-fn ',fn (w state))))

(def-with-bddify aig-eval)
(def-with-bddify faig-eval)
(def-with-bddify aig-eval-list)
(def-with-bddify aig-eval-alist)
(def-with-bddify faig-eval-list)
(def-with-bddify faig-eval-alist)



;; Now we apply these to various shapes of AIG-EVAL.
(local
 (progn
   (defthm faig-eval-list-to-aig-eval-list
     (equal (aig-list-to-faig-list
             (aig-eval-list-with-bddify
              (faig-list-to-aig-list pairs)
              al tries mwa))
            (faig-eval-list-with-bddify pairs al tries mwa)))

   (defthm aig-eval-alist-is-aig-eval-list
     (equal (pairlis$ (strip-pair-cars aig-al)
                      (aig-eval-list-with-bddify
                       (strip-pair-cdrs aig-al)
                       al tries mwa))
            (aig-eval-alist-with-bddify aig-al al tries mwa)))

   (defthm faig-eval-alist-is-faig-eval-list
     (equal (pairlis$ (strip-pair-cars aig-al)
                      (faig-eval-list-with-bddify
                       (strip-pair-cdrs aig-al)
                       al tries mwa))
            (faig-eval-alist-with-bddify aig-al al tries mwa)))

   (defthm aig-eval-is-aig-eval-list
     (equal (car (aig-eval-list-with-bddify (list x) al tries mwa))
            (aig-eval-with-bddify x al tries mwa)))

   (in-theory (disable aig-eval-with-bddify
                       aig-eval-list-with-bddify
                       aig-eval-alist-with-bddify
                       faig-eval-list-with-bddify
                       faig-eval-alist-with-bddify))))


;; These theorems will be used as alternative definitions for these functions
;; in symbolic execution.

(defthm faig-eval-in-terms-of-faig-eval-list
  (equal (faig-eval-with-bddify x al tries mwa)
         (car (faig-eval-list-with-bddify (list x) al tries mwa)))
  :hints(("Goal" :in-theory (enable faig-eval-list-with-bddify)))
  :rule-classes nil)

(defthm faig-eval-list-in-terms-of-aig-eval-list
  (equal (faig-eval-list-with-bddify x al tries mwa)
         (aig-list-to-faig-list
          (aig-eval-list-with-bddify
           (faig-list-to-aig-list x)
           al tries mwa)))
  :rule-classes nil)


(defthm faig-eval-list-in-terms-of-aig-eval-list-with-bddify
  (equal (faig-eval-list-with-bddify pairs al tries mwa)
         (aig-list-to-faig-list
          (aig-eval-list-with-bddify
           (faig-list-to-aig-list pairs)
           al tries mwa)))
  :rule-classes nil)



(defthm aig-eval-alist-in-terms-of-aig-eval-list
  (equal (aig-eval-alist-with-bddify aig-al al tries mwa)
         (pairlis$ (strip-pair-cars aig-al)
                   (aig-eval-list-with-bddify
                    (strip-pair-cdrs aig-al)
                    al tries mwa)))
  :rule-classes nil)

(defthm faig-eval-alist-in-terms-of-faig-eval-list
  (equal (faig-eval-alist-with-bddify aig-al al tries mwa)
         (pairlis$ (strip-pair-cars aig-al)
                   (faig-eval-list-with-bddify
                    (strip-pair-cdrs aig-al)
                    al tries mwa)))
  :rule-classes nil)

(defthm aig-eval-in-terms-of-aig-eval-list
  (equal (aig-eval-with-bddify x al tries mwa)
         (car (aig-eval-list-with-bddify (list x) al tries mwa)))
  :rule-classes nil)




(defun faig-bddify-list (tries x al maybe-wash-args)
  (mv-let (bdds aigs exact)
    (aig-bddify-list
     tries
     (faig-list-to-aig-list x) al maybe-wash-args)
    (mv (aig-list-to-faig-list bdds)
        (aig-list-to-faig-list aigs)
        exact)))


(defun aig-bddify-alist (tries x al maybe-wash-args)
  (b* (((mv bdds aigs exact)
        (aig-bddify-list
         tries
         (strip-pair-cdrs x)
         al maybe-wash-args))
       (cars (strip-pair-cars x)))
    (mv (pairlis$ cars bdds)
        (pairlis$ cars aigs)
        exact)))

(defun faig-bddify-alist (tries x al maybe-wash-args)
  (b* (((mv bdds aigs exact)
        (faig-bddify-list
         tries
         (strip-pair-cdrs x)
         al maybe-wash-args))
       (cars (strip-pair-cars x)))
    (mv (pairlis$ cars bdds)
        (pairlis$ cars aigs)
        exact)))

(defun aig-bddify (tries x al maybe-wash-args)
  (b* (((mv bdds aigs exact)
        (aig-bddify-list
         tries (list x) al maybe-wash-args)))
    (mv (car bdds) (car aigs) exact)))
