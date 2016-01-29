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
; AIG <--> AIGER file conversion
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "aiger-help")
(include-book "aig-vars-ext")
(include-book "centaur/vl/util/cwtime" :dir :system)
(include-book "centaur/misc/sneaky-load" :dir :system)
(include-book "centaur/misc/numlist" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "misc/definline" :dir :system)
(include-book "arithmetic/nat-listp" :dir :system)
(local (include-book "data-structures/list-defthms" :dir :system))
(local (include-book "clause-processors/instantiate" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/alists/top" :dir :system))

(local (in-theory (disable reverse-removal revappend-removal)))

(local (defthm maybe-byte-p-bound-rw
         (implies (and (maybe-byte-p x) x)
                  (< x 256))
         :rule-classes :rewrite
         :hints(("Goal" :in-theory (enable maybe-byte-p)))))

(defun aiger-gate-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (consp (car x))
         (consp (cdar x))
         (b* (((cons lhs (cons rhs1 rhs2)) (car x)))
           (and (natp lhs)
                (natp rhs1)
                (natp rhs2)
                (< rhs1 lhs)
                (<= rhs2 rhs1)))
         (aiger-gate-listp (cdr x)))))

;; Analysis for writing AIGER files.  This breaks down some ACL2 AIGs into a
;; form where they may be written out straightforwardly.

;; Names maps AIG nodes to AIGER literals (even naturals.)
;; Names should already contain all the variables.
;; Maxvar is 1/2 the highest used literal.
(defun aig-to-aiger (aig names maxvar gates)
  (declare (xargs :guard (natp maxvar)
                  :verify-guards nil))
  (let ((lookup (hons-get aig names)))
    (if lookup
        (mv (nfix (cdr lookup)) names maxvar gates)
      (aig-cases
       aig
       :true (mv 1 names maxvar gates)
       :false (mv 0 names maxvar gates)
       :var (let* ((maxvar (1+ (lnfix maxvar)))
                   (lit (ash maxvar 1)))
              (mv lit
                  (hons-acons aig lit names)
                  maxvar
                  gates))
       :inv (mv-let (lit names maxvar gates)
              (aig-to-aiger (car aig) names maxvar gates)
              (mv (logxor 1 lit)
                  names maxvar gates))
       :and (mv-let (left names maxvar gates)
              (aig-to-aiger (car aig) names maxvar gates)
              (mv-let (right names maxvar gates)
                (aig-to-aiger (cdr aig) names maxvar gates)
                (let* ((maxvar (1+ (lnfix maxvar)))
                       (lit (ash maxvar 1)))
                  (mv lit
                      (hons-acons aig lit names)
                      maxvar
                      (cons
                       (if (<= left right)
                           (list* lit right left)
                         (list* lit left right))
                       gates)))))))))

(defun names-max-entry (names)
  (if (atom names)
      0
    (if (consp (car names))
        (max (names-max-entry (cdr names))
             (nfix (cdar names)))
      (names-max-entry (cdr names)))))

(local (defthm lookup-when-names-max-entry
         (implies (< (names-max-entry names) maxlit)
                  (and (< (nfix (cdr (hons-assoc-equal x names))) maxlit)
                       (implies (natp (cdr (hons-assoc-equal x names)))
                                (< (cdr (hons-assoc-equal x names)) maxlit))))
         :rule-classes :linear))


(defthm aig-to-aiger-natp-maxvar
  (implies (natp maxvar)
           (natp (mv-nth 2 (aig-to-aiger aig names maxvar gates))))
  :rule-classes :type-prescription)

(defthm aig-to-aiger-true-listp-gates
  (equal (true-listp (mv-nth 3 (aig-to-aiger aig names maxvar gates)))
         (true-listp gates))
  :hints(("Goal" :in-theory (disable binary-logxor ash))))

(defthm natp-aig-to-aiger-lit
  (natp (mv-nth 0 (aig-to-aiger aig names maxvar gates)))
  :rule-classes :type-prescription)

(local (defthm ash-1-is-*-2
         (implies (integerp n)
                  (equal (ash n 1)
                         (* 2 n)))
         :hints(("Goal" :in-theory (enable ash** logcons)))))

(local (defthm logxor-1-bound
         (implies (and (< n (+ 2 (* 2 m)))
                       (natp n) (natp m))
                  (< (logxor 1 n) (+ 2 (* 2 m))))
         :hints(("Goal" :in-theory (enable logxor** logcons)))))

(defthm names-max-entry-of-aig-to-aiger
  (implies (and (natp maxvar)
                (< (names-max-entry names) (+ 2 (* 2 maxvar))))
           (b* (((mv lit names maxvar &)
                 (aig-to-aiger x names maxvar gates)))
             (and (< lit (+ 2 (* 2 maxvar)))
                  (< (names-max-entry names) (+ 2 (* 2 maxvar))))))
  :hints (("goal" :induct (aig-to-aiger x names maxvar gates)
           :in-theory (enable ash)))
  :rule-classes (:rewrite :linear))

(defthm aig-to-aiger-maxvar-incr
  (implies (natp maxvar)
           (<= maxvar (mv-nth 2 (aig-to-aiger aig names maxvar gates))))
  :rule-classes :linear)

(defthm aiger-gates-p-aig-to-aiger
  (implies (and (aiger-gate-listp gates)
                (natp maxvar)
                (< (names-max-entry names) (+ 2 (* 2 maxvar))))
           (aiger-gate-listp (mv-nth 3 (aig-to-aiger aig names maxvar gates)))))

(verify-guards aig-to-aiger)

(in-theory (disable aig-to-aiger))

(defun aig-to-aiger-top (aig)
  (declare (Xargs :guard t))
  (b* ((vars (aig-vars-1pass aig))
       (maxvar (len vars))
       (names1 (pairlis$ vars (numlist 2 2 maxvar)))
       ((with-fast names1))
       ((mv outlit names maxvar gates)
        (aig-to-aiger aig names1 maxvar nil)))
    (fast-alist-free names)
    (mv outlit names1 maxvar gates)))

(defun names-numlist-ind (start by vars n)
  (if (atom vars)
      n
    (cons start (names-numlist-ind (+ start by) by (cdr vars) (1- n)))))

(defthm names-max-entry-pairlis-numlist
  (implies (and (posp start) (posp by)
                (equal n (len vars)))
           (< (names-max-entry (pairlis$ vars (numlist start by n)))
              (+ start (* by (len vars)))))
  :hints(("Goal" :in-theory (enable numlist pairlis$)
          :induct (names-numlist-ind start by vars n)
          :expand ((:free (y) (pairlis$ vars y))
                   (:free (l) (numlist start by l)))))
  :rule-classes :linear)

(defthm aiger-gates-p-aig-to-aiger-top
  (aiger-gate-listp (mv-nth 3 (aig-to-aiger-top aig))))

(defun aig-list-to-aiger-tr (aigs names maxvar outs gates)
  (declare (xargs :guard (and (natp maxvar) (true-listp outs))))
  (if (atom aigs)
      (mv names maxvar (reverse outs) gates)
    (mv-let (lit names maxvar gates)
      (aig-to-aiger (car aigs) names maxvar gates)
      (aig-list-to-aiger-tr (cdr aigs) names maxvar (cons lit outs) gates))))

(defun aig-list-to-aiger (aigs names maxvar gates)
  (declare (xargs :guard (natp maxvar)
                  :verify-guards nil))
  (mbe :logic (if (atom aigs)
                  (mv names maxvar nil gates)
                (mv-let (lit names maxvar gates)
                  (aig-to-aiger (car aigs) names maxvar gates)
                  (mv-let (names maxvar outs gates)
                    (aig-list-to-aiger (cdr aigs) names maxvar gates)
                    (mv names maxvar (cons lit outs) gates))))
       :exec (aig-list-to-aiger-tr aigs names maxvar nil gates)))

(defthm aig-list-to-aiger-tr-rw
  (implies (true-listp outs)
           (equal (aig-list-to-aiger-tr aigs names maxvar outs gates)
                  (mv-let
                    (names maxvar outs1 gates)
                    (aig-list-to-aiger aigs names maxvar gates)
                    (mv names maxvar (revappend outs outs1) gates))))
  :hints(("Goal" :in-theory (enable revappend))))

(verify-guards aig-list-to-aiger
  :hints(("Goal" :in-theory (enable revappend))))

(defthm names-max-entry-of-aig-list-to-aiger
  (implies (and (natp maxvar)
                (< (names-max-entry names) (+ 2 (* 2 maxvar))))
           (b* (((mv names maxvar & &)
                 (aig-list-to-aiger x names maxvar gates)))
             (< (names-max-entry names) (+ 2 (* 2 maxvar)))))
  :hints (("goal" :induct (aig-list-to-aiger x names maxvar gates)))
  :rule-classes (:rewrite :linear))

(defthm aiger-gates-p-aig-list-to-aiger
  (implies (and (aiger-gate-listp gates)
                (natp maxvar)
                (< (names-max-entry names) (+ 2 (* 2 maxvar))))
           (aiger-gate-listp (mv-nth 3 (aig-list-to-aiger aigs names maxvar gates)))))

(defthm nat-listp-aig-list-to-aiger-lits
  (nat-listp (mv-nth 2 (aig-list-to-aiger aigs names maxvar gates))))


(defthm aig-list-to-aiger-natp-maxvar
  (implies (natp maxvar)
           (natp (mv-nth 1 (aig-list-to-aiger aigs names maxvar gates))))
  :rule-classes :type-prescription)

(defthm aig-list-to-aiger-len-outs
  (equal (len (mv-nth 2 (aig-list-to-aiger aigs names maxvar gates)))
         (len aigs)))


(defthm aig-list-to-aiger-true-listp-outs
  (true-listp (mv-nth 2 (aig-list-to-aiger aigs names maxvar gates))))

(defthm aig-list-to-aiger-true-listp-gates
  (equal (true-listp (mv-nth 3 (aig-list-to-aiger aigs names maxvar gates)))
         (true-listp gates)))




(defun aig-list-to-aiger-top (aigs)
  (declare (Xargs :guard t))
  (b* ((vars (aig-vars-1pass aigs))
       (maxvar (len vars))
       (names1 (pairlis$ vars (numlist 2 2 maxvar)))
       ((with-fast names1))
       ((mv names maxvar outlits gates)
        (aig-list-to-aiger aigs names1 maxvar nil)))
    (fast-alist-free names)
    (mv outlits names1 maxvar gates)))

(defthm aig-list-to-aiger-top-true-listp-outs
  (true-listp (mv-nth 0 (aig-list-to-aiger-top aigs))))

(defthm aig-list-to-aiger-top-nat-listp-outs
  (nat-listp (mv-nth 0 (aig-list-to-aiger-top aigs))))

(defthm len-aig-list-to-aiger-top-outs
  (equal (len (mv-nth 0 (aig-list-to-aiger-top aigs)))
         (len aigs)))

(defthm natp-aig-list-to-aiger-top-maxvar
  (natp (mv-nth 2 (aig-list-to-aiger-top aigs))))

(defthm aiger-gate-listp-aig-list-to-aiger-top
  (aiger-gate-listp (mv-nth 3 (aig-list-to-aiger-top aigs))))


(defun aiger-list-inputs (max)
  (declare (xargs :guard (natp max)))
  (numlist (* 2 max) -2 max))


;; Takes an alist mapping arbitrary positive AIGs to literals, filters out the
;; non-variable mappings, switches its orientation, and makes it fast.
(defun aiger-reverse-map-names (names)
  (declare (xargs :guard t))
  (if (atom names)
      nil
    (if (and (consp (car names))
             (atom (caar names))) ;; variable
        (hons-acons (cdar names) (caar names)
                    (aiger-reverse-map-names (cdr names)))
      (aiger-reverse-map-names (cdr names)))))

(defun filter-out-alist-keys (lst al)
  (declare (xargs :guard t))
  (if (atom lst)
      nil
    (if (hons-get (car lst) al)
        (filter-out-alist-keys (cdr lst) al)
      (cons (car lst) (filter-out-alist-keys (cdr lst) al)))))

(defun aigs-to-aiger (latch-aigs out-aigs badstate-aigs constraint-aigs)
  (declare (xargs :guard (and (alistp latch-aigs)
                              (true-listp out-aigs)
                              (true-listp badstate-aigs)
                              (true-listp constraint-aigs))))
  "AIGS-TO-AIGER analyzes an AIG network and produces the information necessary
to write them in AIGER format.  It takes four inputs:
LATCH-AIGs - a fast alist mapping names of state elements to their next-state
             AIGs.  This should not contain any shadowed pairs.
OUT-AIGS, BADSTATE-AIGS, CONSTRAINT-AIGS
           - each a list of AIGs giving the formulas of (respectively)
             the primary outputs, (inverted) safety properties, and
             constraints

It produces seven results:
PIs        - the list of primary inputs; that is, the variables used in the
             AIGs excluding those that are named as latches, giving the order
             in which they are indexed
LATCHES    - a list containing the indices corresponding to the latch inputs,
             or next-states
OUTPUTS    - a list containing the indices corresponding to the outputs
BADSTATES  -    ''               ''                             bad states
CNSTRAINTS -    ''               ''                             constraints
GATES      - A list of entries of the form (OUT IN1 . IN2) where OUT is an even
             natural number, IN1 and IN2 are natural numbers, and OUT > IN1 >=
             IN2. This signifies that OUT is defined as the AND of IN1 and IN2,
             where each of the INs, if odd, represents a negation of the node
             corresponding to the next lower even number.



The necessary information to write an AIGER file consists of (LENGTH INS),
OUTS, and GATES.
"
  (b* ((latch-aig-list (strip-cdrs latch-aigs))
       (latch-names (strip-cars latch-aigs))
       (all-aigs (append latch-aig-list out-aigs badstate-aigs constraint-aigs))
       (vars (cwtime (aig-vars-1pass all-aigs)
                     :name aig-vars-1pass
                     :mintime 1))
       (pis (filter-out-alist-keys vars latch-aigs))
       (ins (length pis))
       (names (hons-shrink-alist
               (pairlis$ pis (numlist 2 2 ins))
               (expt 2 20)))
       (latches (len latch-aigs))
       (maxvar (+ ins latches))
       (names (hons-shrink-alist
               (pairlis$ latch-names
                         (numlist (+ 2 (* 2 ins)) 2 latches))
               names))
       ((mv names maxvar latch-lits gates)
        (aig-list-to-aiger latch-aig-list names maxvar nil))
       ((mv names maxvar out-lits gates)
        (aig-list-to-aiger out-aigs names maxvar gates))
       ((mv names maxvar badstate-lits gates)
        (aig-list-to-aiger badstate-aigs names maxvar gates))
       ((mv names & constraint-lits gates)
        (aig-list-to-aiger constraint-aigs names maxvar gates))
       (- (flush-hons-get-hash-table-link names)))
    (mv pis latch-lits out-lits badstate-lits constraint-lits (reverse
                                                               gates))))

(defthm aiger-gate-listp-revappend
  (implies (and (aiger-gate-listp x)
                (aiger-gate-listp y))
           (aiger-gate-listp (revappend x y)))
  :hints(("Goal" :in-theory (enable revappend))))

(defthm aiger-gate-listp-append
  (implies (and (aiger-gate-listp x)
                (aiger-gate-listp y))
           (aiger-gate-listp (append x y)))
  :hints(("Goal" :in-theory (enable append))))

(defthm aiger-gate-listp-rev
  (implies (aiger-gate-listp x)
           (aiger-gate-listp (rev x)))
  :hints(("Goal" :in-theory (enable rev))))

(local (defthm aiger-gate-listp-implies-true-listp
         (implies (aiger-gate-listp x)
                  (true-listp x))))

(local (defthm true-listp-implies-not-stringp
         (implies (true-listp x)
                  (not (stringp x)))))

(local (in-theory (disable aig-vars
                           filter-out-alist-keys
                           numlist
                           hons-shrink-alist
                           append)))

(defthm names-max-entry-of-hons-shrink-alist
  (<= (names-max-entry (hons-shrink-alist a b))
      (max (names-max-entry a) (names-max-entry b)))
  :hints(("Goal" :in-theory (enable hons-shrink-alist)))
  :rule-classes
  ((:linear :trigger-terms ((names-max-entry (hons-shrink-alist a b))))))

;; (defthm aiger-gate-listp-of-nest
;;   (implies (and (aiger-gate-listp gates)
;;                 (natp maxvar)
;;                 (< (names-max-entry names) (+ 2 (* 2 maxvar))))
;;            (b* (((mv names maxvar ?lits gates)
;;                  (aig-list-to-aiger aigs1 names maxvar gates))
;;                 ((mv names maxvar ?lits gates)
;;                  (aig-list-to-aiger aigs2 names maxvar gates))
;;                 ((mv names maxvar ?lits gates)
;;                  (aig-list-to-aiger aigs3 names maxvar gates))
;;                 ((mv ?names ?maxvar ?lits gates)
;;                  (aig-list-to-aiger aigs4 names maxvar gates)))
;;              (aiger-gate-listp gates)))
;;   :hints(("Goal" :in-theory (disable aig-list-to-aiger
;;                                      names-max-entry
;;                                      aiger-gate-listp))))

(defthm aiger-gate-listp-of-aigs-to-aiger
  (aiger-gate-listp (mv-nth 5 (aigs-to-aiger latch-aigs out-aigs badstate-aigs
                                             constraint-aigs)))
  :hints (("goal" :in-theory (disable len pairlis$ aig-list-to-aiger
                                      strip-cdrs strip-cars
                                      aiger-gate-listp
                                      names-max-entry))
          (and stable-under-simplificationp
               (instantiate-thm-for-matching-terms
                names-max-entry-of-hons-shrink-alist
                ((a a) (b b))
                (hons-shrink-alist a b)))))

(defthm nat-listp-of-aigs-to-aiger
  (b* (((mv & latchlits outlits badlits constrlits &)
        (aigs-to-aiger latch-aigs out-aigs badstate-aigs constraint-aigs)))
    (and (nat-listp latchlits)
         (nat-listp outlits)
         (nat-listp badlits)
         (nat-listp constrlits)))
  :hints (("goal" :in-theory (disable len pairlis$ aig-list-to-aiger
                                      strip-cdrs strip-cars
                                      aiger-gate-listp
                                      names-max-entry))))

(defthm true-listp-of-aigs-to-aiger
  (b* (((mv pis latchlits outlits badlits constrlits &)
        (aigs-to-aiger latch-aigs out-aigs badstate-aigs constraint-aigs)))
    (and (true-listp pis)
         (true-listp latchlits)
         (true-listp outlits)
         (true-listp badlits)
         (true-listp constrlits)))
  :hints (("goal" :in-theory (disable len pairlis$ aig-list-to-aiger
                                      strip-cdrs strip-cars
                                      aiger-gate-listp
                                      names-max-entry))))
;; Analysis for reading AIGER files.



(defun aiger-gates-to-aig-map (gates map)
  (declare (xargs :guard t))
  (if (atom gates)
      map
    (b* (((when (or (atom (car gates))
                    (atom (cdar gates))
                    (not (natp (caar gates)))
                    (not (evenp (caar gates)))
                    (not (natp (cadar gates)))
                    (not (natp (cddar gates)))))
          (er hard? 'aiger-gates-to-aig-map "Warning: ill-formed gate: ~x0~%" (car gates))
          (aiger-gates-to-aig-map (cdr gates) map))
         (out (caar gates))
         (in1 (cadar gates))
         (in2 (cddar gates))
         (negatedp1 (logbitp 0 in1))
         (abs1      (logand in1 -2))
         (negatedp2 (logbitp 0 in2))
         (abs2      (logand in2 -2))
         (look1     (if (eql 0 abs1)
                        (list abs1)
                      (hons-get abs1 map)))
         ((run-when (not look1))
          (cw "Warning: no definition of AIGER literal ~x0 before use~%" abs1))
         (look2     (if (eql 0 abs2)
                        (list abs2)
                      (hons-get abs2 map)))
         ((run-when (not look2))
          (cw "Warning: no definition of AIGER literal ~x0 before use~%" abs2))
         (aig1 (if negatedp1 (aig-not (cdr look1)) (cdr look1)))
         (aig2 (if negatedp2 (aig-not (cdr look2)) (cdr look2)))
         (map (hons-acons out (aig-and aig1 aig2) map)))
      (aiger-gates-to-aig-map (cdr gates) map))))



(defun aiger-get-lits-tr (lits map acc)
  (declare (xargs :guard (and (integer-listp lits)
                              (true-listp acc))))
  (if (atom lits)
      (reverse acc)
    (b* ((lit (car lits))
         (negatedp (logbitp 0 lit))
         (abs      (logand lit -2))
         (look (if (eql abs 0)
                   ;; special case: 0 = false
                   (list abs)
                 (hons-get abs map)))
         ((run-when (not look))
          (cw "Warning: no definition of AIGER literal ~x0~%" abs))
         (aig (if negatedp (aig-not (cdr look)) (cdr look))))
      (aiger-get-lits-tr (cdr lits) map (cons aig acc)))))

(defun aiger-get-lits (lits map)
  (declare (xargs :guard (integer-listp lits)
                  :verify-guards nil))
  (mbe :logic
       (if (atom lits)
           nil
         (b* ((lit (car lits))
              (negatedp (logbitp 0 lit))
              (abs      (logand lit -2))
              (look (if (eql abs 0)
                        ;; special case: 0 = false
                        (list abs)
                      (hons-get abs map)))
              ((run-when (not look))
               (cw "Warning: no definition of AIGER literal ~x0~%" abs))
              (aig (if negatedp (aig-not (cdr look)) (cdr look))))
           (cons aig (aiger-get-lits (cdr lits) map))))
       :exec (aiger-get-lits-tr lits map nil)))

(defthm aiger-get-lits-tr-rw
  (implies (not (stringp acc))
           (equal (aiger-get-lits-tr list map acc)
                  (revappend acc (aiger-get-lits list map))))
  :hints(("Goal" :in-theory (enable revappend))))

(verify-guards aiger-get-lits
  :hints(("Goal" :in-theory (enable revappend))))




(defun aiger-to-aigs (innames latchnames latches outs badstates constraints gates)
  (declare (xargs :guard (and (true-listp innames)
                              (true-listp latchnames)
                              (integer-listp outs)
                              (integer-listp badstates)
                              (integer-listp constraints)
                              (integer-listp latches))))
  "AIGER-TO-AIGS: Inputs:
inNAMES   - list of names to be given to AIGER PIs in order
LATCHNAMES - list of names to be given to AIGER latches in order
LATCHES - list of AIGER literals giving the latches
OUTS    - list of AIGER literals giving the primary outputs
BADS    - list of AIGER literals giving the bad states
CNSTRS  - list of AIGER literals giving the constraints
GATES   - list of gate entries, as above.
Returns
LATCH-AIGS - alist mapping latch names to AIG next-state functions
OUT-AIGS   - list of primary output AIGs
BAD-AIGS   - list of bad-state AIGs
CNSTR-AIGS - list of constraint AIGs. "

  (b* ((names (hons-shrink-alist
               (append (pairlis$ (numlist 2 2 (length innames))
                                 innames)
                       (pairlis$ (numlist (+ 2 (* 2 (length innames)))
                                          2 (length latchnames))
                                 latchnames))
               nil))
       (names (aiger-gates-to-aig-map gates names))
       (out-aigs (aiger-get-lits outs names))
       (bad-aigs (aiger-get-lits badstates names))
       (cnstr-aigs (aiger-get-lits constraints names))
       (latch-aigs (pairlis$ latchnames
                             (aiger-get-lits latches names)))
       (- (flush-hons-get-hash-table-link names)))
    (mv latch-aigs out-aigs bad-aigs cnstr-aigs)))





;; Writing AIGER files.


(defun aiger-write-gates (gates prev stream state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-output-channel-p stream :byte state)
                              (aiger-gate-listp gates)
                              (natp prev))))
  (if (atom gates)
      state
    (b* (((when (or (atom (car gates))
                    (atom (cdar gates))))
          (cw "Warning: Malformed gate: ~x0~%" gates)
          (aiger-write-gates (cdr gates) prev stream state))
         ((cons lhs (cons rhs1 rhs2)) (car gates))
         ((when (not (and (eql (+ 2 prev) lhs)
                          (< rhs1 lhs)
                          (<= rhs2 rhs1))))
          (cw "Warning: Bad ordering on gate.
               prev: ~x0 lhs: ~x1 rhs1: ~x2 rhs2: ~x3~%"
              prev lhs rhs1 rhs2)
          (aiger-write-gates (cdr gates) prev stream state))
         (state (aiger-write-delta (- lhs rhs1) stream state))
         (state (aiger-write-delta (- rhs1 rhs2) stream state))
         (prev lhs))
      (aiger-write-gates (cdr gates) prev stream state))))

(defthm open-output-channel-p1-of-aiger-write-gates
  (implies (and (state-p1 state)
                (symbolp stream)
                (open-output-channel-p1 stream :byte state))
           (let ((state (aiger-write-gates gates prev stream state)))
             (and (state-p1 state)
                  (open-output-channel-p1 stream :byte state)))))







(local (in-theory (disable aig-vars
                           aig-list-to-aiger
                           aigs-to-aiger
                           aiger-write-gates)))

(defun aiger-write-binary (latch-aigs out-aigs bad-aigs cnstr-aigs stream state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-output-channel-p stream :byte state)
                              (true-listp latch-aigs)
                              (true-listp out-aigs)
                              (true-listp bad-aigs)
                              (true-listp cnstr-aigs))))
  (b* ((nlatches (length latch-aigs))
       (nouts (length out-aigs))
       (nbads (length bad-aigs))
       (ncnstrs (length cnstr-aigs))
       (- (sneaky-save 'latch-aigs latch-aigs)
          (sneaky-save 'out-aigs out-aigs)
          (sneaky-save 'bad-aigs bad-aigs)
          (sneaky-save 'cnstr-aigs cnstr-aigs))
       ((mv pis latch-lits out-lits bad-lits cnstr-lits gates)
        (cwtime (ec-call (aigs-to-aiger latch-aigs out-aigs bad-aigs cnstr-aigs))
                :name aigs-to-aiger
                :mintime 1))
       (- (sneaky-save 'write-pis pis)
          (sneaky-save 'write-latch-lits latch-lits)
          (sneaky-save 'write-out-lits out-lits)
          (sneaky-save 'write-bad-lits bad-lits)
          (sneaky-save 'write-cnstr-lits cnstr-lits)
          (sneaky-save 'write-gates gates))
       (nins (length pis))
       (ngates (length gates))
       (maxvar (+ nins nlatches ngates))
       (state (aiger-write-header maxvar nins nlatches nouts ngates nbads ncnstrs
                                  stream state))
       (state (write-char-separated-ascii-nat-list
               latch-lits #\Newline stream state))
       (state (write-char-separated-ascii-nat-list
               out-lits #\Newline stream state))
       (state (write-char-separated-ascii-nat-list
               bad-lits #\Newline stream state))
       (state (write-char-separated-ascii-nat-list
               cnstr-lits #\Newline stream state))
       (state (cwtime (aiger-write-gates gates (* 2 (+ nins nlatches))
                                 stream state))))
    (mv pis state)))

(defthm open-output-channel-p1-of-aiger-write-binary
  (implies (and (state-p1 state)
                (symbolp stream)
                (open-output-channel-p1 stream :byte state))
           (let ((state (mv-nth 1 (aiger-write-binary latch-aigs out-aigs bad-aigs cnstr-aigs stream state))))
             (and (state-p1 state)
                  (open-output-channel-p1 stream :byte state))))
  :hints(("Goal" :in-theory (disable aiger-gate-listp))))

(in-theory (disable aiger-write-binary))

(defttag aiger-write)

(define aiger-write
  ((fname stringp "The file name to use.")
   &optional
   (latch-aigs true-listp "Alist mapping latch names to their update functions.")
   (out-aigs   true-listp "List of primary output AIGs.")
   (bad-aigs   true-listp "List of bad-state AIGs.")
   (cnstr-aigs true-listp "List of constraint AIGs.")
   (state      'state))
  :returns (mv (pis "The ordering of primary inputs that we use in the resulting
                     AIGER file, derived from variables within the input AIGs.")
               (state))
  :parents (aig-other)
  :short "Write out a collection of AIGs into an AIGER file, directly, without
going through @(see aignet)."
  :long "<p>See also @('aignet::aiger-write') for an @(see aignet)-based
alternative.  We generally prefer to use @('aignet::aiger-write') and may
eventually move to deprecate this function.</p>"
  (b* (((mv channel state)
        (open-output-channel! fname :byte state))
       ((unless channel)
        (ec-call (aiger-write-binary latch-aigs out-aigs bad-aigs
                                     cnstr-aigs
                                     channel state)))
       ((mv pis state) (aiger-write-binary latch-aigs out-aigs bad-aigs
                                           cnstr-aigs
                                           channel state))
       (state (close-output-channel channel state)))
    (mv pis state)))



;; Reading AIGER files.

;; Use a buffered read stream so we can look ahead.  Here the
;; buf is either empty or a single byte.


(set-state-ok t)


(defun read-n-str-separated-nats-tr (n sep finalp stream buf state acc)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf)
                              (stringp sep)
                              (true-listp acc)
                              (natp n))
                  :measure (nfix n)))
  (if (zp n)
      (mv t (reverse acc) buf state)
    (b* (((mv num buf state)
          (read-ascii-nat stream buf state))
         ((when (not num))
          (cw "Failed to parse number~%")
          (break$)
          (mv nil nil buf state))
         ((when (and (zp (1- n)) (not finalp)))
          (mv t (reverse (cons num acc)) buf state))
         ((mv ok buf state) (require-ascii-str sep stream buf state))
         ((when (not ok))
          (b* (((mv byte buf state)
                (peek-byte-buf stream buf state)))
            (cw "Bad separator: ~x0~%" byte)
            (break$)
            (mv nil nil buf state))))
      (read-n-str-separated-nats-tr (1- n) sep finalp stream buf state
                                    (cons num acc)))))


(defthm open-input-channel-p1-of-read-n-str-separated-nats-tr
  (implies (and (state-p1 state)
                (symbolp stream)
                (open-input-channel-p1 stream :byte state))
           (b* (((mv & & & state)
                 (read-n-str-separated-nats-tr n sep finalp stream buf state acc)))
             (and (state-p1 state)
                  (open-input-channel-p1 stream :byte state)))))

(defthm maybe-byte-p-of-read-n-str-separated-nats-tr
  (implies (maybe-byte-p buf)
           (maybe-byte-p (mv-nth 2 (read-n-str-separated-nats-tr n sep finalp stream buf state acc))))
  :rule-classes (:rewrite :type-prescription))

(defthm nat-listp-revappend
  (implies (and (nat-listp a) (nat-listp b))
           (nat-listp (revappend a b)))
  :hints(("Goal" :in-theory (enable revappend))))

(defthm nat-listp-of-read-n-str-separated-nats-tr
  (implies (nat-listp acc)
           (nat-listp (mv-nth 1 (read-n-str-separated-nats-tr
                                 n sep finalp stream buf state acc))))
  :hints(("Goal" :in-theory (enable read-n-str-separated-nats-tr))))

(in-theory (disable read-n-str-separated-nats-tr))

(defun read-n-str-separated-nats (n sep finalp stream buf state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf)
                              (stringp sep)
                              (natp n))))
  (read-n-str-separated-nats-tr n sep finalp stream buf state nil))

(defthm open-input-channel-p1-of-read-n-str-separated-nats
  (implies (and (state-p1 state)
                (symbolp stream)
                (open-input-channel-p1 stream :byte state))
           (b* (((mv & & & state)
                 (read-n-str-separated-nats n sep finalp stream buf state)))
             (and (state-p1 state)
                  (open-input-channel-p1 stream :byte state)))))

(defthm maybe-byte-p-of-read-n-str-separated-nats
  (implies (maybe-byte-p buf)
           (maybe-byte-p (mv-nth 2 (read-n-str-separated-nats n sep finalp stream buf state))))
  :rule-classes (:rewrite :type-prescription))

(defthm nat-listp-of-read-n-str-separated-nats
  (nat-listp (mv-nth 1 (read-n-str-separated-nats
                                 n sep finalp stream buf state)))
  :hints(("Goal" :in-theory (enable read-n-str-separated-nats))))

(in-theory (disable read-n-str-separated-nats))



(defun aiger-read-gate (prev stream buf state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf)
                              (natp prev))))
  (b* (((mv err delta1 buf state) (read-bytecoded-nat stream buf state))
       ((when err) (mv err nil buf state))
       ((when (int= delta1 0))
        (mv (aiger-err "Malformed gate: delta 0")
            nil buf state))
       ((mv err delta2 buf state) (read-bytecoded-nat stream buf state))
       ;; delta2 may be 0
       ((when err) (mv err nil buf state))
       (lhs (+ 2 prev))
       (rhs1 (- lhs delta1))
       (rhs2 (- rhs1 delta2))
       ((when (< rhs2 0))
        (mv (aiger-err "Malformed gate: diffs too big")
            nil buf state)))
    (mv nil (list* lhs rhs1 rhs2) buf state)))

(defthm open-input-channel-p1-of-aiger-read-gate
  (implies (and (state-p1 state)
                (symbolp stream)
                (open-input-channel-p1 stream :byte state))
           (b* (((mv & & & state)
                 (aiger-read-gate prev stream buf state)))
             (and (state-p1 state)
                  (open-input-channel-p1 stream :byte state)))))

(defthm maybe-byte-p-of-aiger-read-gate
  (maybe-byte-p (mv-nth 2 (aiger-read-gate prev stream buf state)))
  :rule-classes (:rewrite :type-prescription))


(defthm aiger-buf-measure-of-aiger-read-gate-weak
  (b* (((mv & & buf1 state1)
        (aiger-read-gate prev stream buf state)))
    (<= (aiger-buf-measure stream buf1 state1)
        (aiger-buf-measure stream buf state)))
  :rule-classes :linear)


(defthm aiger-buf-measure-of-aiger-read-gate-strong
  (b* (((mv err & buf1 state1)
        (aiger-read-gate prev stream buf state)))
    (implies (not err)
             (< (aiger-buf-measure stream buf1 state1)
                (aiger-buf-measure stream buf state))))
  :rule-classes :linear)

(in-theory (disable aiger-read-gate))

(defun aiger-read-n-gates-aux (n acc prev stream buf state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf)
                              (natp prev)
                              (true-listp acc)
                              (natp n))))
  (if (zp n)
      (mv nil (reverse acc) buf state)
    (b* (((mv err gate buf state) (aiger-read-gate prev stream buf state))
         ((when err) (mv err nil nil state)))
      (aiger-read-n-gates-aux (1- n) (cons gate acc) (+ 2 prev) stream buf
                              state))))

(defthm open-input-channel-p1-of-aiger-read-n-gates-aux
  (implies (and (state-p1 state)
                (symbolp stream)
                (open-input-channel-p1 stream :byte state))
           (b* (((mv & & & state)
                 (aiger-read-n-gates-aux n acc prev stream buf state)))
             (and (state-p1 state)
                  (open-input-channel-p1 stream :byte state)))))

(defthm maybe-byte-p-of-aiger-read-n-gates-aux
  (implies (maybe-byte-p buf)
           (maybe-byte-p (mv-nth 2 (aiger-read-n-gates-aux n acc prev stream buf state))))
  :rule-classes (:rewrite :type-prescription))

(defthm aiger-gate-listp-of-aiger-read-n-gates-aux
  (implies (and (aiger-gate-listp acc)
                (natp prev))
           (aiger-gate-listp (mv-nth 1 (aiger-read-n-gates-aux n acc prev
                                                               stream buf
                                                               state))))
  :hints(("Goal" :in-theory (e/d (aiger-read-n-gates-aux
                                  aiger-read-gate)))))

(in-theory (disable aiger-read-n-gates-aux))

(defun aiger-read-n-gates (n prev stream buf state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf)
                              (natp prev)
                              (natp n))))
  (aiger-read-n-gates-aux n nil prev stream buf state))

(defthm open-input-channel-p1-of-aiger-read-n-gates
  (implies (and (state-p1 state)
                (symbolp stream)
                (open-input-channel-p1 stream :byte state))
           (b* (((mv & & & state)
                 (aiger-read-n-gates n prev stream buf state)))
             (and (state-p1 state)
                  (open-input-channel-p1 stream :byte state)))))

(defthm maybe-byte-p-of-aiger-read-n-gates
  (implies (maybe-byte-p buf)
           (maybe-byte-p (mv-nth 2 (aiger-read-n-gates n prev stream buf state))))
  :rule-classes (:rewrite :type-prescription))

(defthm aiger-gate-listp-of-aiger-read-n-gates
  (implies (natp prev)
           (aiger-gate-listp (mv-nth 1 (aiger-read-n-gates n prev stream buf
                                                           state)))))

(in-theory (disable aiger-read-n-gates))

(local (in-theory (disable state-p1-forward)))


(defun aiger-parse-binary (stream buf state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf))))
  (b* (((mv err i l a o b c buf state)
        (aiger-parse-header stream buf state))
       ((when err)
        (mv err nil nil nil nil nil state))
       (newline-str (coerce (list #\Newline) 'string))
       ((mv ok latch-lits buf state)
        (read-n-str-separated-nats l newline-str t stream buf state))
       ((when (not ok))
        (mv (aiger-err (msg "Failed to read ~x0 latches~%" l))
            nil nil nil nil nil state))
       ((mv ok out-lits buf state)
        (read-n-str-separated-nats o newline-str t stream buf state))
       ((when (not ok))
        (mv (aiger-err (msg "Failed to read ~x0 outputs~%" o))
            nil nil nil nil nil state))
       ((mv ok bad-lits buf state)
        (read-n-str-separated-nats b newline-str t stream buf state))
       ((when (not ok))
        (mv (aiger-err (msg "Failed to read ~x0 bad literals" o))
            nil nil nil nil nil state))
       ((mv ok cnstr-lits buf state)
        (read-n-str-separated-nats c newline-str t stream buf state))
       ((when (not ok))
        (mv (aiger-err (msg "Failed to read ~x0 constraints~%" o))
            nil nil nil nil nil state))
       ((mv err gates & state)
        (aiger-read-n-gates a (* 2 (+ i l)) stream buf state))
       ((when err) (mv err nil nil nil nil nil state)))
    (mv nil latch-lits out-lits bad-lits cnstr-lits gates state)))


(defthm open-input-channel-p1-of-aiger-parse-binary
  (implies (and (state-p1 state)
                (symbolp stream)
                (open-input-channel-p1 stream :byte state))
           (b* (((mv & & & & & & state)
                 (aiger-parse-binary stream buf state)))
             (and (state-p1 state)
                  (open-input-channel-p1 stream :byte state))))
  :hints(("Goal" :in-theory (disable nth-with-large-index
                                     mv-nth-cons-meta
                                     nth nfix-when-natp
                                     nfix-when-not-natp len))))

(defthm aiger-gate-listp-of-aiger-parse-binary
  (aiger-gate-listp (mv-nth 5 (aiger-parse-binary stream buf state)))
  :hints(("Goal" :in-theory (disable nth-with-large-index
                                     mv-nth-cons-meta
                                     nth nfix-when-natp
                                     nfix-when-not-natp len))))

(defthm nat-listp-lits-of-aiger-parse-binary
  (b* (((mv & latches outs bads cnstrs & &)
        (aiger-parse-binary stream buf state)))
    (and (nat-listp latches)
         (nat-listp outs)
         (nat-listp bads)
         (nat-listp cnstrs)))
  :hints(("Goal" :in-theory (disable nth-with-large-index
                                     mv-nth-cons-meta
                                     nth nfix-when-natp
                                     nfix-when-not-natp len))))

(in-theory (disable aiger-parse-binary))

(defun aiger-parse (fname state)
  (declare (xargs :stobjs state
                  :guard (stringp fname)))
  (b* (((mv channel state) (open-input-channel fname :byte state))
       ((when (not channel))
        (mv (aiger-err (msg "AIGER-PARSE: Failed to open file ~x0.~%" fname))
            nil nil nil nil nil state))
       ((mv err latch-lits out-lits bad-lits cnstr-lits gates state)
        (aiger-parse-binary channel nil state))
       (state (close-input-channel channel state)))
    (mv err latch-lits out-lits bad-lits cnstr-lits gates state)))

(local (defthm nat-listp-implies-integer-listp
         (implies (nat-listp x)
                  (integer-listp x))))

(define aiger-read
  ((fname      stringp    "The file name to read.")
   (innames    true-listp "A list of names to give the primary inputs.")
   (latchnames true-listp "A list of names to use for the latches.")
   state)
  :returns (mv (err        "An error @(see msg) on any error.")
               (latch-aigs "An alist of latch names to their update functions.")
               (out-aigs   "List of output aigs.")
               (bad-aigs   "List of bad-state aigs.")
               (cnstr-aigs "List of constraint aigs.")
               state)
  :parents (aig-other)
  :short "Read an AIGER file into a collection of AIGs."

  (b* (((mv err latch-lits out-lits bad-lits cnstr-lits gates state) (aiger-parse fname state))
       ((when err) (mv err nil nil nil nil state))
       (- (sneaky-save 'innames innames)
          (sneaky-save 'latchnames latchnames)
          (sneaky-save 'latch-lits latch-lits)
          (sneaky-save 'out-lits out-lits)
          (sneaky-save 'bad-lits bad-lits)
          (sneaky-save 'cnstr-lits cnstr-lits)
          (sneaky-save 'gates gates))
       ((mv latch-aigs out-aigs bad-aigs cnstr-aigs)
        (aiger-to-aigs innames latchnames latch-lits out-lits bad-lits cnstr-lits gates)))
    (mv nil latch-aigs out-aigs bad-aigs cnstr-aigs state)))

;; (b* ((latch-aigs (hons-shrink-alist
;;                   `((c . ,(aig-ite 'a 'c 'd))
;;                     (d . ,(aig-ite 'b 'd 'c)))
;;                   nil))
;;      (out-aigs (list (aig-and 'a 'c)
;;                      (aig-and 'b 'd)))
;;      (- (cw "latch-aigs: ~x0~%out-aigs: ~x1~%" latch-aigs out-aigs))
;;      (?latchnames (strip-cars latch-aigs))
;;      ((mv pis latch-lits out-lits gates)
;;       (aigs-to-aiger latch-aigs out-aigs))
;;      (- (cw "pis: ~x0~%latch-lits: ~x1~%out-lits: ~x2~%gates: ~x3~%"
;;             pis latch-lits out-lits gates))
;;      ((mv ?innames state)
;;       (aiger-write latch-aigs out-aigs "foo" state))
;;      (- (cw "latchnames: ~x0~%" latchnames))
;;      (- (cw "innames: ~x0~%" innames))
;;      ((mv & latch-lits out-lits gates state)
;;       (aiger-parse "foo" state))
;;      (- (cw "latch-lits: ~x0~%out-lits: ~x1~%gates: ~x2~%" latch-lits out-lits
;;             gates))
;;      ((mv latch-aigs out-aigs)
;;       (aiger-to-aigs innames latchnames latch-lits out-lits gates)))
;;   (mv nil latch-aigs out-aigs state))









