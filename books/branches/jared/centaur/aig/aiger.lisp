; Centaur AIG Library
; Copyright (C) 2012 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; AIG <--> AIGER file conversion
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "tools/bstar" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(include-book "data-structures/list-defthms" :dir :system)
(include-book "aig-vars-ext")
(include-book "centaur/vl/util/cwtime" :dir :system)
(include-book "centaur/misc/sneaky-load" :dir :system)
(include-book "centaur/misc/numlist" :dir :system)
(include-book "tools/defmacfun" :dir :system)
(include-book "misc/definline" :dir :system)
(include-book "std/io/base" :dir :system)
(include-book "arithmetic/nat-listp" :dir :system)
(local (include-book "clause-processors/instantiate" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/alists/top" :dir :system))
(include-book "cutil/defmvtypes" :dir :system)

(local (in-theory (disable reverse-removal revappend-removal)))

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

(defun aiger-err (msg)
  (declare (xargs :guard t))
  msg)

(local (in-theory (enable* ihsext-bounds-thms)))

(local (defthm logtail-decr
         (implies (and (posp n)
                       (posp s))
                  (< (logtail s n) n))
         :hints(("Goal" :in-theory (enable* ihsext-inductions
                                            ihsext-recursive-redefs)
                 :induct t))
         :rule-classes :linear))

(local (defthm logtail-decr2
         (implies (and (posp (logtail s n))
                       (posp s))
                  (< (logtail s n) n))
         :hints(("Goal" :in-theory (enable* ihsext-inductions
                                            ihsext-recursive-redefs)
                 :induct t))
         :rule-classes :linear))

(defun aiger-write-delta (n stream state)
  (declare (xargs :guard (and (natp n)
                              (symbolp stream)
                              (open-output-channel-p stream :byte state))
                  :verify-guards nil
                  :measure (nfix n)
                  :stobjs state))
  (b* ((n (lnfix n))
       (nextn (ash n -7))
       (donep (zp nextn))
       (newbyte (if donep n (logior #x80 (logand #x7F n))))
       (state (write-byte$ newbyte stream state)))
    (if donep
        state
      (aiger-write-delta nextn stream state))))

(local
 (encapsulate nil
   (local (defthm bound-when-logtail-7-is-0-lemma
            (implies (and (equal (logtail n x) 0)
                          (natp x)
                          (natp n))
                     (< x (ash 1 n)))
            :hints (("goal" :in-theory (enable* ihsext-inductions
                                                ihsext-recursive-redefs)))
            :rule-classes nil))
   (defthm bound-when-logtail-7-is-0
     (implies (and (equal (logtail 7 x) 0)
                   (natp x)
                   (natp n))
              (< x 128))
     :rule-classes :forward-chaining
     :hints (("goal" :use ((:instance bound-when-logtail-7-is-0-lemma
                            (n 7))))))

   (defthm logior-128-loghead-7-bound
     (< (logior 128 (loghead 7 n)) 256)
     :hints (("goal" :use ((:instance unsigned-byte-p-of-loghead
                            (size1 8) (size 7) (i n))
                           (:instance unsigned-byte-p-of-logior
                            (n 8) (x 128) (y (loghead 7 n))))
              :in-theory (disable unsigned-byte-p-of-logior
                                  unsigned-byte-p-of-loghead))))))

(verify-guards aiger-write-delta)

(defthm open-output-channel-p1-of-aiger-write-delta
  (implies (and (state-p1 state)
                (symbolp stream)
                (open-output-channel-p1 stream :byte state))
           (let ((state (aiger-write-delta n stream state)))
             (and (state-p1 state)
                  (open-output-channel-p1 stream :byte state)))))

           

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


(defun write-ascii-string1 (idx str stream state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-output-channel-p stream :byte state)
                              (stringp str)
                              (natp idx))
                  :measure (nfix (- (length str) (nfix idx)))))
  (if (<= (length str) (lnfix idx))
      state
    (let ((state (write-byte$ (char-code (char str idx)) stream state)))
      (write-ascii-string1 (1+ (lnfix idx)) str stream state))))

(defthm open-output-channel-p1-of-write-ascii-string1
  (implies (and (state-p1 state)
                (symbolp stream)
                (open-output-channel-p1 stream :byte state))
           (let ((state (write-ascii-string1 idx str stream state)))
             (and (state-p1 state)
                  (open-output-channel-p1 stream :byte state)))))

(defun write-ascii-string (str stream state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-output-channel-p stream :byte state)
                              (stringp str))))
  (write-ascii-string1 0 str stream state))

(encapsulate nil
  (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
  (local (in-theory (disable floor)))
  (defun write-ascii-nat (n stream state)
    (declare (xargs :stobjs state
                    :guard (and (symbolp stream)
                                (open-output-channel-p stream :byte state)
                                (natp n))
                    :ruler-extenders :all
                    :measure (nfix n)
                    :verify-guards nil))
    (b* ((n (lnfix n))
         (digit (mod n 10))
         (rest (floor n 10))
         (byte (+ (char-code #\0) digit))
         (state (if (zp rest)
                    state
                  (write-ascii-nat rest stream state))))
      (write-byte$ byte stream state)))

  (defthm open-output-channel-p1-of-write-ascii-nat
    (implies (and (state-p1 state)
                  (symbolp stream)
                  (open-output-channel-p1 stream :byte state))
             (let ((state (write-ascii-nat n stream state)))
               (and (state-p1 state)
                    (open-output-channel-p1 stream :byte state)))))

  (verify-guards write-ascii-nat))

(defun write-char-separated-ascii-nat-list (lst sep stream state)
  (declare (xargs :guard (and (symbolp stream)
                              (open-output-channel-p stream :byte state)
                              (nat-listp lst)
                              (characterp sep))
                  :stobjs state))
  (if (atom lst)
      state
    (b* ((state (write-ascii-nat (car lst) stream state))
         (state (write-byte$ (char-code sep) stream state)))
      (write-char-separated-ascii-nat-list
       (cdr lst) sep stream state))))

(defthm open-output-channel-p1-of-write-char-separated-ascii-nat-list
  (implies (and (state-p1 state)
                (symbolp stream)
                (open-output-channel-p1 stream :byte state))
           (let ((state (write-char-separated-ascii-nat-list lst sep stream state)))
             (and (state-p1 state)
                  (open-output-channel-p1 stream :byte state)))))

(in-theory (disable write-char-separated-ascii-nat-list))

(defun write-char-separated-ascii-nat-list-no-end (lst sep stream state)
  (declare (xargs :guard (and (symbolp stream)
                              (open-output-channel-p stream :byte state)
                              (nat-listp lst)
                              (characterp sep))
                  :stobjs state))
  (if (atom lst)
      state
    (b* ((state (write-ascii-nat (car lst) stream state))
         (state (if (consp (cdr lst))
                    (write-byte$ (char-code sep) stream state)
                  state)))
      (write-char-separated-ascii-nat-list-no-end
       (cdr lst) sep stream state))))

(defthm open-output-channel-p1-of-write-char-separated-ascii-nat-list-no-end
  (implies (and (state-p1 state)
                (symbolp stream)
                (open-output-channel-p1 stream :byte state))
           (let ((state (write-char-separated-ascii-nat-list-no-end lst sep stream state)))
             (and (state-p1 state)
                  (open-output-channel-p1 stream :byte state)))))

(in-theory (disable write-char-separated-ascii-nat-list-no-end))

(defun drop-trailing-0s (lst)
  (declare (Xargs :guard t))
  (if (Atom lst)
      nil
    (let ((rest (drop-trailing-0s (cdr lst))))
      (if rest
          (cons (car lst) rest)
        (if (eql (car lst) 0)
            nil
          (list (car lst)))))))

(defthm nat-listp-drop-trailing-0s
  (implies (nat-listp x)
           (nat-listp (drop-trailing-0s x))))

(defun aiger-write-header (maxvar nins nlatches nouts ngates nbads ncnstrs stream state)
  (declare (xargs :stobjs state
                   :guard (and (symbolp stream)
                               (open-output-channel-p stream :byte state)
                               (natp maxvar) (natp nins) (natp nlatches) (natp nouts)
                               (natp ngates) (natp nbads) (natp ncnstrs))))
  (b* ((state (write-ascii-string "aig " stream state))
       (state (write-char-separated-ascii-nat-list-no-end
               (append (list maxvar nins nlatches nouts ngates)
                       (drop-trailing-0s (list nbads ncnstrs)))
               #\Space stream state))
       (state (write-byte$ (char-code #\Newline) stream state)))
    state))

(defthm open-output-channel-p1-of-aiger-write-header
  (implies (and (state-p1 state)
                (symbolp stream)
                (open-output-channel-p1 stream :byte state))
           (let ((state (aiger-write-header maxvar nins nlatches nouts ngates
                                            nbads ncnstrs stream state)))
             (and (state-p1 state)
                  (open-output-channel-p1 stream :byte state)))))

(in-theory (disable aiger-write-header))

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

(defmacfun aiger-write (fname &optional latch-aigs out-aigs bad-aigs cnstr-aigs
                              &auto state)
  (declare (xargs :stobjs state
                  :guard (and (stringp fname)
                              (true-listp latch-aigs)
                              (true-listp out-aigs)
                              (true-listp bad-aigs)
                              (true-listp cnstr-aigs))))
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


(defund maybe-byte-p (x)
  (declare (xargs :guard t))
  (or (not x)
      (bytep x)))

(defthm maybe-byte-p-of-byte
  (implies (and (natp x) (< x 256))
           (maybe-byte-p x))
  :hints(("Goal" :in-theory (enable maybe-byte-p))))

(defthm maybe-byte-p-of-read-byte$
  (implies (and (state-p1 state)
                (symbolp stream)
                (open-input-channel-p1 stream :byte state))
           (maybe-byte-p (mv-nth 0 (read-byte$ stream state))))
  :hints(("Goal" :in-theory (enable maybe-byte-p))))

(defthm maybe-byte-p-compound-recognizer
  (implies (maybe-byte-p x)
           (or (not x)
               (natp x)))
  :hints(("Goal" :in-theory (enable maybe-byte-p)))
  :rule-classes :compound-recognizer)

(defthm maybe-byte-p-bound
  (implies (and (maybe-byte-p x)
                x)
           (< x 256))
  :hints(("Goal" :in-theory (enable maybe-byte-p)))
  :rule-classes :forward-chaining)

(local (defthm maybe-byte-p-bound-rw
         (implies (and (maybe-byte-p x) x)
                  (< x 256))
         :rule-classes :rewrite))

(set-state-ok t)

(definline read-byte-buf (stream buf state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf))))
  (mbe :logic (mv-let (res buf state)
                (if buf 
                    (mv buf nil state)
                  (b* (((mv byte state) (read-byte$ stream state)))
                    (mv byte nil state)))
                (mv (and (maybe-byte-p res) res) buf state))
       :exec (if buf 
                 (mv buf nil state)
               (b* (((mv byte state) (read-byte$ stream state)))
                 (mv byte nil state)))))

(defthm maybe-byte-p-of-read-byte-buf-res
  (maybe-byte-p (mv-nth 0 (read-byte-buf stream buf state)))
  :rule-classes (:rewrite :type-prescription))

(defthm maybe-byte-p-of-read-byte-buf-buf
  (maybe-byte-p (mv-nth 1 (read-byte-buf stream buf state)))
  :rule-classes (:rewrite :type-prescription))

(definline peek-byte-buf (stream buf state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf))))
  (mbe :logic (mv-let (res buf state)
                (if (and (maybe-byte-p buf) buf)
                    (mv buf buf state)
                  (b* (((mv byte state) (read-byte$ stream state)))
                    (mv byte byte state)))
                (mv (and (maybe-byte-p res) res)
                    (and (maybe-byte-p buf) buf)
                    state))
       :exec (if buf
                 (mv buf buf state)
               (b* (((mv byte state) (read-byte$ stream state)))
                 (mv byte byte state)))))

(defthm maybe-byte-p-of-peek-byte-buf-res
  (maybe-byte-p (mv-nth 0 (peek-byte-buf stream buf state)))
  :rule-classes (:rewrite :type-prescription))

(defthm maybe-byte-p-of-peek-byte-buf-buf
  (maybe-byte-p (mv-nth 1 (peek-byte-buf stream buf state)))
  :rule-classes (:rewrite :type-prescription))

(defthm peek-byte-buf-of-peek-byte-buf
  (implies (mv-nth 0 (peek-byte-buf stream buf state))
           (equal (peek-byte-buf stream
                                 (mv-nth 1 (peek-byte-buf stream buf state))
                                 (mv-nth 2 (peek-byte-buf stream buf state)))
                  (peek-byte-buf stream buf state))))

(definline skip-byte-buf (stream buf state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state))))
  (if buf
      (mv nil state)
    (b* (((mv & state) (read-byte$ stream state)))
        (mv nil state))))

(defthm maybe-byte-p-of-skip-byte-buf
  (maybe-byte-p (mv-nth 0 (skip-byte-buf stream buf state)))
  :rule-classes (:rewrite :type-prescription))


(defthm open-input-channel-p1-of-read-byte-buf
  (implies (and (symbolp stream)
                (state-p1 state)
                (open-input-channel-p1 stream :byte state))
           (b* (((mv & & state) (read-byte-buf stream buf state)))
             (and (open-input-channel-p1 stream :byte state)
                  (state-p1 state)))))


(defthm open-input-channel-p1-of-peek-byte-buf
  (implies (and (symbolp stream)
                (state-p1 state)
                (open-input-channel-p1 stream :byte state))
           (b* (((mv & & state) (peek-byte-buf stream buf state)))
             (and (open-input-channel-p1 stream :byte state)
                  (state-p1 state)))))

(defthm open-input-channel-p1-of-skip-byte-buf
  (implies (and (symbolp stream)
                (state-p1 state)
                (open-input-channel-p1 stream :byte state))
           (b* (((mv & state) (skip-byte-buf stream buf state)))
             (and (open-input-channel-p1 stream :byte state)
                  (state-p1 state)))))
    
(defun aiger-buf-measure (stream buf state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf))))
  (+ (if buf 1 0) (non-exec (file-measure stream state))))

(defthm aiger-buf-measure-of-read-byte-buf-weak
  (b* (((mv & buf1 state1) (read-byte-buf stream buf state)))
    (<= (aiger-buf-measure stream buf1 state1)
        (aiger-buf-measure stream buf state)))
  :rule-classes :linear)

(defthm aiger-buf-measure-of-read-byte-buf-strong
  (b* (((mv res1 buf1 state1) (read-byte-buf stream buf state)))
    (implies res1
             (< (aiger-buf-measure stream buf1 state1)
                (aiger-buf-measure stream buf state))))
  :rule-classes :linear)

;; there is no strong
(defthm aiger-buf-measure-of-peek-byte-buf
  (b* (((mv & buf1 state1) (peek-byte-buf stream buf state)))
    (<= (aiger-buf-measure stream buf1 state1)
        (aiger-buf-measure stream buf state)))
  :rule-classes :linear)

;; there is no strong
(defthm aiger-buf-measure-of-skip-byte-buf
  (b* (((mv buf1 state1) (skip-byte-buf stream buf state)))
    (<= (aiger-buf-measure stream buf1 state1)
        (aiger-buf-measure stream buf state)))
  :rule-classes :linear)

(defthm aiger-buf-measure-of-skip-byte-buf-strong-by-peek
  (b* (((mv peek buf1 state1) (peek-byte-buf stream buf state))
       ((mv buf2 state2) (skip-byte-buf stream buf1 state1)))
    (implies peek
             (< (aiger-buf-measure stream buf2 state2)
                (aiger-buf-measure stream buf state))))
  :rule-classes :linear)

(in-theory (disable aiger-buf-measure
                    read-byte-buf
                    peek-byte-buf
                    skip-byte-buf))


(defun skip-ascii-chars (char stream buf state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (characterp char)
                              (maybe-byte-p buf))
                  :measure (aiger-buf-measure stream buf state)))
  (b* (((mv byte buf state) (peek-byte-buf stream buf state))
       ((when (not (eql byte (char-code char))))
        (mv buf state))
       ((mv buf state) (skip-byte-buf stream buf state)))
    (skip-ascii-chars char stream buf state)))

(defthm open-input-channel-p1-of-skip-ascii-chars
  (implies (and (state-p1 state)
                (symbolp stream)
                (open-input-channel-p1 stream :byte state))
           (b* (((mv & state)
                 (skip-ascii-chars char stream buf state)))
             (and (state-p1 state)
                  (open-input-channel-p1 stream :byte state)))))

(defthm maybe-byte-p-of-skip-ascii-chars
  (maybe-byte-p (mv-nth 0 (skip-ascii-chars char stream buf state)))
  :rule-classes (:rewrite :type-prescription))

(local (in-theory (disable skip-ascii-chars)))

(defun require-ascii-str1 (idx str stream buf state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (natp idx)
                              (stringp str)
                              (<= idx (length str))
                              (maybe-byte-p buf))
                  :measure (nfix (- (length str) (nfix idx)))))
  (if (<= (length str) (lnfix idx))
      (mv t buf state)
    (b* (((mv byte buf state)
          (peek-byte-buf stream buf state))
         ((when (or (not byte)
                    (not (eql byte (char-code (char str idx))))))
          (cw "Bad: ~x0 ~x1~%" (char str idx)
              (if byte (code-char byte) nil))
          (mv nil buf state))
         ((mv buf state) (skip-byte-buf stream buf state)))
      (require-ascii-str1 (1+ (lnfix idx)) str stream buf state))))

(defthm open-input-channel-p1-of-require-ascii-str1
  (implies (and (state-p1 state)
                (symbolp stream)
                (open-input-channel-p1 stream :byte state))
           (b* (((mv & & state)
                 (require-ascii-str1 idx str stream buf state)))
             (and (state-p1 state)
                  (open-input-channel-p1 stream :byte state)))))

(defthm maybe-byte-p-of-require-ascii-str1
  (implies (maybe-byte-p buf)
           (maybe-byte-p (mv-nth 1 (require-ascii-str1 idx str stream buf
                                                       statE))))
  :rule-classes (:rewrite :type-prescription))

(in-theory (disable  require-ascii-str1))

(defun require-ascii-str (str stream buf state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (stringp str)
                              (maybe-byte-p buf))))
  (require-ascii-str1 0 str stream buf state))

(defthm open-input-channel-p1-of-require-ascii-str
  (implies (and (state-p1 state)
                (symbolp stream)
                (open-input-channel-p1 stream :byte state))
           (b* (((mv & & state)
                 (require-ascii-str str stream buf state)))
             (and (state-p1 state)
                  (open-input-channel-p1 stream :byte state)))))

(defthm maybe-byte-p-of-require-ascii-str
  (implies (maybe-byte-p buf)
           (maybe-byte-p (mv-nth 1 (require-ascii-str str stream buf statE))))
  :rule-classes (:rewrite :type-prescription))

(in-theory (disable require-ascii-str))

(defun read-ascii-nat1 (rest stream buf state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf)
                              (natp rest))
                  :measure (aiger-buf-measure stream buf state)))
  (b* (((mv byte buf state) (peek-byte-buf stream buf state))
       ((when (not (and (integerp byte)
                        (<= (char-code #\0) byte)
                        (<= byte (char-code #\9)))))
        (mv rest buf state))
       ((mv buf state) (skip-byte-buf stream buf state)))
    (read-ascii-nat1
     (+ (* 10 rest) (- byte (char-code #\0)))
     stream buf state)))

(defthm natp-read-ascii-nat1
  (implies (natp rest)
           (natp (mv-nth 0 (read-ascii-nat1 rest stream buf state))))
  :hints(("Goal" :in-theory (enable read-ascii-nat1)))
  :rule-classes (:rewrite :type-prescription))

(defthm open-input-channel-p1-of-read-ascii-nat1
  (implies (and (state-p1 state)
                (symbolp stream)
                (open-input-channel-p1 stream :byte state))
           (b* (((mv & & state)
                 (read-ascii-nat1 rest stream buf state)))
             (and (state-p1 state)
                  (open-input-channel-p1 stream :byte state)))))

(defthm maybe-byte-p-of-read-ascii-nat1
  (maybe-byte-p (mv-nth 1 (read-ascii-nat1 rest stream buf state)))
  :rule-classes (:rewrite :type-prescription))

(defthm aiger-buf-measure-of-read-ascii-nat1
  (b* (((mv & buf1 state1)
        (read-ascii-nat1 rest stream buf state)))
    (<= (aiger-buf-measure stream buf1 state1)
        (aiger-buf-measure stream buf state)))
  :rule-classes :linear)

(in-theory (disable read-ascii-nat1))

(defun read-ascii-nat (stream buf state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf))))
  (b* (((mv byte buf state) (peek-byte-buf stream buf state))
       ((when (not (and (integerp byte)
                        (<= (char-code #\0) byte)
                        (<= byte (char-code #\9)))))
        (mv nil buf state))
       ((mv buf state) (skip-byte-buf stream buf state)))
    (read-ascii-nat1
     (- byte (char-code #\0))
     stream buf state)))

(defthm natp-read-ascii-nat
  (or (not (mv-nth 0 (read-ascii-nat stream buf state)))
      (natp (mv-nth 0 (read-ascii-nat stream buf state))))
  :hints(("Goal" :in-theory (enable read-ascii-nat)))
  :rule-classes :type-prescription)

(defthm natp-read-ascii-nat-when-peek
  (implies (b* ((n (mv-nth 0 (peek-byte-buf stream buf state))))
             (and (integerp n)
                  (<= (char-code #\0) n)
                  (<= n (char-code #\9))))
           (natp (mv-nth 0 (read-ascii-nat stream buf state))))
  :hints(("Goal" :in-theory (enable read-ascii-nat))))

(defthm open-input-channel-p1-of-read-ascii-nat
  (implies (and (state-p1 state)
                (symbolp stream)
                (open-input-channel-p1 stream :byte state))
           (b* (((mv & & state)
                 (read-ascii-nat stream buf state)))
             (and (state-p1 state)
                  (open-input-channel-p1 stream :byte state)))))

(defthm maybe-byte-p-of-read-ascii-nat
  (maybe-byte-p (mv-nth 1 (read-ascii-nat stream buf state))))

(defthm aiger-buf-measure-of-read-ascii-nat-weak
  (b* (((mv & buf1 state1)
        (read-ascii-nat stream buf state)))
    (<= (aiger-buf-measure stream buf1 state1)
        (aiger-buf-measure stream buf state)))
  :rule-classes :linear)

(defthm aiger-buf-measure-of-read-ascii-nat-strong
  (b* (((mv res buf1 state1)
        (read-ascii-nat stream buf state)))
    (implies res
             (< (aiger-buf-measure stream buf1 state1)
                (aiger-buf-measure stream buf state))))
  :rule-classes :linear)

(defthm aiger-buf-measure-of-read-ascii-nat-strong1
  (b* (((mv & buf1 state1)
        (read-ascii-nat stream buf state))
       (byte1 (mv-nth 0 (peek-byte-buf stream buf state))))
    (implies (and (integerp byte1)
                  (<= (char-code #\0) byte1)
                  (<= byte1 (char-code #\9)))
             (< (aiger-buf-measure stream buf1 state1)
                (aiger-buf-measure stream buf state))))
  :rule-classes :linear)

(in-theory (disable read-ascii-nat))

;; skips spaces and tabs
(defun skip-linespace (stream buf state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf))
                  :measure (aiger-buf-measure stream buf state)))
  (b* (((mv byte buf state) (peek-byte-buf stream buf state))
       ((when (not (and (integerp byte)
                        (member (code-char byte) '(#\Space #\Tab)))))
        (mv buf state))
       ((mv buf state) (skip-byte-buf stream buf state)))
    (skip-linespace stream buf state)))

(defthm open-input-channel-p1-of-skip-linespace
  (implies (and (state-p1 state)
                (symbolp stream)
                (open-input-channel-p1 stream :byte state))
           (b* (((mv & state)
                 (skip-linespace stream buf state)))
             (and (state-p1 state)
                  (open-input-channel-p1 stream :byte state)))))

(defthm maybe-byte-p-of-skip-linespace
  (maybe-byte-p (mv-nth 0 (skip-linespace stream buf state)))
  :rule-classes (:rewrite :type-prescription))

(defthm aiger-buf-measure-of-skip-linespace
  (b* (((mv  buf1 state1)
        (skip-linespace stream buf state)))
    (<= (aiger-buf-measure stream buf1 state1)
        (aiger-buf-measure stream buf state)))
  :rule-classes :linear)

(in-theory (disable skip-linespace))

;; Reads natural numbers until we come to some non-digit, non-space/tab
;; character.
(defun read-nats-in-line (stream buf state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf))
                  :measure (aiger-buf-measure stream buf state)))
  (b* (((mv buf state) (skip-linespace stream buf state))
       ((mv byte buf state) (peek-byte-buf stream buf state))
       ((unless (and (integerp byte)
                     (<= (char-code #\0) byte)
                     (<= byte (char-code #\9))))
        (mv nil buf state))
       ((mv head buf state) (read-ascii-nat stream buf state))
       ((mv rest buf state) (read-nats-in-line stream buf state)))
    (mv (cons head rest) buf state)))

(defthm open-input-channel-p1-of-read-nats-in-line
  (implies (and (state-p1 state)
                (symbolp stream)
                (open-input-channel-p1 stream :byte state))
           (b* (((mv & & state)
                 (read-nats-in-line stream buf state)))
             (and (state-p1 state)
                  (open-input-channel-p1 stream :byte state)))))

(defthm maybe-byte-p-of-read-nats-in-line
  (maybe-byte-p (mv-nth 1 (read-nats-in-line stream buf state)))
  :rule-classes (:rewrite :type-prescription))

(defthm aiger-buf-measure-of-read-nats-in-line
  (b* (((mv & buf1 state1)
        (read-nats-in-line stream buf state)))
    (<= (aiger-buf-measure stream buf1 state1)
        (aiger-buf-measure stream buf state)))
  :rule-classes :linear)

(defthm nat-listp-read-nats-in-line
  (nat-listp (mv-nth 0 (read-nats-in-line stream buf state)))
  :hints(("Goal" :in-theory (enable read-nats-in-line)))
  :rule-classes
  (:rewrite
   (:forward-chaining :trigger-terms ((mv-nth 0 (read-nats-in-line stream buf state))))))

(in-theory (disable read-nats-in-line))
       
      
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


(defun read-bytecoded-nat (stream buf state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf))
                  :verify-guards nil
                  :measure (aiger-buf-measure stream buf state)))
  (b* (((mv byte buf state) (read-byte-buf stream buf state))
       ((when (not byte))
        
        (mv (aiger-err "EOF while reading bytecoded natural~%")
            0 buf state))
       ((when (not (logbitp 7 byte)))
        ;; done
        (mv nil byte buf state))
       ((mv err rest buf state)
        (read-bytecoded-nat stream buf state))
       ((when err)
        (mv err 0 buf state)))
    (mv nil
        (+ (logand #x7F byte) (ash rest 7))
        buf state)))

(defthm natp-of-read-bytecoded-nat
  (natp (mv-nth 1 (read-bytecoded-nat stream buf state)))
  :rule-classes :type-prescription)

(verify-guards read-bytecoded-nat)

(defthm open-input-channel-p1-of-read-bytecoded-nat
  (implies (and (state-p1 state)
                (symbolp stream)
                (open-input-channel-p1 stream :byte state))
           (b* (((mv & & & state)
                 (read-bytecoded-nat stream buf state)))
             (and (state-p1 state)
                  (open-input-channel-p1 stream :byte state)))))

(defthm maybe-byte-p-of-read-bytecoded-nat
  (maybe-byte-p (mv-nth 2 (read-bytecoded-nat stream buf state)))
  :rule-classes (:rewrite :type-prescription))


(defthm aiger-buf-measure-of-read-bytecoded-nat-weak
  (b* (((mv & & buf1 state1)
        (read-bytecoded-nat stream buf state)))
    (<= (aiger-buf-measure stream buf1 state1)
        (aiger-buf-measure stream buf state)))
  :hints (("goal" :induct (read-bytecoded-nat stream buf state)))
  :rule-classes :linear)


(defthm aiger-buf-measure-of-read-bytecoded-nat-strong
  (b* (((mv err & buf1 state1)
        (read-bytecoded-nat stream buf state)))
    (implies (not err)
             (< (aiger-buf-measure stream buf1 state1)
                (aiger-buf-measure stream buf state))))
  :hints (("goal" :induct (read-bytecoded-nat stream buf state)))
  :rule-classes :linear)

(in-theory (Disable read-bytecoded-nat))

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

(local
 (defthm natp-nth-in-nat-list
   (implies (and (nat-listp x)
                 (natp n)
                 (< n (len x)))
            (natp (nth n x)))
   :rule-classes (:rewrite :type-prescription)))


(defun aiger-parse-header (stream buf state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp stream)
                              (open-input-channel-p stream :byte state)
                              (maybe-byte-p buf))))
  (b* (((mv ok buf state) (require-ascii-str "aig" stream buf state))
       ((when (not ok))
        (mv (aiger-err "Bad header: no \"aig\"~%")
            0 0 0 0 0 0 buf state))
       ((mv buf state) (skip-ascii-chars #\Space stream buf state))
       ((mv sizes buf state)
        (read-nats-in-line stream buf state))
       ((when (not (<= 5 (len sizes))))
        (mv (aiger-err "Bad header: not enough numbers in size list")
            0 0 0 0 0 0 buf state))
       ((mv first buf state) (read-byte-buf stream buf state))
       ((when (not (and first (eql (code-char first) #\Newline))))
        (mv (aiger-err "Bad header: didn't reach newline while reading size list~%")
            0 0 0 0 0 0 buf state))
       ((mv buf state) (skip-ascii-chars #\Space stream buf state))
       ((nths & i l o a b c j f) sizes)
       ;; the b c j f entries aren't required
       (b (nfix b))
       (c (nfix c))
       (j (nfix j))
       (f (nfix f))
       ((unless (and (equal j 0)
                     (equal f 0)))
        (mv (aiger-err "We don't support justice properties or fairness constraints yet~%")
            0 0 0 0 0 0 buf state)))
    (mv nil i l a o b c buf state)))

(defthm open-input-channel-p1-of-aiger-parse-header
  (implies (and (state-p1 state)
                (symbolp stream)
                (open-input-channel-p1 stream :byte state))
           (b* ((state
                 (mv-nth 8 (aiger-parse-header stream buf state))))
             (and (state-p1 state)
                  (open-input-channel-p1 stream :byte state)))))

(defthm maybe-byte-p-of-aiger-parse-header
  (implies (maybe-byte-p buf)
           (maybe-byte-p (mv-nth 7 (aiger-parse-header stream buf state))))
  :rule-classes (:rewrite :type-prescription))

(local (in-theory (disable nth-when-zp)))
(defmvtypes aiger-parse-header (nil natp natp natp natp natp natp nil nil))

(local (in-theory (disable aiger-parse-header)))
  
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
                                     natp-nth-in-nat-list
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
                                     natp-nth-in-nat-list
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

(defun aiger-read (fname innames latchnames state)
  (declare (xargs :stobjs state
                  :guard (and (true-listp innames)
                              (true-listp latchnames)
                              (stringp fname))))
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
  








