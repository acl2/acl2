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
(include-book "assms/top")
(include-book "traces/trace-okp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; Essay on Rewriting Caching
;;
;; We use a cache to avoid repeatedly rewriting the same term.  The cache acts
;; like an accumulator: crewrite takes the current cache as an input, and when
;; it returns its resulting term, it also returns an updated cache.
;;
;; The cache remembers how previously-rewritten terms were simplified.  For now
;; just think of the cache as a mapping from terms to traces.  For example, if
;; (foo x) previously rewrote to true, our cache might contain an entry such as
;; (foo x) -> [trace of how (foo x) rewrites to true].  Now, when we encounter
;; (foo x) again, we can simply reuse this trace.
;;
;;
;; Introduction.
;;
;; Caching is a subtle business.  Lets first review the arguments taken by
;; crewrite.  We omit the cache, since it's what we're discussing, and we also
;; omit the control structure, since it never changes.  This leaves us with:
;;
;;   - x, the term to rewrite
;;   - assms, the current assumptions we're rewriting with
;;   - iffp, the context we're in
;;   - blimit, the backchain limit (how hard to try when relieving hyps?)
;;   - rlimit, the rewrite limit (how many times can we successively rewrite x?)
;;   - anstack, the ancestors stack
;;
;; As these arguments change, we need to identify (1) it is sound to reuse the
;; previous results, and (2) when it is desirable to reuse the previous
;; results.
;;
;; Soundness.  A fundamental limitation of our implementation is that all
;; traces in the cache use the current assms structure.  It might be possible
;; to reimplement the cache to also reuse traces which contain fewer
;; assumptions, but this seemed too complicated.
;;
;; This restriction is not very severe.  The only place the rewriter changes
;; assumptions is when we encounter (if x y z).  Here, y is rewritten with the
;; extra assumption that x is true, and z is rewritten with the extra
;; assumption that x is false; when we encounter y and z, we create fresh,
;; empty caches which are thrown away after we are done rewriting y and z.  But
;; in all the other cases, the assms structure is unchanged and we can keep
;; using and adding to our evolving cache.
;;
;; Desirability.  A couple of ideas are implicit when we say "cache."  First,
;; we want to avoid expensive computation by remembering the work we've already
;; done.  Second, we want to know something like "using the cache does not
;; change our output term."
;;
;; Actually we want to take a more permissive view of the cache.  Arguments
;; like the backchain limit and rewrite limit are always changing as we recur,
;; and we don't want to throw out a whole lot of previous work just because it
;; was done with blimit 1000, and now we're at blimit 999.
;;
;;
;; Handling argument variation.
;;
;; RLIMIT.  Even though the rlimit can be reached if it is set low enough or
;; loopy rules are present, we think of hitting the rlimit as a degenerate
;; behavior.  In fact, the rewriter even prints out a warning if this occurs.
;; So in the caching code, we completely ignore the rlimit, even though this
;; could in principle cause a different term' to be produced.
;;
;; IFFP.  Suppose term has been rewritten to term' under equal and this result
;; has been cached.  Now suppose term is being rewritten under iff for the
;; first time.  We feel that it's fair to just rewrite term' under iff, instead
;; of starting with term.  This might lead to a different result, but we think
;; a "good" rewrite strategy shouldn't be bothered by this kind of variation,
;; and we would like to take advantage of the previous attempt.
;;
;; BLIMIT. There are two ways that the backchain limit can decrease:
;;
;;  (a) If the hyp has no explicit limit, the blimit is decreased by one;
;;  (b) Else, the blimit is decreased to min(explicit-limit, blimit-1).
;;
;; I think of explicit backchain limits as a technique to make rules "cheap"
;; even though they might have expensive hypotheses.  In fact, I have never
;; used a backchain limit over 3.  And, I don't expect the backchain limit to
;; ever be reached unless a "cheap" rule has fired to artificially lower it.
;;
;; Accordingly, I implement the following strategy for dealing with the blimit.
;; Until a case such as (b) is encountered, results are cached without regard
;; to the blimit.  This of course might violate "strict correctness" as even a
;; high blimit could be reached by ordinary rules, but I don't expect this case
;; to ever occur.  On the other hand, once we artificially lower the blimit, we
;; totally disable caching of rewrites.  This way, hyps which are to be
;; relieved "cheaply" are never cached, which shouldn't be a big deal since
;; they are "cheap" to relieve anyway.
;;
;; Of course, if we're relieving some hypothesis (foo x) with a backchain limit
;; of 1, and we have "(foo x) rewrites to (bar x)" in our cache, we still use
;; this fact even if it was obtained using a high backchain limit; we already
;; did the work, we might as well use it!
;;
;; ANSTACK.  Handling the ancestors stack is the most complicated thing we need
;; to do.  The problem here is that we can have diverging anstacks which
;; restrict different things.  That is, suppose we apply some rule of the form
;; (implies (and hyp1 hyp2) (equal lhs rhs)).  Then terms we reach while
;; backchaining to prove hyp1 will have hyp1 on their anstack, while terms we
;; reach while backchaining to prove hyp2 will have hyp2 on their anstack.
;; This "divergence" is potentially bad because each anstack will prevent
;; backchaining to relieve different sets of terms.  This makes caching
;; dangerous: we might cache a "poor" result becuase of anstack restrictions,
;; then reuse it in a later context where more backchaining would have been
;; permitted.
;;
;; Fortunately, it is somewhat rare for ancestors to prevent rewrites from
;; occurring, so we adopt a pretty simple strategy of not caching traces which
;; have failed because of ancestors.  More formally, let us introduce a new
;; notion of "ancestors-limited" rewrites.  We define this notion on a
;; per-rewriting-step basis:
;;
;;  - relieve-hyp is alimited if the ancestors-check causes it to fail, or if
;;    the attempt to rewrite its term fails and is alimited
;;  - relieve-hyps is alimited if any of its calls to relieve-hyp are alimited
;;  - match is alimited if its relieve-hyps fails and is alimited
;;  - matches is alimited if all of its matches fail and any of them is alimited
;;  - rule is alimited if all its matches fail and any of them is alimited
;;  - rules is alimited if all its rules fail and any of them is alimited
;;  - term is alimited if (1) simplification fails, (2) rules were tried, and
;;    some rule was alimited
;;  - termlist is alimited if any of its terms are alimited
;;
;; This definition allows us to cache some terms even when ancestor limits have
;; been hit in the course of rewriting them.  For example, if there are two
;; rules which can be used to simplify (foo x), and only one of them is
;; ancestor limited, we are rewriting (foo x) and ancestors prevent us from
;; applying a rule, but another rule can still be used to simplify foo.

;; (defthm range-of-update
;;   ;; BOZO move to utilities
;;   (equal (range (update key val map))
;;          (cons val (range map)))
;;   :hints(("Goal" :in-theory (enable update))))



(defun hons-lookup (key map)
  ;; Alias for lookup; gets redefined to hons-assoc-equal "under the hood" for bootstrapping
  (declare (xargs :guard (mapp map)))
  (lookup key map))

(defun hons-update (key val map)
  ;; Alias for update; gets redefined to hons-acons "under the hood" for bootstrapping
  (declare (xargs :guard (mapp map)))
  (cons (cons key val) map))



(defund rw.cachelinep (x)
  (declare (xargs :guard t))
  (and (consp x)
       (let ((eqltrace (car x))
             (ifftrace (cdr x)))
         (and (implies eqltrace
                       (and (rw.tracep eqltrace)
                            (equal (rw.trace->iffp eqltrace) nil)))
              (implies ifftrace
                       (and (rw.tracep ifftrace)
                            (equal (rw.trace->iffp ifftrace) t)))))))

(defund rw.cacheline (eqltrace ifftrace)
  (declare (xargs :guard (and (or (not eqltrace)
                                  (and (rw.tracep eqltrace)
                                       (equal (rw.trace->iffp eqltrace) nil)))
                              (or (not ifftrace)
                                  (and (rw.tracep ifftrace)
                                       (equal (rw.trace->iffp ifftrace) t))))))
  (cons eqltrace ifftrace))

(defund rw.cacheline->eqltrace (x)
  (declare (xargs :guard (rw.cachelinep x)))
  (car x))

(defund rw.cacheline->ifftrace (x)
  (declare (xargs :guard (rw.cachelinep x)))
  (cdr x))

(defthm booleanp-of-rw.cachelinep
  (equal (booleanp (rw.cachelinep x))
         t)
  :hints(("Goal" :in-theory (enable rw.cachelinep))))

(defthm forcing-rw.cachelinep-of-rw.cacheline
  (implies (force (and (or (not eqltrace)
                           (and (rw.tracep eqltrace)
                                (equal (rw.trace->iffp eqltrace) nil)))
                       (or (not ifftrace)
                           (and (rw.tracep ifftrace)
                                (equal (rw.trace->iffp ifftrace) t)))))
           (equal (rw.cachelinep (rw.cacheline eqltrace ifftrace))
                  t))
  :hints(("Goal" :in-theory (enable rw.cachelinep rw.cacheline))))

(defthm rw.cacheline->eqltrace-of-rw.cacheline
  (equal (rw.cacheline->eqltrace (rw.cacheline eqltrace ifftrace))
         eqltrace)
  :hints(("Goal" :in-theory (enable rw.cacheline rw.cacheline->eqltrace))))

(defthm rw.cacheline->ifftrace-of-rw.cacheline
  (equal (rw.cacheline->ifftrace (rw.cacheline eqltrace ifftrace))
         ifftrace)
  :hints(("Goal" :in-theory (enable rw.cacheline rw.cacheline->ifftrace))))

(defthm forcing-rw.tracep-of-rw.cacheline->eqltrace
  (implies (force (rw.cachelinep x))
           (equal (rw.tracep (rw.cacheline->eqltrace x))
                  (if (rw.cacheline->eqltrace x)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable rw.cacheline->eqltrace rw.cachelinep))))

(defthm forcing-rw.trace->iffp-of-rw.cacheline->eqltrace
  (implies (force (and (rw.cachelinep x)
                       (rw.cacheline->eqltrace x)))
           (equal (rw.trace->iffp (rw.cacheline->eqltrace x))
                  nil))
  :hints(("Goal" :in-theory (enable rw.cacheline->eqltrace rw.cachelinep))))

(defthm forcing-rw.tracep-of-rw.cacheline->ifftrace
  (implies (force (rw.cachelinep x))
           (equal (rw.tracep (rw.cacheline->ifftrace x))
                  (if (rw.cacheline->ifftrace x)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable rw.cacheline->ifftrace rw.cachelinep))))

(defthm forcing-rw.trace->iffp-of-rw.cacheline->ifftrace
  (implies (force (and (rw.cachelinep x)
                       (rw.cacheline->ifftrace x)))
           (equal (rw.trace->iffp (rw.cacheline->ifftrace x))
                  t))
  :hints(("Goal" :in-theory (enable rw.cacheline->ifftrace rw.cachelinep))))

(deflist rw.cacheline-listp (x)
  (rw.cachelinep x)
  :elementp-of-nil nil)



(defund rw.cacheline-assmsp (line assms)
  ;; BOZO probably get rid of this and change it to hypboxp
  (declare (xargs :guard (and (rw.cachelinep line)
                              (rw.assmsp assms))))
  (let ((ifftrace (rw.cacheline->ifftrace line))
        (eqltrace (rw.cacheline->eqltrace line)))
    (and (or (not ifftrace)
             (equal (rw.trace->hypbox ifftrace)
                    (rw.assms->hypbox assms)))
         (or (not eqltrace)
             (equal (rw.trace->hypbox eqltrace)
                    (rw.assms->hypbox assms))))))

(defthm booleanp-of-rw.cacheline-assmsp
  (equal (booleanp (rw.cacheline-assmsp line assms))
         t)
  :hints(("Goal" :in-theory (enable rw.cacheline-assmsp))))

(deflist rw.cacheline-list-assmsp (x assms)
  (rw.cacheline-assmsp x assms)
  :guard (and (rw.cacheline-listp x)
              (rw.assmsp assms)))

(defthm forcing-rw.trace->assms-of-rw.cacheline->ifftrace
  (implies (and (force (rw.cacheline->ifftrace x))
; Matt K. mod for v7-2: Don't force assumption below with free variable.
                (rw.cacheline-assmsp x assms))
           (equal (rw.trace->hypbox (rw.cacheline->ifftrace x))
                  (rw.assms->hypbox assms)))
  :hints(("Goal" :in-theory (enable rw.cacheline-assmsp))))

(defthm forcing-rw.trace->assms-of-rw.cacheline->eqltrace
  (implies (and (force (rw.cacheline->eqltrace x))
; Matt K. mod for v7-2: Don't force assumption below with free variable.
                (rw.cacheline-assmsp x assms))
           (equal (rw.trace->hypbox (rw.cacheline->eqltrace x))
                  (rw.assms->hypbox assms)))
  :hints(("Goal" :in-theory (enable rw.cacheline-assmsp))))

(defthm forcing-rw.cacheline-assmsp-of-rw.cacheline
  (implies (force (and (or (not eqltrace)
                           (equal (rw.trace->hypbox eqltrace)
                                  (rw.assms->hypbox assms)))
                       (or (not ifftrace)
                           (equal (rw.trace->hypbox ifftrace)
                                  (rw.assms->hypbox assms)))))
           (equal (rw.cacheline-assmsp (rw.cacheline eqltrace ifftrace) assms)
                  t))
  ;; BOZO ugly disables
  :hints(("Goal" :in-theory (enable rw.cacheline-assmsp rw.cacheline rw.cacheline->eqltrace rw.cacheline->ifftrace))))

(defthm rw.trace->assms-of-rw.cacheline->eqltrace-of-lookup
  (implies (and (rw.cacheline-list-assmsp (range data) assms)
                (rw.cacheline->eqltrace (cdr (lookup term data))))
           (equal (rw.trace->hypbox (rw.cacheline->eqltrace (cdr (lookup term data))))
                  (rw.assms->hypbox assms)))
  :hints(("Goal" :induct (cdr-induction data))))

(defthm rw.trace->assms-of-rw.cacheline->ifftrace-of-lookup
  (implies (and (rw.cacheline-list-assmsp (range data) assms)
                (rw.cacheline->ifftrace (cdr (lookup term data))))
           (equal (rw.trace->hypbox (rw.cacheline->ifftrace (cdr (lookup term data))))
                  (rw.assms->hypbox assms)))
  :hints(("Goal" :induct (cdr-induction data))))



(defund rw.cacheline-traces-okp (line defs)
  (declare (xargs :guard (and (rw.cachelinep line)
                              (definition-listp defs))))
  (let ((ifftrace (rw.cacheline->ifftrace line))
        (eqltrace (rw.cacheline->eqltrace line)))
    (and (or (not ifftrace)
             (rw.trace-okp ifftrace defs))
         (or (not eqltrace)
             (rw.trace-okp eqltrace defs)))))

(defthm booleanp-of-rw.cacheline-traces-okp
  (equal (booleanp (rw.cacheline-traces-okp line defs))
         t)
  :hints(("Goal" :in-theory (enable rw.cacheline-traces-okp))))

(deflist rw.cacheline-list-traces-okp (x defs)
  (rw.cacheline-traces-okp x defs)
  :guard (and (rw.cacheline-listp x)
              (definition-listp defs)))

(defthm forcing-rw.trace-okp-of-rw.cacheline->ifftrace
  (implies (force (and (rw.cacheline->ifftrace x)
                       (rw.cacheline-traces-okp x defs)))
           (equal (rw.trace-okp (rw.cacheline->ifftrace x) defs)
                  t))
  :hints(("Goal" :in-theory (enable rw.cacheline-traces-okp))))

(defthm forcing-rw.trace-okp-of-rw.cacheline->eqltrace
  (implies (force (and (rw.cacheline->eqltrace x)
                       (rw.cacheline-traces-okp x defs)))
           (equal (rw.trace-okp (rw.cacheline->eqltrace x) defs)
                  t))
  :hints(("Goal" :in-theory (e/d (rw.cacheline-traces-okp)
                                 (forcing-rw.trace-okp-of-rw.cacheline->ifftrace)))))

(defthm forcing-rw.cacheline-traces-okp-of-rw.cacheline
  (implies (force (and (or (not eqltrace)
                           (rw.trace-okp eqltrace defs))
                       (or (not ifftrace)
                           (rw.trace-okp ifftrace defs))))
           (equal (rw.cacheline-traces-okp (rw.cacheline eqltrace ifftrace) defs)
                  t))
  ;; BOZO ugly disables
  :hints(("Goal" :in-theory (enable rw.cacheline-traces-okp rw.cacheline rw.cacheline->eqltrace rw.cacheline->ifftrace))))

(defthm rw.trace-okp-of-rw.cacheline->eqltrace-of-lookup
  (implies (and (rw.cacheline-list-traces-okp (range data) defs)
                (rw.cacheline->eqltrace (cdr (lookup term data))))
           (equal (rw.trace-okp (rw.cacheline->eqltrace (cdr (lookup term data))) defs)
                  t))
  :hints(("Goal"
          :induct (cdr-induction data)
          :in-theory (disable (:executable-counterpart ACL2::force)))))

(defthm rw.trace-okp-of-rw.cacheline->ifftrace-of-lookup
  (implies (and (rw.cacheline-list-traces-okp (range data) defs)
                (rw.cacheline->ifftrace (cdr (lookup term data))))
           (equal (rw.trace-okp (rw.cacheline->ifftrace (cdr (lookup term data))) defs)
                  t))
  :hints(("Goal"
          :induct (cdr-induction data)
          :in-theory (disable (:executable-counterpart ACL2::force)))))




(defund rw.cacheline-atblp (line atbl)
  (declare (xargs :guard (and (rw.cachelinep line)
                              (logic.arity-tablep atbl))))
  (let ((ifftrace (rw.cacheline->ifftrace line))
        (eqltrace (rw.cacheline->eqltrace line)))
    (and (or (not ifftrace)
             (rw.trace-atblp ifftrace atbl))
         (or (not eqltrace)
             (rw.trace-atblp eqltrace atbl)))))

(defthm booleanp-of-rw.cacheline-atblp
  (equal (booleanp (rw.cacheline-atblp line atbl))
         t)
  :hints(("Goal" :in-theory (enable rw.cacheline-atblp))))

(deflist rw.cacheline-list-atblp (x atbl)
  (rw.cacheline-atblp x atbl)
  :guard (and (rw.cacheline-listp x)
              (logic.arity-tablep atbl)))

(defthm forcing-rw.trace-atblp-of-rw.cacheline->ifftrace
  (implies (force (and (rw.cacheline->ifftrace x)
                       (rw.cacheline-atblp x atbl)))
           (equal (rw.trace-atblp (rw.cacheline->ifftrace x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.cacheline-atblp))))

(defthm forcing-rw.trace-atblp-of-rw.cacheline->eqltrace
  (implies (force (and (rw.cacheline->eqltrace x)
                       (rw.cacheline-atblp x atbl)))
           (equal (rw.trace-atblp (rw.cacheline->eqltrace x) atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (rw.cacheline-atblp)
                                 (forcing-rw.trace-atblp-of-rw.cacheline->ifftrace)))))

(defthm forcing-rw.cacheline-atblp-of-rw.cacheline
  (implies (force (and (or (not eqltrace)
                           (rw.trace-atblp eqltrace atbl))
                       (or (not ifftrace)
                           (rw.trace-atblp ifftrace atbl))))
           (equal (rw.cacheline-atblp (rw.cacheline eqltrace ifftrace) atbl)
                  t))
  ;; BOZO ugly disables
  :hints(("Goal" :in-theory (enable rw.cacheline-atblp rw.cacheline rw.cacheline->eqltrace rw.cacheline->ifftrace))))

(defthm rw.trace-atblp-of-rw.cacheline->eqltrace-of-lookup
  (implies (and (rw.cacheline-list-atblp (range data) atbl)
                (rw.cacheline->eqltrace (cdr (lookup term data))))
           (equal (rw.trace-atblp (rw.cacheline->eqltrace (cdr (lookup term data))) atbl)
                  t))
  :hints(("Goal"
          :induct (cdr-induction data)
          :in-theory (disable (:executable-counterpart ACL2::force)))))

(defthm rw.trace-atblp-of-rw.cacheline->ifftrace-of-lookup
  (implies (and (rw.cacheline-list-atblp (range data) atbl)
                (rw.cacheline->ifftrace (cdr (lookup term data))))
           (equal (rw.trace-atblp (rw.cacheline->ifftrace (cdr (lookup term data))) atbl)
                  t))
  :hints(("Goal"
          :induct (cdr-induction data)
          :in-theory (disable (:executable-counterpart ACL2::force)))))




(defund rw.cacheline-env-okp (line defs thms atbl)
  (declare (xargs :guard (and (rw.cachelinep line)
                              (definition-listp defs)
                              (rw.cacheline-traces-okp line defs)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (let ((ifftrace (rw.cacheline->ifftrace line))
        (eqltrace (rw.cacheline->eqltrace line)))
    (and (or (not ifftrace)
             (rw.trace-env-okp ifftrace defs thms atbl))
         (or (not eqltrace)
             (rw.trace-env-okp eqltrace defs thms atbl)))))

(defthm booleanp-of-rw.cacheline-env-okp
  (equal (booleanp (rw.cacheline-env-okp line defs thms atbl))
         t)
  :hints(("Goal" :in-theory (enable rw.cacheline-env-okp))))

(deflist rw.cacheline-list-env-okp (x defs thms atbl)
  (rw.cacheline-env-okp x defs thms atbl)
  :guard (and (rw.cacheline-listp x)
              (definition-listp defs)
              (rw.cacheline-list-traces-okp x defs)
              (logic.formula-listp thms)
              (logic.arity-tablep atbl)))

(defthm forcing-rw.trace-env-okp-of-rw.cacheline->ifftrace
  (implies (force (and (rw.cacheline->ifftrace x)
                       (rw.cacheline-env-okp x defs thms atbl)))
           (equal (rw.trace-env-okp (rw.cacheline->ifftrace x) defs thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.cacheline-env-okp))))

(defthm forcing-rw.trace-env-okp-of-rw.cacheline->eqltrace
  (implies (force (and (rw.cacheline->eqltrace x)
                       (rw.cacheline-env-okp x defs thms atbl)))
           (equal (rw.trace-env-okp (rw.cacheline->eqltrace x) defs thms atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (rw.cacheline-env-okp)
                                 (forcing-rw.trace-env-okp-of-rw.cacheline->ifftrace)))))

(defthm forcing-rw.cacheline-env-okp-of-rw.cacheline
  (implies (force (and (or (not eqltrace)
                           (rw.trace-env-okp eqltrace defs thms atbl))
                       (or (not ifftrace)
                           (rw.trace-env-okp ifftrace defs thms atbl))))
           (equal (rw.cacheline-env-okp (rw.cacheline eqltrace ifftrace) defs thms atbl)
                  t))
  ;; BOZO ugly disables
  :hints(("Goal" :in-theory (enable rw.cacheline-env-okp rw.cacheline rw.cacheline->eqltrace rw.cacheline->ifftrace))))

(defthm rw.trace-env-okp-of-rw.cacheline->eqltrace-of-lookup
  (implies (and (rw.cacheline-list-env-okp (range data) defs thms atbl)
                (rw.cacheline->eqltrace (cdr (lookup term data))))
           (equal (rw.trace-env-okp (rw.cacheline->eqltrace (cdr (lookup term data))) defs thms atbl)
                  t))
  :hints(("Goal"
          :induct (cdr-induction data)
          :in-theory (disable (:executable-counterpart ACL2::force)))))

(defthm rw.trace-env-okp-of-rw.cacheline->ifftrace-of-lookup
  (implies (and (rw.cacheline-list-env-okp (range data) defs thms atbl)
                (rw.cacheline->ifftrace (cdr (lookup term data))))
           (equal (rw.trace-env-okp (rw.cacheline->ifftrace (cdr (lookup term data))) defs thms atbl)
                  t))
  :hints(("Goal"
          :induct (cdr-induction data)
          :in-theory (disable (:executable-counterpart ACL2::force)))))


(defmap :map (rw.cachemapp x)
        :key (logic.termp x)
        :val (rw.cachelinep x)
        :key-list (logic.term-listp x)
        :val-list (rw.cacheline-listp x)
        :val-of-nil nil)

;; (defthm forcing-rw.cachemapp-of-update
;;   ;; BOZO add something like this to defmap?
;;   (implies (force (and (logic.termp key)
;;                        (rw.cachelinep val)
;;                        (rw.cachemapp x)))
;;            (equal (rw.cachemapp (update key val x))
;;                   t))
;;   :hints(("Goal" :in-theory (enable update))))



(defund rw.cachemap-lhses-okp (x)
  (declare (xargs :guard (rw.cachemapp x)))
  (if (consp x)
      (and (let* ((term     (car (car x)))
                  (line     (cdr (car x)))
                  (eqltrace (rw.cacheline->eqltrace line))
                  (ifftrace (rw.cacheline->ifftrace line)))
             (and (or (not eqltrace)
                      (equal (rw.trace->lhs eqltrace) term))
                  (or (not ifftrace)
                      (equal (rw.trace->lhs ifftrace) term))))
           (rw.cachemap-lhses-okp (cdr x)))
    t))

(defthm rw.cachemap-lhses-okp-when-not-consp
  (implies (not (consp x))
           (equal (rw.cachemap-lhses-okp x)
                  t))
  :hints(("Goal" :in-theory (enable rw.cachemap-lhses-okp))))

(defthm rw.cachemap-lhses-okp-of-cons
  (equal (rw.cachemap-lhses-okp (cons a x))
         (and (let* ((term     (car a))
                     (line     (cdr a))
                     (eqltrace (rw.cacheline->eqltrace line))
                     (ifftrace (rw.cacheline->ifftrace line)))
                (and (or (not eqltrace)
                         (equal (rw.trace->lhs eqltrace) term))
                     (or (not ifftrace)
                         (equal (rw.trace->lhs ifftrace) term))))
              (rw.cachemap-lhses-okp x)))
  :hints(("Goal" :in-theory (enable rw.cachemap-lhses-okp))))

(defthm booleanp-of-rw.cachemap-lhses-okp
  (equal (booleanp (rw.cachemap-lhses-okp x))
         t)
  :hints(("Goal" :in-theory (enable rw.cachemap-lhses-okp))))

(defthm rw.trace->lhs-of-rw.cacheline->eqltrace-of-lookup
  (implies (and (rw.cachemap-lhses-okp data)
                (rw.cacheline->eqltrace (cdr (lookup term data))))
           (equal (rw.trace->lhs (rw.cacheline->eqltrace (cdr (lookup term data))))
                  term))
  :hints(("Goal" :induct (cdr-induction data))))

(defthm rw.trace->lhs-of-rw.cacheline->ifftrace-of-lookup
  (implies (and (rw.cachemap-lhses-okp data)
                (rw.cacheline->ifftrace (cdr (lookup term data))))
           (equal (rw.trace->lhs (rw.cacheline->ifftrace (cdr (lookup term data))))
                  term))
  :hints(("Goal" :induct (cdr-induction data))))





(defaggregate rw.cache
  (blockp data)
  :require ((booleanp-of-rw.cache->blockp   (booleanp blockp))
            (rw.cachemapp-of-rw.cache->data (rw.cachemapp data)))
  :legiblep nil)


(defund rw.cache-assmsp (cache assms)
  (declare (xargs :guard (and (rw.cachep cache)
                              (rw.assmsp assms))))
  (rw.cacheline-list-assmsp (range (rw.cache->data cache)) assms))

(defthm booleanp-of-rw.cache-assmsp
  (equal (booleanp (rw.cache-assmsp x assms))
         t)
  :hints(("Goal" :in-theory (enable rw.cache-assmsp))))


(defund rw.cache-traces-okp (cache defs)
  (declare (xargs :guard (and (rw.cachep cache)
                              (definition-listp defs))))
  (rw.cacheline-list-traces-okp (range (rw.cache->data cache)) defs))

(defthm booleanp-of-rw.cache-traces-okp
  (equal (booleanp (rw.cache-traces-okp cache defs))
         t)
  :hints(("Goal" :in-theory (enable rw.cache-traces-okp))))



(defund rw.cache-atblp (cache atbl)
  (declare (xargs :guard (and (rw.cachep cache)
                              (logic.arity-tablep atbl))))
  (rw.cacheline-list-atblp (range (rw.cache->data cache)) atbl))

(defthm booleanp-of-rw.cache-atblp
  (equal (booleanp (rw.cache-atblp cache atbl))
         t)
  :hints(("Goal" :in-theory (enable rw.cache-atblp))))


(defund rw.cache-env-okp (cache defs thms atbl)
  (declare (xargs :guard (and (rw.cachep cache)
                              (definition-listp defs)
                              (rw.cache-traces-okp cache defs)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))
                  :guard-hints (("Goal" :in-theory (enable rw.cache-traces-okp)))))
  (rw.cacheline-list-env-okp (range (rw.cache->data cache)) defs thms atbl))

(defthm booleanp-of-rw.cache-env-okp
  (equal (booleanp (rw.cache-env-okp cache defs thms atbl))
         t)
  :hints(("Goal" :in-theory (enable rw.cache-env-okp))))



(defund rw.cache-lhses-okp (cache)
  (declare (xargs :guard (rw.cachep cache)))
  (rw.cachemap-lhses-okp (rw.cache->data cache)))

(defthm booleanp-of-rw.cache-lhses-okp
  (equal (booleanp (rw.cache-lhses-okp cache))
         t)
  :hints(("Goal" :in-theory (enable rw.cache-lhses-okp))))



(defund rw.set-blockedp (blockedp cache)
  (declare (xargs :guard (and (booleanp blockedp)
                              (rw.cachep cache))))
  (rw.cache blockedp (rw.cache->data cache)))

(defthm forcing-rw.cachep-of-rw.set-blockedp
  (implies (force (and (booleanp blockedp)
                       (rw.cachep cache)))
           (equal (rw.cachep (rw.set-blockedp blockedp cache))
                  t))
  :hints(("Goal" :in-theory (enable rw.set-blockedp))))

(defthm forcing-rw.cache-assmsp-of-rw.set-blockedp
  (implies (force (and (booleanp blockedp)
                       (rw.cache-assmsp cache assms)))
           (equal (rw.cache-assmsp (rw.set-blockedp blockedp cache) assms)
                  t))
  :hints(("Goal" :in-theory (enable rw.set-blockedp rw.cache-assmsp))))

(defthm forcing-rw.cache-traces-okp-of-rw.set-blockedp
  (implies (force (and (booleanp blockedp)
                       (rw.cache-traces-okp cache defs)))
           (equal (rw.cache-traces-okp (rw.set-blockedp blockedp cache) defs)
                  t))
  :hints(("Goal" :in-theory (enable rw.set-blockedp rw.cache-traces-okp))))

(defthm forcing-rw.cache-atblp-of-rw.set-blockedp
  (implies (force (and (booleanp blockedp)
                       (rw.cache-atblp cache atbl)))
           (equal (rw.cache-atblp (rw.set-blockedp blockedp cache) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.set-blockedp rw.cache-atblp))))

(defthm forcing-rw.cache-env-okp-of-rw.set-blockedp
  (implies (force (and (booleanp blockedp)
                       (rw.cache-env-okp cache defs thms atbl)))
           (equal (rw.cache-env-okp (rw.set-blockedp blockedp cache) defs thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.set-blockedp rw.cache-env-okp))))

(defthm forcing-rw.cache-lhses-okp-of-rw.set-blockedp
  (implies (force (and (booleanp blockedp)
                       (rw.cache-lhses-okp cache)))
           (equal (rw.cache-lhses-okp (rw.set-blockedp blockedp cache))
                  t))
  :hints(("Goal" :in-theory (enable rw.set-blockedp rw.cache-lhses-okp))))




(defund rw.cache-update (term trace iffp cache)
  ;; We make a special exception so that rewriting to a constant is permitted
  ;; even when the cache is blocked.
  (declare (xargs :guard (and (logic.termp term)
                              (rw.tracep trace)
                              (equal iffp (rw.trace->iffp trace))
                              (rw.cachep cache))))
  (let ((blockp (rw.cache->blockp cache))
        (data   (rw.cache->data cache)))
    (if (and blockp
             (not (logic.constantp (rw.trace->rhs trace))))
        ;; Not allowed to change the cache.
        cache
    ;; Allowed to write to the cache.
    (let* ((entry          (hons-lookup term data))
           (new-cache-line (if iffp
                               (rw.cacheline (and entry (rw.cacheline->eqltrace (cdr entry))) trace)
                             (rw.cacheline trace (and entry (rw.cacheline->ifftrace (cdr entry))))))
           (new-data       (hons-update term new-cache-line data)))
      (rw.cache blockp new-data)))))

(defthm forcing-rw.cachep-of-rw.cache-update
  (implies (force (and (logic.termp term)
                       (rw.tracep trace)
                       (equal iffp (rw.trace->iffp trace))
                       (rw.cachep cache)))
           (equal (rw.cachep (rw.cache-update term trace iffp cache))
                  t))
  :hints(("Goal" :in-theory (enable rw.cache-update))))

(defthm forcing-rw.cache-assmsp-of-rw.cache-update
  (implies (force (and (logic.termp term)
                       (rw.tracep trace)
                       (equal iffp (rw.trace->iffp trace))
                       (rw.cachep cache)
                       (equal (rw.trace->hypbox trace)
                              (rw.assms->hypbox assms))
                       (rw.cache-assmsp cache assms)))
           (equal (rw.cache-assmsp (rw.cache-update term trace iffp cache) assms)
                  t))
  :hints(("Goal" :in-theory (enable rw.cache-update rw.cache-assmsp))))

(defthm forcing-rw.cache-traces-okp-of-rw.cache-update
  (implies (force (and (logic.termp term)
                       (rw.tracep trace)
                       (equal iffp (rw.trace->iffp trace))
                       (rw.cachep cache)
                       (rw.trace-okp trace defs)
                       (rw.cache-traces-okp cache defs)))
           (equal (rw.cache-traces-okp (rw.cache-update term trace iffp cache) defs)
                  t))
  :hints(("Goal" :in-theory (enable rw.cache-update rw.cache-traces-okp))))

(defthm forcing-rw.cache-atblp-of-rw.cache-update
  (implies (force (and (logic.termp term)
                       (rw.tracep trace)
                       (equal iffp (rw.trace->iffp trace))
                       (rw.cachep cache)
                       (rw.trace-atblp trace atbl)
                       (rw.cache-atblp cache atbl)))
           (equal (rw.cache-atblp (rw.cache-update term trace iffp cache) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.cache-update rw.cache-atblp))))

(defthm forcing-rw.cache-env-okp-of-rw.cache-update
  (implies (force (and (logic.termp term)
                       (rw.tracep trace)
                       (equal iffp (rw.trace->iffp trace))
                       (rw.cachep cache)
                       (rw.trace-env-okp trace defs thms atbl)
                       (rw.cache-env-okp cache defs thms atbl)))
           (equal (rw.cache-env-okp (rw.cache-update term trace iffp cache) defs thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.cache-update rw.cache-env-okp))))

(defthm forcing-rw.cache-lhses-okp-of-rw.cache-update
  (implies (force (and (logic.termp term)
                       (rw.tracep trace)
                       (equal iffp (rw.trace->iffp trace))
                       (rw.cachep cache)
                       (equal (rw.trace->lhs trace) term)
                       (rw.cache-lhses-okp cache)))
           (equal (rw.cache-lhses-okp (rw.cache-update term trace iffp cache))
                  t))
  :hints(("Goal" :in-theory (enable rw.cache-update rw.cache-lhses-okp))))





(defund rw.cache-lookup (term iffp cache)
  (declare (xargs :guard (and (logic.termp term)
                              (booleanp iffp)
                              (rw.cachep cache))))
  (let ((entry (hons-lookup term (rw.cache->data cache))))
    (and entry
         (if iffp
             (rw.cacheline->ifftrace (cdr entry))
           (rw.cacheline->eqltrace (cdr entry))))))

(defthm forcing-rw.tracep-of-rw.cache-lookup
  (implies (force (and (rw.cache-lookup term iffp cache)
                       (logic.termp term)
                       (rw.cachep cache)))
           (equal (rw.tracep (rw.cache-lookup term iffp cache))
                  t))
  :hints(("Goal" :in-theory (enable rw.cache-lookup))))

(defthm forcing-rw.trace->iffp-of-rw.cache-lookup
  (implies (force (and (rw.cache-lookup term iffp cache)
                       (logic.termp term)
                       (rw.cachep cache)
                       (booleanp iffp)))
           (equal (rw.trace->iffp (rw.cache-lookup term iffp cache))
                  iffp))
  :hints(("Goal" :in-theory (enable rw.cache-lookup))))

(defthm forcing-rw.trace->hypbox-of-rw.cache-lookup
  (implies (force (and (rw.cache-lookup term iffp cache)
                       (logic.termp term)
                       (rw.cachep cache)
                       (booleanp iffp)
                       (rw.cache-assmsp cache assms)))
           (equal (rw.trace->hypbox (rw.cache-lookup term iffp cache))
                  (rw.assms->hypbox assms)))
  :hints(("Goal" :in-theory (enable rw.cache-lookup rw.cache-assmsp))))

(defthm forcing-rw.trace->lhs-of-rw.cache-lookup
  (implies (force (and (rw.cache-lookup term iffp cache)
                       (logic.termp term)
                       (rw.cachep cache)
                       (booleanp iffp)
                       (rw.cache-lhses-okp cache)))
           (equal (rw.trace->lhs (rw.cache-lookup term iffp cache))
                  term))
  :hints(("Goal" :in-theory (enable rw.cache-lookup rw.cache-lhses-okp))))

(defthm forcing-rw.trace-okp-of-rw.cache-lookup
  (implies (force (and (rw.cache-lookup term iffp cache)
                       (logic.termp term)
                       (rw.cachep cache)
                       (booleanp iffp)
                       (rw.cache-traces-okp cache defs)))
           (equal (rw.trace-okp (rw.cache-lookup term iffp cache) defs)
                  t))
  :hints(("Goal" :in-theory (enable rw.cache-lookup rw.cache-traces-okp))))

(defthm forcing-rw.trace-atblp-of-rw.cache-lookup
  (implies (force (and (rw.cache-lookup term iffp cache)
                       (logic.termp term)
                       (rw.cachep cache)
                       (booleanp iffp)
                       (rw.cache-atblp cache atbl)))
           (equal (rw.trace-atblp (rw.cache-lookup term iffp cache) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.cache-lookup rw.cache-atblp))))

(defthm forcing-rw.trace-env-okp-of-rw.cache-lookup
  (implies (force (and (rw.cache-lookup term iffp cache)
                       (logic.termp term)
                       (rw.cachep cache)
                       (booleanp iffp)
                       (rw.cache-env-okp cache defs thms atbl)))
           (equal (rw.trace-env-okp (rw.cache-lookup term iffp cache) defs thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.cache-lookup rw.cache-env-okp))))




(defund rw.empty-cache ()
  (declare (xargs :guard t))
  (rw.cache nil nil))

(in-theory (disable (:executable-counterpart rw.empty-cache)))

(defthm rw.cachep-of-rw.empty-cache
  (equal (rw.cachep (rw.empty-cache))
         t)
  :hints(("Goal" :in-theory (enable rw.empty-cache))))

(defthm rw.cache-assmsp-of-rw.empty-cache
  (equal (rw.cache-assmsp (rw.empty-cache) assms)
         t)
  :hints(("Goal" :in-theory (enable rw.empty-cache rw.cache-assmsp))))

(defthm rw.cache-traces-okp-of-rw.empty-cache
  (equal (rw.cache-traces-okp (rw.empty-cache) defs)
         t)
  :hints(("Goal" :in-theory (enable rw.empty-cache rw.cache-traces-okp))))

(defthm rw.cache-atblp-of-rw.empty-cache
  (equal (rw.cache-atblp (rw.empty-cache) atbl)
         t)
  :hints(("Goal" :in-theory (enable rw.empty-cache rw.cache-atblp))))

(defthm rw.cache-env-okp-of-rw.empty-cache
  (equal (rw.cache-env-okp (rw.empty-cache) defs thms atbl)
         t)
  :hints(("Goal" :in-theory (enable rw.empty-cache rw.cache-env-okp))))

(defthm rw.cache-lhses-okp-rw.empty-cache
  (equal (rw.cache-lhses-okp (rw.empty-cache))
         t)
  :hints(("Goal" :in-theory (enable rw.empty-cache rw.cache-lhses-okp))))




(defund rw.maybe-update-cache (condition term trace iffp cache)
  ;; We can't just use an alias for if, because we need to update the cache
  ;; lazily
  (declare (xargs :guard (and (logic.termp term)
                              (rw.cachep cache)
                              (or (not condition)
                                  (and (rw.tracep trace)
                                       (equal (rw.trace->iffp trace) iffp)
                                       (equal (rw.trace->lhs trace) term))))))
  (if condition
      (rw.cache-update term trace iffp cache)
    cache))

(defthm forcing-rw.cachep-of-rw.maybe-update-cache
  (implies (force (and (logic.termp term)
                       (rw.cachep cache)
                       (or (not condition)
                           (and (rw.tracep trace)
                                (equal (rw.trace->iffp trace) iffp)))))
           (equal (rw.cachep (rw.maybe-update-cache condition term trace iffp cache))
                  t))
  :hints(("Goal" :in-theory (enable rw.maybe-update-cache))))

(defthm forcing-rw.cache-assmsp-of-rw.maybe-update-cache
   (implies (force (and (logic.termp term)
                        (rw.cachep cache)
                        (rw.cache-assmsp cache assms)
                        (or (not condition)
                            (and (rw.tracep trace)
                                 (equal (rw.trace->iffp trace) iffp)
                                 (equal (rw.trace->hypbox trace)
                                        (rw.assms->hypbox assms))))))
            (equal (rw.cache-assmsp (rw.maybe-update-cache condition term trace iffp cache) assms)
                   t))
   :hints(("Goal" :in-theory (enable rw.maybe-update-cache))))

(defthm forcing-rw.cache-traces-okp-of-rw.maybe-update-cache
  (implies (force (and (logic.termp term)
                       (rw.cachep cache)
                       (rw.cache-traces-okp cache defs)
                       (or (not condition)
                           (and (rw.tracep trace)
                                (rw.trace-okp trace defs)
                                (equal (rw.trace->iffp trace) iffp)))))
           (equal (rw.cache-traces-okp (rw.maybe-update-cache condition term trace iffp cache) defs)
                  t))
  :hints(("Goal" :in-theory (enable rw.maybe-update-cache))))

(defthm forcing-rw.cache-atblp-of-rw.maybe-update-cache
  (implies (force (and (logic.termp term)
                       (rw.cachep cache)
                       (rw.cache-atblp cache atbl)
                       (or (not condition)
                           (and (rw.tracep trace)
                                (rw.trace-atblp trace atbl)
                                (equal (rw.trace->iffp trace) iffp)))))
           (equal (rw.cache-atblp (rw.maybe-update-cache condition term trace iffp cache) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.maybe-update-cache))))

(defthm forcing-rw.cache-env-okp-of-rw.maybe-update-cache
  (implies (force (and (logic.termp term)
                       (rw.cachep cache)
                       (rw.cache-env-okp cache defs thms atbl)
                       (or (not condition)
                           (and (rw.tracep trace)
                                (rw.trace-env-okp trace defs thms atbl)
                                (equal (rw.trace->iffp trace) iffp)))))
           (equal (rw.cache-env-okp (rw.maybe-update-cache condition term trace iffp cache) defs thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.maybe-update-cache))))

(defthm forcing-rw.cache-lhses-okp-of-rw.maybe-update-cache
  (implies (force (and (logic.termp term)
                       (rw.cachep cache)
                       (rw.cache-lhses-okp cache)
                       (or (not condition)
                           (and (rw.tracep trace)
                                (equal (rw.trace->iffp trace) iffp)
                                (equal (rw.trace->lhs trace) term)))))
           (equal (rw.cache-lhses-okp (rw.maybe-update-cache condition term trace iffp cache))
                  t))
  :hints(("Goal" :in-theory (enable rw.maybe-update-cache))))


