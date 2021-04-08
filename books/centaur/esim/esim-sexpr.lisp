; ESIM Symbolic Hardware Simulator
; Copyright (C) 2008-2015 Centaur Technology
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


; esim-sexpr.lisp -- efficient symbolic simulator for E modules
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "esim-paths")
(include-book "esim-sexpr-support")
(include-book "std/strings/strsubst" :dir :system)
(include-book "std/strings/substrp" :dir :system)
(include-book "centaur/misc/ap" :dir :system)
(include-book "centaur/4v-sexpr/sexpr-fixpoint" :dir :system)
(include-book "centaur/4v-sexpr/sexpr-to-faig" :dir :system)
(include-book "centaur/4v-sexpr/sexpr-equivs" :dir :system)
(local (include-book "esim-sexpr-support-thms"))
(local (include-book "centaur/4v-sexpr/sexpr-advanced" :dir :system))
(local (in-theory (disable* set::double-containment)))
(set-well-founded-relation nat-list-<)

(defxdoc esim
  :parents (hardware-verification)
  :short "ESIM is a simple, hierarchical, bit-level, cycle-based,
register-transfer level hardware description language.  It is based on a clean,
monotonic four-valued logic (see @(see acl2::4v)) and features strong support
for symbolic simulation with @(see gl::gl)."

  :long "<box><p><b>Note:</b> ESIM is no longer being actively developed.  You
will probably want to instead see its successor, @(see sv).</p></box>

<p>ESIM is a bit-level ``back-end'' for carrying out hardware verification with
ACL2.  It consists of:</p>

<ul>

<li>A simplistic, bit-level module representation, ``E modules,'' which are
typically produced from Verilog designs using @(see vl2014::defmodules).</li>

<li>A family of functions for ``stepping'' an E module to compute expressions
that capture its next-state and outputs as @(see 4v-sexprs) or as @(see faig)s;
see @(see esim-steps).</li>

<li>Mechanisms for describing symbolic runs of a module over multiple clock
phases, such as @(see symbolic-test-vectors).</li>

</ul>

<p>There is a @(see esim-tutorial) that provides a hands-on guide for how to
use @(see vl), @(see esim), and @(see gl) together to verify some simple
hardware designs.</p>

<p>Aside from the tutorial, ESIM is not very well documented.  An early version
of E is described somewhat in:</p>

<p>Warren A. Hunt, Jr. and Sol Swords.  <a
href='http://dx.doi.org/10.1007/978-3-642-02658-4_28'>Centaur technology media
unit verification.  Case study: Floating point addition.</a> in Computer Aided
Verification (CAV '09), June 2009.</p>")

(defxdoc esim-tutorial
  :parents (esim)
  :short "The @(see esim) hardware verification tutorial."

  :long "<p>The ESIM tutorial walks through the verification of some very
simple hardware designs using Centaur's ESIM books.  These hardware designs are
all contrived and are far simpler than real hardware.  But this makes them easy
to understand and verify.</p>

<p>The ESIM tutorial is meant to be followed along with interactively.  To
begin, please go to this file:</p>

@({
centaur/esim/tutorial/intro.lisp
})

<p>in your ACL2 books directory (sometimes called @(':dir :system')).</p>")


(defconst *esim-sexpr-rewrite* t)


(defsection sexpr-pat-alist-translate

  ;; Old-pat and new-pat should be similarly shaped.  For each corrseponding atom
  ;; A in old-pat and B in new-pat, map B to the binding of A in alist.
  (defund sexpr-pat-alist-translate (old-pat new-pat alist acc)
    (declare (Xargs :guard (data-for-patternp old-pat new-pat)))
    (if old-pat
        (if (atom old-pat)
            (cons (cons new-pat
                        ;; [Jared]: This was previous 4v-sexpr-alist-lookup but
                        ;; now I just use hons-get because our NIL evaluates to X
                        ;; convention means we don't need anything special
                        (cdr (hons-get old-pat alist)))
                  acc)
          (sexpr-pat-alist-translate
           (car old-pat) (car new-pat) alist
           (sexpr-pat-alist-translate
            (cdr old-pat) (cdr new-pat) alist acc)))
      acc))

  (local (in-theory (enable sexpr-pat-alist-translate)))

  (defthm true-listp-sexpr-pat-alist-translate
    (equal (true-listp (sexpr-pat-alist-translate old new al acc))
           (true-listp acc)))

  (local (defun sexpr-pat-alist-translate-to-append-ind (p1 p2 al acc)
           (if p1
               (if (atom p1)
                   (list p2 al acc)
                 (list (sexpr-pat-alist-translate-to-append-ind
                        (car p1) (car p2) al
                        (sexpr-pat-alist-translate (cdr p1) (cdr p2) al acc))
                       (sexpr-pat-alist-translate-to-append-ind
                        (cdr p1) (cdr p2) al acc)
                       (sexpr-pat-alist-translate-to-append-ind
                        (car p1) (car p2) al
                        (sexpr-pat-alist-translate (cdr p1) (cdr p2) al nil))))
             acc)))

  (defthm sexpr-pat-alist-translate-to-append
    (implies (syntaxp (not (equal acc ''nil)))
             (equal (sexpr-pat-alist-translate p1 p2 al acc)
                    (append (sexpr-pat-alist-translate p1 p2 al nil)
                            acc)))
    :hints (("goal" :induct (sexpr-pat-alist-translate-to-append-ind
                             p1 p2 al acc)
             :expand ((:free (acc) (sexpr-pat-alist-translate p1 p2 al acc))))))

  (defthm sexpr-pat-alist-translate-compose-alist
    (equal (sexpr-pat-alist-translate p1 p2 (4v-sexpr-compose-alist al env) nil)
           (4v-sexpr-compose-alist (sexpr-pat-alist-translate p1 p2 al nil) env)))

  (defthm sexpr-pat-alist-translate-compose-with-rw-alist
    (equal (sexpr-pat-alist-translate p1 p2 (4v-sexpr-compose-with-rw-alist al env) nil)
           (4v-sexpr-compose-with-rw-alist (sexpr-pat-alist-translate p1 p2 al nil) env)))

  (defthm sexpr-pat-alist-translate-of-append-when-keys-subset
    (implies (subsetp-equal (pat-flatten1 p1) (alist-keys a))
             (equal (sexpr-pat-alist-translate p1 p2 (append a b) nil)
                    (sexpr-pat-alist-translate p1 p2 a nil)))
    :hints(("Goal" :in-theory (enable subsetp-equal))))


  (defthm sexpr-pat-alist-translate-of-append-when-keys-not-intersecting
    (implies (not (intersectp-equal (pat-flatten1 p1) (alist-keys a)))
             (equal (sexpr-pat-alist-translate p1 p2 (append a b) nil)
                    (sexpr-pat-alist-translate p1 p2 b nil)))
    :hints(("Goal" :in-theory (enable intersectp-equal))))

  (defthm hons-assoc-equal-sexpr-pat-alist-translate
    (implies (and (similar-patternsp (double-rewrite oldpat)
                                     (double-rewrite newpat)))
             (iff (hons-assoc-equal key (sexpr-pat-alist-translate
                                         oldpat newpat al acc))
                  (or (member-equal key (pat-flatten1 newpat))
                      (hons-assoc-equal key acc)))))

  (defthm alist-keys-sexpr-pat-alist-translate
    (implies (similar-patternsp (double-rewrite p1) (double-rewrite p2))
             (equal (alist-keys (sexpr-pat-alist-translate p1 p2 al acc))
                    (append (pat-flatten1 p2) (alist-keys acc))))))




;; Our primitive modules really just have their next-state/output/internal
;; signal alists recorded inside them, so eapply-sexpr just returns them.
(defun eapply-sexpr (x)
  (declare (xargs :guard t))
  (mv (gpl :nst x)
      (gpl :out x)
      (gpl :int x)))



(defsection mod-varmap

  ;; Collects an alist mapping each atom in pat to a distinct natural number,
  ;; avoiding duplication.
  (defun pattern-to-indices (pat acc idx)
    (declare (xargs :guard (acl2-numberp idx)))
    (b* (((when (not pat)) (mv acc idx))
         ((when (atom pat))
          (if (hons-get pat acc)
              (mv acc idx)
            (mv (hons-acons pat idx acc) (+ 1 idx))))
         ((mv acc idx)
          (pattern-to-indices (cdr pat) acc idx)))
      (pattern-to-indices (car pat) acc idx)))

  (local
   (defthm numberp-pattern-to-indices-idx
     (implies (acl2-numberp idx)
              (acl2-numberp
               (mv-nth 1 (pattern-to-indices pat acc idx))))))

  ;; Collects an alist mapping each atom in the inputs and outputs of the
  ;; occurrences to distinct natural numbers, avoiding duplication.
  (defun esim-sexpr-indices-occs (mod occnames acc idx)
    (declare (xargs :guard (acl2-numberp idx)))
    (if (atom occnames)
        (mv acc idx)
      (b* ((occ (cdr (hons-get (car occnames) (occmap mod))))
           ((mv acc idx) (pattern-to-indices (gpl :i occ) acc idx))
           ((mv acc idx) (pattern-to-indices (gpl :o occ) acc idx)))
        (esim-sexpr-indices-occs mod (cdr occnames) acc idx))))




  (defun mod-varmap (mod)
    (declare (Xargs :guard t))
    (b* (((mv acc idx) (pattern-to-indices (gpl :i mod) nil 0))
         ((mv acc idx) (pattern-to-indices (mod-state mod) acc idx))
         ((mv acc &)   (esim-sexpr-indices-occs
                        mod (alist-keys (occmap mod))
                        acc idx)))
      acc))


  (defthm natp-pattern-to-indices
    (implies (natp idx)
             (natp (mv-nth 1 (pattern-to-indices pat acc idx))))
    :rule-classes :type-prescription)

  (defthm 4v-nsexpr-alist-p-pattern-to-indices
    (implies (natp idx)
             (equal (4v-nsexpr-alist-p
                     (mv-nth 0 (pattern-to-indices pat acc idx)))
                    (4v-nsexpr-alist-p acc))))

  (defthm natp-esim-sexpr-indices-occs
    (implies (natp idx)
             (natp (mv-nth 1 (esim-sexpr-indices-occs mod occs acc idx))))
    :rule-classes :type-prescription)

  (defthm 4v-nsexpr-alist-p-esim-sexpr-indices-occs
    (implies (natp idx)
             (equal (4v-nsexpr-alist-p
                     (mv-nth 0 (esim-sexpr-indices-occs mod occs acc idx)))
                    (4v-nsexpr-alist-p acc))))

  (defthm 4v-nsexpr-alist-p-mod-varmap
    (4v-nsexpr-alist-p (mod-varmap mod)))

  (in-theory (disable mod-varmap))

  (defthm sexpr-var-key-alistp-pattern-to-indices
    (iff (sexpr-var-key-alistp (mv-nth 0 (pattern-to-indices pat acc idx)))
         (sexpr-var-key-alistp acc)))

  (defthm sexpr-varp-idx-pattern-to-indices
    (implies (and idx (not (consp idx)))
             (and (mv-nth 1 (pattern-to-indices pat acc idx))
                  (not (consp (mv-nth 1 (pattern-to-indices pat acc idx))))))
    :rule-classes :type-prescription)

  (defthm sexpr-var-val-alistp-pattern-to-indices
    (implies (and idx (not (consp idx)))
             (iff (sexpr-var-val-alistp (mv-nth 0 (pattern-to-indices pat acc idx)))
                  (sexpr-var-val-alistp acc))))

  (defthm sexpr-var-key-alistp-esim-sexpr-indices-occs
    (iff (sexpr-var-key-alistp (mv-nth 0 (esim-sexpr-indices-occs
                                          mod occs acc idx)))
         (sexpr-var-key-alistp acc)))

  (defthm sexpr-varp-idx-esim-sexpr-indices-occs
    (implies (and idx (not (consp idx)))
             (and (mv-nth 1 (esim-sexpr-indices-occs mod occs acc idx))
                  (not (consp (mv-nth 1 (esim-sexpr-indices-occs mod occs acc idx))))))
    :rule-classes :type-prescription)

  (defthm sexpr-var-val-alistp-esim-sexpr-indices-occs
    (implies (and idx (not (consp idx)))
             (iff (sexpr-var-val-alistp (mv-nth 0 (esim-sexpr-indices-occs mod occs acc idx)))
                  (sexpr-var-val-alistp acc))))




  (defun max-list (x)
    (if (atom x)
        -1
      (max (car x)
           (max-list (cdr x)))))

  (defthm max-alist-vals-pattern-to-indices
    (implies (and (natp idx)
                  (< (max-list (alist-vals acc)) idx))
             (mv-let (alist idx)
               (pattern-to-indices pat acc idx)
               (< (max-list (alist-vals alist)) idx)))
    :rule-classes (:rewrite :linear))

  (local
   (defthm not-hons-rassoc-equal-when-above-max
     (implies (and (natp idx)
                   (< (max-list (alist-vals acc)) idx))
              (not (hons-rassoc-equal idx acc)))
     :hints(("Goal" :in-theory (enable alist-vals
                                       hons-rassoc-equal)))))

  (defthm no-duplicate-vals-pattern-to-indices
    (implies (and (natp idx)
                  (< (max-list (alist-vals acc)) idx)
                  (no-duplicatesp-equal (alist-vals acc)))
             (no-duplicatesp-equal
              (alist-vals (mv-nth 0 (pattern-to-indices pat acc idx))))))

  (defthm max-alist-vals-esim-sexpr-indices-occs
    (implies (and (natp idx)
                  (< (max-list (alist-vals acc)) idx))
             (mv-let (alist idx)
               (esim-sexpr-indices-occs mod occs acc idx)
               (< (max-list (alist-vals alist)) idx)))
    :rule-classes (:rewrite :linear))

  (defthm no-duplicate-vals-esim-sexpr-indices-occs
    (implies (and (natp idx)
                  (< (max-list (alist-vals acc)) idx)
                  (no-duplicatesp-equal (alist-vals acc)))
             (no-duplicatesp-equal
              (alist-vals (mv-nth 0 (esim-sexpr-indices-occs mod occs acc
                                                             idx))))))


  (defthm no-duplicate-keys-pattern-to-indices
    (iff (no-duplicatesp-equal
          (alist-keys (mv-nth 0 (pattern-to-indices pat acc idx))))
         (no-duplicatesp-equal (alist-keys acc))))

  (defthm no-duplicate-keys-esim-sexpr-indices-occs
    (iff (no-duplicatesp-equal
          (alist-keys (mv-nth 0 (esim-sexpr-indices-occs mod occs acc idx))))
         (no-duplicatesp-equal (alist-keys acc))))

  (defthm alist-keys-pattern-to-indices
    (set-equiv (alist-keys (mv-nth 0 (pattern-to-indices pat acc idx)))
                (append (pat-flatten1 pat) (alist-keys acc)))
    :hints (("goal"
             :induct t
             :in-theory (enable pat-flatten1))
            (witness :ruleset set-equiv-witnessing)))


  (defthm alist-keys-esim-sexpr-indices-occs
    (set-equiv (alist-keys (mv-nth 0 (esim-sexpr-indices-occs mod occs acc idx)))
                (append (collect-signal-list
                         :o (occs-for-names occs mod))
                        (collect-signal-list
                         :i (occs-for-names occs mod))
                        (alist-keys acc)))
    :hints (("goal" :induct t :do-not-induct t
             :in-theory (enable fal-extract))
            (witness :ruleset set-equiv-witnessing))))



(defmacro estime (form &key name (mintime '1) minalloc)
    ;; Same as cwtime, but defaults to 1 second mintime.
    `(cwtime ,form :name ,name :mintime ,mintime :minalloc ,minalloc))




(defsection 4v-sexpr-alist-extract

  (defthm 4v-sexpr-alist-extract-append-keys
    (equal (4v-sexpr-alist-extract (append a b) c)
           (append (4v-sexpr-alist-extract a c)
                   (4v-sexpr-alist-extract b c))))

  (defthm 4v-sexpr-alist-extract-append-vals-when-keys-subset
    (implies (subsetp-equal keys (alist-keys a))
             (equal (4v-sexpr-alist-extract keys (append a b))
                    (4v-sexpr-alist-extract keys a)))
    :hints(("Goal" :in-theory (enable 4v-sexpr-alist-extract
                                      subsetp-equal))))

  (defthm 4v-sexpr-alist-extract-append-vals-when-keys-not-intersecting
    (implies (not (intersectp-equal keys (alist-keys a)))
             (equal (4v-sexpr-alist-extract keys (append a b))
                    (4v-sexpr-alist-extract keys b)))
    :hints(("Goal" :in-theory (enable 4v-sexpr-alist-extract
                                      intersectp-equal))))



  (defthm 4v-sexpr-alist-extract-of-pat->al
    (implies (and (similar-patternsp (double-rewrite p1)
                                     (double-rewrite p2))
                  (no-duplicatesp-equal (pat-flatten1 p1)))
             (equal (4v-sexpr-alist-extract
                     (pat-flatten1 p1)
                     (pat->al p1 p2 nil))
                    (pat->al p1 p2 nil))))


  (defthm alist-keys-4v-sexpr-alist-extract
    (Equal (alist-keys (4v-sexpr-alist-extract keys al))
           (append keys nil)))

  (defthm sexpr-pat-alist-translate-of-4v-sexpr-alist-extract
    (implies (no-duplicatesp-equal (pat-flatten1 p1))
             (equal (sexpr-pat-alist-translate
                     p1 p2 (4v-sexpr-alist-extract (pat-flatten1 p1) al) nil)
                    (sexpr-pat-alist-translate p1 p2 al nil)))
    :hints (("goal"
             :induct (sexpr-pat-alist-translate p1 p2 al nil)
             :in-theory (enable (:induction sexpr-pat-alist-translate))
             :expand ((:free (al)
                       (sexpr-pat-alist-translate p1 p2 al nil))
                      (:free (al)
                       (sexpr-pat-alist-translate nil p2 al nil)))))))



(defsection good-esim-modulep

  (defthm no-duplicatesp-equal-ins-of-good-module
    (implies (good-esim-modulep mod)
             (no-duplicatesp-equal (pat-flatten1 (gpl :i mod))))
    :hints(("Goal" :in-theory (enable good-esim-modulep))))

  (defthm no-duplicatesp-equal-sts-of-good-module
    (implies (good-esim-modulep mod)
             (no-duplicatesp-equal (pat-flatten1 (mod-state mod))))
    :hints(("Goal" :in-theory (enable good-esim-modulep))))

  (defthm no-duplicatesp-equal-outs-of-good-module
    (implies (good-esim-modulep mod)
             (no-duplicatesp-equal (pat-flatten1 (gpl :o mod))))
    :hints(("Goal" :in-theory (enable good-esim-modulep))))

  (defthm no-duplicate-internals-when-good-esim-probe-modulep
    (implies (good-esim-probe-modulep mod)
             (no-duplicatesp-equal (pat-flatten1 (mod-internals mod))))
    :hints(("Goal" :expand ((good-esim-probe-modulep mod))))))




(defsection 4v-sexpr-vars-list

  (defthm 4v-sexpr-vars-list-append
    (set-equiv (4v-sexpr-vars-list (append a b))
               (append (4v-sexpr-vars-list a) (4v-sexpr-vars-list b)))
    :hints(("Goal" :in-theory (enable append))))

  (defthm not-member-4v-sexpr-vars-of-hons-assoc-equal
    (implies (not (member-equal v (4v-sexpr-vars-list (alist-vals al))))
             (not (member-equal v (4v-sexpr-vars (cdr (hons-assoc-equal
                                                    k al)))))))

  (defthm member-vars-sexpr-pat-alist-translate
    (implies (and (not (member-equal v (4v-sexpr-vars-list (alist-vals al))))
                  (not (member-equal v (4v-sexpr-vars-list (alist-vals acc)))))
             (not (member-equal
                   v (4v-sexpr-vars-list
                      (alist-vals
                       (sexpr-pat-alist-translate
                        oldpat newpat al acc))))))
    :hints(("Goal" :in-theory (enable sexpr-pat-alist-translate))))

  (defthm member-vars-4v-sexpr-alist-extract
    (implies (not (member-equal v (4v-sexpr-vars-list (alist-vals al))))
             (not (member-equal v (4v-sexpr-vars-list
                                   (alist-vals
                                    (4v-sexpr-alist-extract
                                     keys al)))))))

  (defthm member-vars-pat->al
    (implies (and (similar-patternsp (double-rewrite keys)
                                     (double-rewrite vals))
                  (not (member-equal v (pat-flatten1 vals)))
                  (not (member-equal v (4v-sexpr-vars-list
                                        (alist-vals acc)))))
             (not (member-equal v (4v-sexpr-vars-list
                                   (alist-vals
                                    (pat->al keys vals acc)))))))

  (defthm 4v-sexpr-vars-list-4v-sexpr-compose-alist
    (implies (not (member-equal v (4v-sexpr-vars-list (alist-vals al))))
             (not (member-equal v (4v-sexpr-vars-list
                                   (alist-vals
                                    (4v-sexpr-compose-alist x al)))))))

  (defthm 4v-sexpr-vars-list-4v-sexpr-compose-with-rw-alist
    (implies (not (member-equal v (4v-sexpr-vars-list (alist-vals al))))
             (not (member-equal v (4v-sexpr-vars-list
                                   (alist-vals
                                    (4v-sexpr-compose-with-rw-alist x al))))))))


(defsection mod-state

  (defthm member-occ-state1
    (implies (not (member-equal v (pat-flatten1 (occs-state occs))))
             (not (member-equal v (pat-flatten1 (occ-state
                                                (cdr (hons-assoc-equal
                                                      occ (occmap1 occs)))))))))

  (defthm member-occ-state
    (implies (and (not (member-equal v (pat-flatten1 (mod-state mod))))
                  (not (gpl :x mod)))
             (not (member-equal v (pat-flatten1 (occ-state (esim-get-occ occ mod))))))
    :hints(("Goal" :expand ((mod-state mod)
                            (occmap mod))))))







(encapsulate nil
  ;; Technical theorem we need for guards on new probe functions

  (local (defthm len-is-0
           (equal (equal (len x) 0)
                  (atom x))))
  (local (defun pairlis$-alist-vals-ind (keys vals)
           (if (or (atom keys) (atom vals))
               nil
             (pairlis$-alist-vals-ind
              (if (consp (car vals))
                  (cdr keys)
                keys)
              (cdr vals)))))

  (defthm 4v-sexpr-compose-alist-of-pairlis$-of-alist-vals
    (implies (equal (len keys) (len (alist-vals al1)))
             (equal (4v-sexpr-compose-alist
                     (pairlis$ keys (alist-vals al1)) al2)
                    (pairlis$ keys (alist-vals (4v-sexpr-compose-alist al1 al2)))))
    :hints(("Goal" :in-theory (enable alist-vals pairlis$)
            :induct (pairlis$-alist-vals-ind keys al1))))

  (defthm 4v-sexpr-compose-with-rw-alist-of-pairlis$-of-alist-vals
    (implies (equal (len keys) (len (alist-vals al1)))
             (equal (4v-sexpr-compose-with-rw-alist
                     (pairlis$ keys (alist-vals al1)) al2)
                    (pairlis$ keys (alist-vals (4v-sexpr-compose-with-rw-alist al1 al2)))))
    :hints(("Goal" :in-theory (enable alist-vals pairlis$)
            :induct (pairlis$-alist-vals-ind keys al1)))))






(defsection esim-simplify-update-fns
  :parents (esim)
  :short "Pluggable conservative simplifier for ESIM fixpoint extraction"
  :long "Esim-simplify-update-fns is a constrained function that is called in
conservative versions of ESIM such as ESIM-SEXPR-SIMP.  It is constrained to
produce a conservative approximation of the update functions that it is passed.
An executable function that obeys these constraints can be attached to it.
Thus, it can be used to (say) replace the update functions with Xes, rewrite
them into a nicer form, perform Shannon expansion on certain signals, etc.
Esim-simplify-update-fns is also passed the module that is currently being
examined, so that you may choose to only perform simplifcations on certain
modules.

By default, esim-simplify-update-fns has an attachment that simply preserves
the existing update functions without modification."
  (encapsulate
    (((esim-simplify-update-fns * *) => *))

    (local (defun esim-simplify-update-fns (mod update-fns)
             (declare (ignore mod))
             update-fns))

    (defthm esim-simplify-update-fns-conservative
      (4v-sexpr-alist-<= (esim-simplify-update-fns mod update-fns)
                         update-fns))

    (defthm esim-simplify-update-fns-alist-keys-same
      (set-equiv (alist-keys (esim-simplify-update-fns mod update-fns))
                  (alist-keys update-fns)))

    (defthm esim-simplify-update-fns-4v-sexpr-vars-subset
      (subsetp-equal
       (4v-sexpr-vars-list
        (alist-vals (esim-simplify-update-fns mod update-fns)))
       (append (4v-sexpr-vars-list (alist-vals update-fns))
               (alist-keys (mod-varmap mod))))))



  ;; Note that this is outside the encapsulate; it is a consequence of the
  ;; constraints, not a constraint itself.
  (defthm good-sexpr-varmap-esim-simplify-update-fns
    (implies (good-sexpr-varmap (mod-varmap mod) update-fns)
             (good-sexpr-varmap
              (mod-varmap mod)
              (esim-simplify-update-fns mod update-fns)))
    :hints (("goal" :in-theory (e/d (subsetp-trans2)
                                    (esim-simplify-update-fns-4v-sexpr-vars-subset))
             :use esim-simplify-update-fns-4v-sexpr-vars-subset))))

(defun esim-simplify-update-fns-id (mod ups)
  (declare (ignore mod)
           (xargs :guard t))
  ups)

(defattach esim-simplify-update-fns esim-simplify-update-fns-id)




(defsection esim-printing

  (defstub esim-pre-fixpoint-print (mod outfns) nil)

  (defun esim-pre-fixpoint-print-default (mod outfns)
    (declare (xargs :guard t)
             (ignore mod outfns))
    nil)

  (defattach esim-pre-fixpoint-print esim-pre-fixpoint-print-default))






(defun mk-symbol-substitution (names str repl)
  (declare (Xargs :guard (and (Symbol-listp names)
                              (stringp str)
                              (stringp repl))))
  (b* (((when (Atom names)) nil)
       (name (symbol-name (car names)))
       ((unless (str::substrp str name))
        (mk-symbol-substitution (cdr names) str repl))
       (new-name (str::strsubst str repl name))
       (sym (intern-in-package-of-symbol new-name (car names))))
    (cons (cons (car names) sym)
          (mk-symbol-substitution (cdr names) str repl))))

(defun filter-symbols (lst)
  (Declare (Xargs :guard t))
  (if (atom lst)
      nil
    (if (symbolp (car lst))
        (cons (car lst) (Filter-Symbols (Cdr lst)))
      (filter-symbols (Cdr lst)))))





(mutual-recursion
 (defun check-features (features feature-form)
   (if (atom feature-form)
       (and (member-eq feature-form features) t)
     (case (car feature-form)
       (or (or-list (check-features-list features (cdr feature-form))))
       (and (and-list (check-features-list features (cdr feature-form))))
       (not (not (check-features features (cadr feature-form)))))))

 (defun check-features-list (features forms)
   (if (atom forms)
       nil
     (cons (check-features features (car forms))
           (check-features-list features (cdr forms))))))

(defun replace-templates (features forms)
  (b* (((when (atom forms)) forms)
       ((unless (and (consp (car forms))
                     (eq (caar forms) 'template)))
        (cons (replace-templates features (car forms))
              (replace-templates features (cdr forms))))
       (template-form (car forms))
       (feature-form (cadr template-form))
       (subforms (cddr template-form))
       ((unless (check-features features feature-form))
        (replace-templates features (cdr forms))))
    (append (replace-templates features subforms)
            (replace-templates features (cdr forms)))))





; Note on the template system for generating esim-sexpr functions.

; There are getting to be a lot of different versions of esim-sexpr:
; esim-sexpr-probe, esim-sexpr-simp, the proofs are done in terms of
; componentwise functions esim-sexpr-out/esim-sexpr-nst, etc.  We'd like to
; consolidate all these definitions so we don't need to copy/paste so much.

; Following are three event templates, each with a corresponding macro that
; instantiates it.

; The first template is called *esim-sexpr-template* and generates an
; esim-sexpr-like function that produces either the next-state, outputs, or
; internal signal functions of a module.  This template also supports
; generating a single definition that returns next-state, outputs, and
; optionally internal signals as a MV.  This template does guard verification,
; but only for single-value functions.

; The second template is called *esim-sexpr-multi-template*.  It is intended
; for generating a multi-value esim-sexpr that we then prove equivalent to the
; MV of some predefined single-value functions.  Runing def-esim-sexpr-multi
; first instantiates the first template to define the multivalue function and
; then instantiates the second template to do the proof and verify the guards.

; The third template is called *esim-sexpr-mv-template*.  It generates a
; multi-value esim-sexpr and its interface is exactly like esim-sexpr-multi,
; but instead of making a new definition it simply calls the pre-existing
; single-value functions.  Because of this, we leave the definitions enabled
; and we don't need to prove anything.

; Pros of MV versus MULTI:
; - Requires fewer proofs and less complicated defintions.  These extra proofs
;   are automated and the work of creating the definitions is already done.
;   However, if we were to decide to stick with the MV approach, we could
;   simplfy *esim-sexpr-template* somewhat by removing the support for
;   multi-valued functions.
; - Keeps a good memoization discipline.  The outputs of each module (the
;   fixpoint, really) are stored in one table, the next-states in another, and
;   the internal signals in a third.  The fixpoint results stored in the
;   outputs table are reused in the computation of the next-state and internal
;   results.  Contrast with the multi approach, where if we run ESIM-SEXPR-OUT
;   and then ESIM-SEXPR, or else ESIM-SEXPR and then ESIM-SEXPR-PROBE, we rerun
;   the fixpoint computation.

; Pros of MULTI versus MV:
; - Marginally faster, about 5% on FADD.  This is due to the fact that (e.g.)
;   the MULTI version of ESIM-SEXPR will only do one traversal of the module
;   hierarchy in order to get the output/next-state functions, whereas the MV
;   version will do two, one for outputs and one for next-states; three for the
;   MV version of ESIM-SEXPR-PROBE.



; Template:  This defconst will contain all the code for esim-sexpr,
; esim-sexpr-probe, esim-sexpr-simp, etc, so that we don't have to change it
; all in several places every time.

; The template keywords here have the following meanings:
; :nst, :out, :probe: see :multi, below.
; :multi:     When set, produce at least the next-state and outputs (as a MV),
;             as well as internal signals if :probe is set.  :Out and :nst
;             should both be set in this case.  When not set, exactly one of
;             :out, :nst, and :probe should be set, and this only produces a
;             single value.
; :old-probe: Meaningless when :probe is not set.  When set, produces internal
;             signals in an alist mapping symbols, each containing a
;             hierarchical wire name, to values.  Otherwise, maps
;             lists of symbols, each giving a hierarchical wire name where all
;             but the last symbol are occurrences and the last symbol is the
;             local wire name.
; :simplify:  Allow the update functions to be simplified before the fixpoint
;             is computed.  Only meaningful when :out is set.

(defmacro esim-4v-sexpr-compose-alist (&rest args)
  `(if *esim-sexpr-rewrite*
       (4v-sexpr-compose-with-rw-alist . ,args)
     (4v-sexpr-compose-alist . ,args)))

(defmacro esim-4v-sexpr-restrict-alist (&rest args)
  `(if *esim-sexpr-rewrite*
       (4v-sexpr-restrict-with-rw-alist . ,args)
     (4v-sexpr-restrict-alist . ,args)))

(defmacro esim-4v-sexpr-compose-fn ()
  '(if *esim-sexpr-rewrite* '4v-sexpr-compose-with-rw '4v-sexpr-compose))

(defmacro esim-4v-sexpr-restrict-fn ()
  '(if *esim-sexpr-rewrite* '4v-sexpr-restrict-with-rw '4v-sexpr-restrict))

(defconst *esim-sexpr-template*
  '(progn
     (mutual-recursion
      (defun esim-sexpr-fnname
        (mod ; module to simulate
         in  ; particular input alist to use (binds inputs to 4v consts)
         st  ; particular state alist to use (binds state bits to 4v consts)
         )
        (declare (xargs :measure (list (acl2-count mod) 50 50)
                        :well-founded-relation nat-list-<
                        :hints (("goal" :do-not-induct t))
                        :guard (and (estime (good-esim-modulep mod))
                                    (template :probe
                                      (estime
                                       (template (not :old-probe)
                                         (new-good-esim-probe-modulep mod))
                                       (template :old-probe
                                         (good-esim-probe-modulep mod)))))
                        :verify-guards nil))
        ;; NOTE: although this is in the mutual-recursion, it is not actually used
        ;; in the "general" computation -- the :exec part of esim-sexpr-occ-fn
        ;; directly calls the general function instead.

        (b* ( ;; Get the fully-general update functions for the module.  Each
             ;; function here is a sexpr with variables from (gpl :i mod) and
             ;; (mod-state mod).
             ((template (not :multi) general-thing)
              (template :multi
                (mv general-nst ; (mod-state mod)          -> fully general update functions
                    general-out ; (gpl :o mod) & locals    -> fully general update functions
                    (template :probe
                      general-probe) ; (mod-internal-paths mod) -> fully general update functions
                    ))
               (esim-sexpr-general-fnname mod))

             ((with-fast
               ;; Usually these aren't fast because we don't want to leave a bunch
               ;; of fast alists stuck in the memo tables, and we don't want to rely
               ;; on memoized results to stay fast since anyone might free them.
               (template :out general-out)
               (template :nst general-nst)
               (template :probe general-probe)))

             (flat-ins  (pat-flatten1 (gpl :i mod)))
             (flat-sts  (pat-flatten1 (mod-state mod)))
             (template :out
              (flat-outs (pat-flatten1 (gpl :o mod))))

             ;; BOZO these are probably effectively no-ops that, at most, rearrange
             ;; the order of signals in the alist.  It might be that this was a
             ;; useful in proofs to see that only the relevant signals were bound,
             ;; but it is probably possible to prove this away.  Sol says we might
             ;; want this because of the MBE in the concrete esim spec, which will
             ;; produce the signals in these orders.
             (template :out
               (general-out (4v-sexpr-alist-extract flat-outs general-out)))
             (template :nst
               (general-nst (4v-sexpr-alist-extract flat-sts general-nst)))
             (template :old-probe
               (general-probe (4v-sexpr-alist-extract
                               (pat-flatten1 (mod-internals mod))
                               general-probe)))

             ;; Fix the in and st alists to only bind the appropriate keys.  We
             ;; would like to skip this step for performance reasons.  Note below
             ;; that when we create the restrict-al, we use append, so it's
             ;; important at least that the ins don't include any state bits.
             ;; Maybe there's also a reason to do it to the states, or maybe we
             ;; can get rid of it.
             (in (time$ (4v-sexpr-alist-extract flat-ins in)
                        :mintime 1
                        :msg "; Fixing input alist took ~st sec, ~sa bytes.~%"))
             (st (time$ (4v-sexpr-alist-extract flat-sts st)
                        :mintime 1
                        :msg "; Fixing state alist took ~st sec, ~sa bytes.~%"))

             ;; Concatenate in and st to form an alist that maps the variable names
             ;; used in general-nst/out to their incoming values.  Note: the state
             ;; names must be disjoint from the signal and input names.
             (restrict-al
              ;; BOZO maybe we can do this better with something like
              ;; hons-shrink-alist, or perhaps combine it with the sexpr-extracts
              ;; somehow.
              ;; 3.29 seconds for the first run
              (time$ (make-fast-alist (append in st))
                     :mintime 1
                     :msg "; Making unified restrict-al took ~st sec, ~sa bytes.~%"))

             ;; Get the specialized outputs by composing the fully general
             ;; functions with the restrict-al.  We use compose instead of
             ;; restrict so that unbound vars become X.
             (template :out
               (out (esim-4v-sexpr-compose-alist general-out restrict-al)))
             (template :nst
               (nst (esim-4v-sexpr-compose-alist general-nst restrict-al)))
             (template :probe
               (probe (esim-4v-sexpr-compose-alist general-probe restrict-al))))
          (fast-alist-free restrict-al)
          (clear-memoize-table (esim-4v-sexpr-compose-fn))
          (template :multi (mv nst out (template :probe probe)))
          (template (not :multi) thing)))

      (defun esim-sexpr-general-fnname (mod)
        ;; Returns (general-nst general-thing general-probe).
        ;; These are non-fast alists where:
        ;;  - general-nst binds (mod-state mod)          -> fully general update functions
        ;;  - general-out binds (gpl :o mod) & locals    -> fully general update functions
        ;;  - general-probe binds (mod-internal-paths mod) -> fully general update functions
        ;; Each function is a sexpr.
        ;;  - the 4v-sexpr-vars are from (gpl :i mod) and (mod-state mod).
        (declare (xargs :measure (list (acl2-count mod) 49 50)
                        :guard (and (estime (good-esim-modulep mod))
                                    (template :probe
                                     (estime
                                      (template (not :old-probe)
                                       (new-good-esim-probe-modulep mod))
                                      (template :old-probe
                                       (good-esim-probe-modulep mod)))))))
        (time$
         (if (gpl :x mod)
             ;; Special case for primitives and overridden modules.  Eapply-sexpr
             ;; returns (mv (gpl :nst x) (gpl :out x) (gpl :int x)), and this is
             ;; already exactly what we want.
             (b* (((mv ?nst ?out ?probe)
                   (eapply-sexpr (gpl :x mod))))
               (template :multi
                 (mv nst out (template :probe probe)))
               (template (not :multi) thing))
           ;; Otherwise use the fixpoint version.
           (esim-sexpr-fixpoint-fnname mod))
         :msg "done ~x0: ~st seconds, ~sa bytes~%"
         :args (list (gpl :n mod))
         :mintime 1))

      (defun esim-sexpr-fixpoint-fnname (mod)
        ;; MOD is a non-primitive module.
        ;; Returns (general-nst general-out general-probe).
        ;; These are non-fast alists where:
        ;;  - general-nst binds (mod-state mod)          -> fully general update functions
        ;;  - general-out binds (gpl :o mod) & locals    -> fully general update functions
        ;;  - general-probe binds (mod-internal-paths mod) -> fully general update functions
        ;; Each function is a sexpr.
        ;;  - the 4v-sexpr-vars are from (gpl :i mod) and (mod-state mod).
        (declare (xargs :guard (and (estime (good-esim-modulep mod))
                                    (not (gpl :x mod))
                                    (template :probe
                                     (estime
                                      (template (not :old-probe)
                                       (new-good-esim-probe-modulep mod))
                                      (template :old-probe
                                       (good-esim-probe-modulep mod)))))
                        :verify-guards nil
                        :measure (list (acl2-count mod) 48 50)))
        (b* (;; Occs is an alist mapping occurrence names to occurrences, so
             ;; occnames is the list of occurrence names.
             (occs     (make-fast-alist (occmap mod)))
             (occnames (alist-keys occs))

             ((template (not :multi) thing-fns)
              (template :multi
                (mv nst-fns out-fns (template :probe probe-fns)))
              ;; Get the update functions from the occurrences.  (We
              ;; aren't doing any fixpoint stuff yet, just getting the expressions
              ;; to use.)  These are all ordinary, slow alists.
              ;;
              ;;   - update-fns binds all of the module's signal names (including
              ;;     the local, internal wires and also the primary outputs) to
              ;;     their update functions.
              ;;
              ;;   - nst-fns binds all state bits to their update functions.
              ;;
              ;;   - internal-fns binds paths from (mod-internal-paths mod) to their
              ;;     update functions, but does NOT include any "local wires" in the
              ;;     current module; it only includes the paths from submodule
              ;;     instances.
              (esim-sexpr-occs-fnname mod occnames))

             (template :out
              (varmap (mod-varmap mod))

              (template :simplify
               (out-fns (esim-simplify-update-fns mod out-fns)))

              (- (esim-pre-fixpoint-print mod out-fns))

              ;; Get the least fixpoint for the update functions.
              (fixpoint (time$ (sexpr-fixpoint-with-varmap out-fns varmap)
                               :msg "fixpoint for ~x0 (~x1 signals): ~st seconds, ~sa bytes~%"
                               :args (list (gpl :n mod) (len out-fns))
                               :mintime 1))
              (out fixpoint)
              (- (fast-alist-free varmap)))

             (template (not :out)
               (fixpoint (esim-sexpr-general-out-fn mod)))

             (template (or (not :out) :multi)
               ((with-fast fixpoint))

               (template :nst
                 (nst (esim-4v-sexpr-restrict-alist nst-fns fixpoint)))

               (template :probe
                 ;; To produce the actual general-probe list from the internal-fns, we
                 ;; need to add in any local wires.  BOZO we could probably optimize
                 ;; this a bit.  If we changed our path format so that the wire name
                 ;; was just the final cdr, we could avoid some of this and just append
                 ;; the extract onto the restrict.  OTOH, this is probably all quite
                 ;; minimal in its actual cost.
                 (local-wires (hons-set-diff (driven-signals mod)
                                             (pat-flatten1 (gpl :o mod))))
                 (template (not :old-probe)
;        (- (cw "In module ~x0." (gpl :n mod)))
;        (- (cw "local wires: ~x0.~%" local-wires))
;        (- (cw "local paths: ~x0.~%" local-paths))
;        (- (cw "local vals: ~x0.~%" local-vals))
                   (probe (append (4v-sexpr-alist-extract local-wires fixpoint)
                                  (esim-4v-sexpr-restrict-alist probe-fns fixpoint))))

                 (template :old-probe
                   (probe (append (4v-sexpr-alist-extract local-wires fixpoint)
                                  (esim-4v-sexpr-restrict-alist probe-fns fixpoint)))))))

          ;; Jared: adding this clear, as in esim-sexpr-fixpoint.
          (clear-memoize-table (esim-4v-sexpr-restrict-fn))

          ;; I was surprised that we freed these.  But, it makes sense if you
          ;; keep in mind that this function should only be called once per
          ;; module, so we don't need these particular maps for mod later on.
          (fast-alist-free occs)
          (template :multi (mv nst out (template :probe probe)))
          (template (not :multi) thing)))

      (defun esim-sexpr-occs-fnname (mod occs)
        ;; Gather the update functions from a module's occurrences.
        ;;
        ;; Mod is the module itself, and occs is the occurrence map that
        ;; binds occurrence names to occurrences.
        ;;
        ;; Update-fns, nst-fns, and internal-fns are accumulators that we are
        ;; constructing.  Each is an alist that maps some names to their update
        ;; functions.
        ;;
        ;; The update-fns alist will contain all of the driven signals, including
        ;; both internal wires and primary outputs.
        ;;
        ;; The nst-fns alist will contain all of the state bits.
        ;;
        ;; The internal-fns alist will contain all of the "inherited", internal
        ;; paths from submodules, but their names are all fixed up so that they
        ;; correspond to real names from (mod-internal-paths mod).  That is, if we
        ;; have a submodule foo_inst of module foo, and (a b c) is a canonical path
        ;; into foo, then internal-fns will get an entry whose path is (foo_inst a b
        ;; c).
        (declare (xargs :guard (and (esim-mod-occs-guard mod occs)
                                    (template :probe
                                      (estime
                                       (template (not :old-probe)
                                         (new-good-esim-probe-modulep mod))
                                       (template :old-probe
                                         (good-esim-probe-modulep mod)))))
                        :measure (list (acl2-count mod) 47 (len occs))))
        ;; This just iterates over the occurrences and accumulates all
        ;; update/next-state functions.
        (if (or (atom occs)
                (not (mbt (consp (gpl :occs mod)))))
            (progn$ ;; silly way of keeping the if indentation right
             (template (not :multi) 'thing-fns)
             (template :multi (mv 'nst-fns 'out-fns
                                  (template :probe 'probe-fns))))
          (b* (((template (not :multi) thing-fns1)
                (template :multi (mv nst-fns1 out-fns1 (template :probe probe-fns1)))
                (esim-sexpr-occ-fnname
                 (cdr (hons-get (car occs) (occmap mod)))))
               ((template (not :multi) thing-fns-r)
                (template :multi (mv nst-fns-r out-fns-r (template :probe probe-fns-r)))
                (esim-sexpr-occs-fnname mod (cdr occs))))
            (template (not :multi) (append thing-fns1 thing-fns-r))
            (template :multi
              (mv (append nst-fns1 nst-fns-r)
                  (append out-fns1 out-fns-r)
                  (template :probe
                    (append probe-fns1 probe-fns-r)))))))

      (defun esim-sexpr-occ-fnname (occ)
        ;; Gather the update functions from a single occurrence.
        ;; update-fns, nst-fns, and internal-fns are as in esim-sexpr-occs-fn.
        (declare (xargs :measure (list (acl2-count occ) 51 50)
                        :guard (and (good-esim-occp occ)
                                    (template :probe
                                     (estime
                                      (template (not :old-probe)
                                       (new-good-esim-probe-occp occ))
                                      (template :old-probe
                                       (good-esim-probe-occp occ)))))))
        (mbe :logic
             (b* ((op (gpl :op occ))
                  ;; Make in/state alists mapping the names within the occurrence
                  ;; to the names outside.
                  (inal (pat->al (gpl :i op) (gpl :i occ) nil))
                  (stal (pat->al (mod-state op) (occ-state occ) nil))

                  ;; Get the update functions for the submodule.  These have the correct
                  ;; values but incorrect keys.
                  ((template (not :multi) thingal)
                   (template :multi (mv nstal outal (template :probe probeal)))
                   (esim-sexpr-fnname op inal stal))

                  ;; Fix the keys by translating them from inner names to outer names.
                  (template :out
                   (out-fns (sexpr-pat-alist-translate
                             (gpl :o op) (gpl :o occ) outal nil)))
                  (template :nst
                   (nst-fns (sexpr-pat-alist-translate
                             (mod-state op) (occ-state occ) nstal nil)))
                  (template :probe
                   (probe-fns
                    (template (not :old-probe)
                     (let* ((old-keys    (alist-keys probeal))
                            (new-keys    (extend-internal-paths (gpl :u occ) old-keys)))
                       (pairlis$ new-keys (alist-vals probeal))))
                    (template :old-probe
                     (sexpr-pat-alist-translate
                      (mod-internals op) (occ-internals occ)
                      probeal nil))))
                  )
               (template (not :multi) thing-fns)
               (template :multi (mv nst-fns out-fns (template :probe probe-fns))))
             :exec
             (b* ((op (gpl :op occ))
                  ;; Make in/state alists mapping the names within the occurrence
                  ;; to the names outside.
                  (restrict-al (pat->al
                                (gpl :i op) (gpl :i occ)
                                (pat->al (mod-state op) (occ-state occ) nil)))

                  ;; Get the general update functions for the submodule.  They
                  ;; have incorrect keys (named using the submodule names, instead
                  ;; of the superior module names), and incorrect values (with
                  ;; variable names from the inputs of the submodule, instead of
                  ;; using the signals we're passing in from the superior module).
                  ((template (not :multi) general-thing)
                   (template :multi (mv general-nst general-out
                                       (template :probe general-probe)))
                   (esim-sexpr-general-fnname op))

                  ((with-fast
                    (template :out general-out)
                    (template :nst general-nst)
                    (template :probe general-probe)
                    restrict-al)) ;; for sexpr-pat-alist-translate

                  ;; BOZO can we combine these operations so we don't need general-out
                  ;; to be fast?  That is, maybe we should compose in the restrict-al
                  ;; before we do the sexpr-pat-alist-translate?

                  ;; Fix the keys by translating them from inner names to outer names.
                  ;; Fix the keys by translating them from inner names to outer names.
                  (template :out
                   (out-fns (sexpr-pat-alist-translate
                             (gpl :o op) (gpl :o occ) general-out nil))
                   (out-fns-new (esim-4v-sexpr-compose-alist out-fns restrict-al)))

                  (template :nst
                   (nst-fns (sexpr-pat-alist-translate
                             (mod-state op) (occ-state occ) general-nst nil))
                   (nst-fns-new (esim-4v-sexpr-compose-alist nst-fns restrict-al)))
                  (template :probe
                   (probe-fns
                    (template (not :old-probe)
                     (let* ((old-keys    (alist-keys general-probe))
                            (new-keys    (extend-internal-paths (gpl :u occ) old-keys)))
                       (pairlis$ new-keys (alist-vals general-probe))))
                    (template :old-probe
                     (sexpr-pat-alist-translate
                      (mod-internals op) (occ-internals occ)
                      general-probe nil)))
                   (probe-fns-new (esim-4v-sexpr-compose-alist probe-fns restrict-al))))
               ;; Jared: adding this clear, as in esim-sexpr-occ
               (clear-memoize-table (esim-4v-sexpr-compose-fn))
               (template (not :multi) thing-fns-new)
               (template :multi (mv nst-fns-new out-fns-new
                                   (template :probe probe-fns-new)))))))

     (template (not :multi)
       (defthm true-listp-esim-sexpr-occ-fnname
         (true-listp (esim-sexpr-occ-fnname occ))
         :hints (("goal" :expand ((esim-sexpr-occ-fnname occ)))))


       (defthm 4v-sexpr-vars-of-esim-sexpr-fnname
         (implies (and (not (member-equal x (4v-sexpr-vars-list
                                             (alist-vals
                                              (4v-sexpr-alist-extract
                                               (pat-flatten1 (gpl :i mod))
                                               ins)))))
                       (not (member-equal x (4v-sexpr-vars-list
                                             (alist-vals
                                              (4v-sexpr-alist-extract
                                               (pat-flatten1 (mod-state mod))
                                               sts))))))
                  (not (member-equal x (4v-sexpr-vars-list
                                        (alist-vals
                                         (esim-sexpr-fnname mod ins sts))))))
         :hints(("Goal" :in-theory (e/d () (esim-sexpr-general-fnname)))))

       (defthm member-vars-esim-sexpr-occ-fnname
         (implies (and (not (member-equal v (pat-flatten1 (gpl :i occ))))
                       (not (member-equal v (pat-flatten1 (occ-state occ))))
                       (good-esim-occp occ))
                  (not (member-equal
                        v (4v-sexpr-vars-list
                           (alist-vals
                            (esim-sexpr-occ-fnname occ))))))
         :hints (("goal" :expand ((esim-sexpr-occ-fnname occ))
                  :in-theory (e/d () (esim-sexpr-fnname))
                  :do-not-induct t)))


       (defthm member-vars-esim-sexpr-occs-fnname
         (implies (and (not (member-equal v (collect-signal-list
                                             :i (occs-for-names occs mod))))
                       (not (member-equal v (pat-flatten1 (mod-state mod))))
                       (not (gpl :x mod))
                       (good-esim-modulep mod))
                  (not (member-equal
                        v (4v-sexpr-vars-list
                           (alist-vals
                            (esim-sexpr-occs-fnname mod occs))))))
         :hints (("goal" :expand ((esim-sexpr-occs-fnname mod occs)
                                  (esim-sexpr-occ-fnname nil))
                  :induct (len occs)
                  :in-theory (e/d (fal-extract)
                                  (esim-sexpr-occ-fnname
                                   (esim-sexpr-occ-fnname)
                                   (esim-sexpr-fnname)
                                   good-esim-modulep occmap))
                  :do-not-induct t))
         :otf-flg t)

       (template :out
         (defthm lookup-in-esim-sexpr-occ-fnname
           (implies (and (not (member-equal key (pat-flatten1 (gpl :o occ))))
                         (good-esim-occp occ))
                    (not (hons-assoc-equal
                          key (esim-sexpr-occ-fnname occ))))
           :hints (("goal" :expand ((esim-sexpr-occ-fnname occ)
                                    (esim-sexpr-occ-fnname nil))
                    :in-theory (e/d () (esim-sexpr-fnname (esim-sexpr-occ-fnname)))
                    :do-not-induct t)))

         (defthm lookup-in-esim-sexpr-occs-fnname
           (implies (and (not (member-equal key (collect-signal-list
                                                 :o (occs-for-names occs mod))))
                         (good-esim-modulep mod))
                    (not (hons-assoc-equal
                          key (esim-sexpr-occs-fnname mod occs))))
           :hints (("goal" :induct (len occs)
                    :in-theory (e/d (fal-extract)
                                    (good-esim-occp
                                     good-esim-modulep occmap
                                     (esim-sexpr-occ-fnname)
                                     esim-sexpr-occ-fnname))
                    :expand ((esim-sexpr-occs-fnname mod occs)
                             (esim-sexpr-occ-fnname nil)))))

         (defthm good-sexpr-varmap-mod-varmap-esim-sexpr-occs-fnname
           (implies (and (good-esim-modulep mod)
                         (not (gpl :x mod)))
                    (good-sexpr-varmap (mod-varmap mod)
                                       (esim-sexpr-occs-fnname
                                        mod (alist-keys (occmap mod)))))
           :hints(("Goal" :in-theory (enable mod-varmap)
                   :do-not-induct t)
                  (witness :ruleset subsetp-witnessing))
           :otf-flg t))

       (verify-guards esim-sexpr-fnname
         :guard-debug t
         :hints (("goal" :do-not-induct t
                  :in-theory (e/d (consp-alist-keys-implies-occs
                                   subsetp-equal)
                                  (hons-assoc-equal
                                   stringify
                                   eapply-sexpr
                                   good-esim-modulep
                                   occmap
                                   good-sexpr-varmap
                                   esim-sexpr-general-fnname
                                   4v-sexpr-restrict
                                   subsetp-car-member
                                   hons-set-diff
                                   sexpr-fixpoints))))
         :otf-flg t)

       (memoize 'esim-sexpr-general-fnname
                (template :simplify :aokp t)))

     (template (and (not :multi) :out)
       (defthm alist-keys-esim-sexpr-fnname
         (equal (alist-keys (esim-sexpr-fnname mod in st))
                (pat-flatten1 (gpl :o mod)))
         :hints(("Goal" :in-theory (e/d (esim-sexpr-fnname)
                                        (esim-sexpr-general-fnname)))))

       (defthm alist-keys-esim-sexpr-occ-fnname
         (implies (good-esim-occp occ)
                  (equal (alist-keys (esim-sexpr-occ-fnname occ))
                         (pat-flatten1 (gpl :o occ))))
         :hints(("Goal" :in-theory (disable esim-sexpr-fnname)
                 :expand ((esim-sexpr-occ-fnname occ)))))

       (defthm alist-keys-esim-sexpr-occs-fnname
         (implies (good-esim-modulep mod)
                  (equal (alist-keys (esim-sexpr-occs-fnname mod occs))
                         (collect-signal-list
                          :o (occs-for-names occs mod))))
         :hints (("goal" :in-theory (e/d (occmap-when-no-occs fal-extract)
                                         (esim-sexpr-occ-fnname
                                          (esim-sexpr-occ-fnname)
                                          good-esim-modulep
                                          occmap))
                  :induct (len occs)
                  :expand ((esim-sexpr-occs-fnname mod occs)
                           (esim-sexpr-occ-fnname nil))))))

     (template (and (not :multi) :nst)
       (defthm alist-keys-esim-sexpr-occ-fnname
         (equal (alist-keys (esim-sexpr-occ-fnname occ))
                (pat-flatten1 (occ-state occ)))
         :hints (("goal" :in-theory (disable esim-sexpr-fnname)
                  :expand ((esim-sexpr-occ-fnname occ)))))

       (defthm alist-keys-esim-sexpr-occs-fnname
         (equal (alist-keys (esim-sexpr-occs-fnname mod occs))
                (pat-flatten1
                 (occs-state (alist-vals (fal-extract occs (occmap mod))))))
         :hints(("Goal" :in-theory (enable occs-state fal-extract)
                 :expand ((esim-sexpr-occs-fnname mod occs))
                 :induct (len occs)))))


     (in-theory (disable esim-sexpr-fnname
                         esim-sexpr-general-fnname
                         esim-sexpr-fixpoint-fnname
                         esim-sexpr-occs-fnname
                         esim-sexpr-occ-fnname))))



(defconst *esim-sexpr-template-names*
  (hons-remove-duplicates
   (filter-symbols (pat-flatten1 *esim-sexpr-template*))))

(defmacro def-esim-sexpr (fnname &key component general-out-name
                                          features)
  (b* ((features (if (eq component :multi)
                     (append '(:multi :nst :out) features)
                   (cons component features))))
    (replace-templates
     features
     (sublis (cons (cons 'esim-sexpr-general-out-fn
                         general-out-name)
                   (append
                    (mk-symbol-substitution
                     *esim-sexpr-template-names*
                     "-FNNAME" (symbol-name fnname))
                    (mk-symbol-substitution
                     *esim-sexpr-template-names*
                     "THING" (symbol-name component))))
             *esim-sexpr-template*))))


(defconst *esim-sexpr-multi-template*
  '(progn
     (defthm-esim-sexpr-flag
       (defthm esim-sexpr-fnname-is-components
         (equal (esim-sexpr-fnname mod in st)
                (list (esim-sexpr-nstfnname mod in st)
                      (esim-sexpr-outfnname mod in st)
                      (template :probe (esim-sexpr-intfnname mod in st))))
         :hints ((and stable-under-simplificationp
                      (flag::expand-calls-computed-hint
                       clause '(esim-sexpr-fnname
                                esim-sexpr-nstfnname
                                esim-sexpr-outfnname
                                (template :probe esim-sexpr-intfnname)))))
         :flag esim)
       (defthm esim-sexpr-general-fnname-is-components
         (equal (esim-sexpr-general-fnname mod)
                (list (esim-sexpr-general-nstfnname mod)
                      (esim-sexpr-general-outfnname mod)
                      (template :probe (esim-sexpr-general-intfnname mod))))
         :hints ((and stable-under-simplificationp
                      (flag::expand-calls-computed-hint
                       clause '(esim-sexpr-general-fnname
                                esim-sexpr-general-nstfnname
                                esim-sexpr-general-outfnname
                                (template :probe esim-sexpr-general-intfnname)))))
         :flag general)

       (defthm esim-sexpr-fixpoint-fnname-is-components
         (implies (not (gpl :x mod))
                  (equal (esim-sexpr-fixpoint-fnname mod)
                         (list (esim-sexpr-fixpoint-nstfnname mod)
                               (esim-sexpr-fixpoint-outfnname mod)
                               (template :probe
                                 (esim-sexpr-fixpoint-intfnname mod)))))
         :hints ((and stable-under-simplificationp
                      (flag::expand-calls-computed-hint
                       clause '(esim-sexpr-fixpoint-fnname
                                esim-sexpr-fixpoint-nstfnname
                                esim-sexpr-fixpoint-outfnname
                                (template :probe
                                  esim-sexpr-fixpoint-intfnname))))
                 (and stable-under-simplificationp
                      (flag::expand-calls-computed-hint
                       clause '(esim-sexpr-general-outfnname)))
                 (and stable-under-simplificationp
                      (flag::expand-calls-computed-hint
                       clause '(esim-sexpr-fixpoint-outfnname))))
         :flag fixpoint)
       (defthm esim-sexpr-occs-fnname-is-components
         (equal (esim-sexpr-occs-fnname mod occs)
                (list (esim-sexpr-occs-nstfnname mod occs)
                      (esim-sexpr-occs-outfnname mod occs)
                      (template :probe
                        (esim-sexpr-occs-intfnname mod occs))))
         :hints ((and stable-under-simplificationp
                      (flag::expand-calls-computed-hint
                       clause '(esim-sexpr-occs-fnname
                                esim-sexpr-occs-nstfnname
                                esim-sexpr-occs-outfnname
                                (template :probe
                                  esim-sexpr-occs-intfnname)))))
         :flag occs)
       (defthm esim-sexpr-occ-fnname-is-components
         (equal (esim-sexpr-occ-fnname occ)
                (list (esim-sexpr-occ-nstfnname occ)
                      (esim-sexpr-occ-outfnname occ)
                      (template :probe
                        (esim-sexpr-occ-intfnname occ))))
         :hints ((and stable-under-simplificationp
                      (flag::expand-calls-computed-hint
                       clause '(esim-sexpr-occ-fnname
                                esim-sexpr-occ-nstfnname
                                esim-sexpr-occ-outfnname
                                (template :probe
                                  esim-sexpr-occ-intfnname)))))
         :flag occ)
       :hints(("Goal" :in-theory (disable eapply-sexpr
                                          sexpr-fixpoint-with-varmap))))

     (verify-guards esim-sexpr-fnname
       :hints (("goal" :do-not-induct t
                :in-theory (e/d (consp-alist-keys-implies-occs
                                 subsetp-equal)
                                (hons-assoc-equal
                                 stringify
                                 eapply-sexpr
                                 good-esim-modulep
                                 occmap
                                 good-sexpr-varmap
                                 4v-sexpr-restrict
                                 subsetp-car-member
                                 hons-set-diff
                                 sexpr-fixpoints)))
               (and stable-under-simplificationp
                    '(:expand ((:free (in st) (esim-sexpr-nstfnname
                                               (gpl :op occ) in st))
                               (:free (in st) (esim-sexpr-outfnname
                                               (gpl :op occ) in st))
                               (template :probe
                                 (:free (in st) (esim-sexpr-intfnname
                                                 (gpl :op occ) in st))))))))

     (memoize 'esim-sexpr-general-fnname
              (template :simplify :aokp t))))


(defconst *esim-sexpr-multi-template-names*
  (hons-remove-duplicates
   (filter-symbols (pat-flatten1 *esim-sexpr-multi-template*))))

(defmacro def-esim-sexpr-multi (fnname &key
                                       out-fnname nst-fnname int-fnname
                                       features)

  `(progn (def-esim-sexpr ,fnname :component :multi :features ,features)
          ,(replace-templates
            features
            (sublis (append

                     (mk-symbol-substitution
                      *esim-sexpr-multi-template-names*
                      "-OUTFNNAME" (symbol-name out-fnname))
                     (mk-symbol-substitution
                      *esim-sexpr-multi-template-names*
                      "-NSTFNNAME" (symbol-name nst-fnname))
                     (mk-symbol-substitution
                      *esim-sexpr-multi-template-names*
                      "-INTFNNAME" (symbol-name int-fnname))
                     (mk-symbol-substitution
                      *esim-sexpr-multi-template-names*
                      "-FNNAME" (symbol-name fnname)))
                    *esim-sexpr-multi-template*))))


(defconst *esim-sexpr-mv-template*
  '(progn (defun esim-sexpr-fnname (mod in st)
            (declare (xargs :guard (and (estime (good-esim-modulep mod))
                                        (template :probe
                                          (estime
                                           (template (not :old-probe)
                                             (new-good-esim-probe-modulep mod))
                                           (template :old-probe
                                             (good-esim-probe-modulep
                                              mod)))))))
            (mv (esim-sexpr-nstfnname mod in st)
                (esim-sexpr-outfnname mod in st)
                (template :probe
                  (esim-sexpr-intfnname mod in st))))

          (defun esim-sexpr-general-fnname (mod)
            (declare (xargs :guard (and (estime (good-esim-modulep mod))
                                        (template :probe
                                          (estime
                                           (template (not :old-probe)
                                             (new-good-esim-probe-modulep mod))
                                           (template :old-probe
                                             (good-esim-probe-modulep
                                              mod)))))))
            (mv (esim-sexpr-general-nstfnname mod)
                (esim-sexpr-general-outfnname mod)
                (template :probe
                  (esim-sexpr-general-intfnname mod))))

          (defun esim-sexpr-fixpoint-fnname (mod)
            (declare (xargs :guard (and (estime (good-esim-modulep mod))
                                        (template :probe
                                          (estime
                                           (template (not :old-probe)
                                             (new-good-esim-probe-modulep mod))
                                           (template :old-probe
                                             (good-esim-probe-modulep
                                              mod))))
                                        (not (gpl :x mod)))))
            (mv (esim-sexpr-fixpoint-nstfnname mod)
                (esim-sexpr-fixpoint-outfnname mod)
                (template :probe
                  (esim-sexpr-fixpoint-intfnname mod))))

          (defun esim-sexpr-occs-fnname (mod occs)
            (declare (xargs :guard (and (esim-mod-occs-guard mod occs)
                                    (template :probe
                                      (estime
                                       (template (not :old-probe)
                                         (new-good-esim-probe-modulep mod))
                                       (template :old-probe
                                         (good-esim-probe-modulep mod)))))))
            (mv (esim-sexpr-occs-nstfnname mod occs)
                (esim-sexpr-occs-outfnname mod occs)
                (template :probe
                  (esim-sexpr-occs-intfnname mod occs))))

          (defun esim-sexpr-occ-fnname (occ)
            (declare (xargs :guard (and (good-esim-occp occ)
                                        (template :probe
                                          (estime
                                           (template (not :old-probe)
                                             (new-good-esim-probe-occp occ))
                                           (template :old-probe
                                             (good-esim-probe-occp occ)))))))
            (mv (esim-sexpr-occ-nstfnname occ)
                (esim-sexpr-occ-outfnname occ)
                (template :probe
                  (esim-sexpr-occ-intfnname occ))))))

(defconst *esim-sexpr-mv-template-names*
  (hons-remove-duplicates
   (filter-symbols (pat-flatten1 *esim-sexpr-mv-template*))))


(defmacro def-esim-sexpr-mv (fnname &key
                                    out-fnname nst-fnname int-fnname
                                    features)
  (replace-templates
   features
   (sublis (append
            (mk-symbol-substitution
             *esim-sexpr-mv-template-names*
             "-OUTFNNAME" (symbol-name out-fnname))
            (mk-symbol-substitution
             *esim-sexpr-mv-template-names*
             "-NSTFNNAME" (symbol-name nst-fnname))
            (mk-symbol-substitution
             *esim-sexpr-mv-template-names*
             "-INTFNNAME" (symbol-name int-fnname))
            (mk-symbol-substitution
             *esim-sexpr-mv-template-names*
             "-FNNAME" (symbol-name fnname)))
           *esim-sexpr-mv-template*)))




(def-esim-sexpr -out :component :out)

(def-esim-sexpr -nst :component :nst
  :general-out-name esim-sexpr-general-out)

(def-esim-sexpr -int :component :probe
  :general-out-name esim-sexpr-general-out)

(def-esim-sexpr -old-int :component :probe
  :general-out-name esim-sexpr-general-out
  :features (:old-probe))

(flag::make-flag esim-sexpr-flag esim-sexpr-out
                 :flag-mapping ((esim-sexpr-out esim)
                                (esim-sexpr-general-out general)
                                (esim-sexpr-fixpoint-out fixpoint)
                                (esim-sexpr-occs-out occs)
                                (esim-sexpr-occ-out occ)))




(def-esim-sexpr-mv ||
  :out-fnname -out
  :nst-fnname -nst)

(def-esim-sexpr-mv -probe
  :out-fnname -out
  :nst-fnname -nst
  :int-fnname -old-int
  :features (:probe :old-probe))

(def-esim-sexpr-mv -new-probe
  :out-fnname -out
  :nst-fnname -nst
  :int-fnname -int
  :features (:probe))




(def-esim-sexpr -simp-out :component :out :features (:simplify))

(def-esim-sexpr -simp-nst :component :nst
  :general-out-name esim-sexpr-general-simp-out
  :features (:simplify))

(def-esim-sexpr -simp-int :component :probe
  :general-out-name esim-sexpr-general-simp-out
  :features (:simplify))

(def-esim-sexpr -simp-old-int :component :probe
  :general-out-name esim-sexpr-general-simp-out
  :features (:old-probe :simplify))


(def-esim-sexpr-mv -simp
  :out-fnname -simp-out
  :nst-fnname -simp-nst
  :features (:simplify))

(def-esim-sexpr-mv -simp-probe
  :out-fnname -simp-out
  :nst-fnname -simp-nst
  :int-fnname -simp-old-int
  :features (:probe :old-probe :simplify))

(def-esim-sexpr-mv -simp-new-probe
  :out-fnname -simp-out
  :nst-fnname -simp-nst
  :int-fnname -simp-int
  :features (:probe :simplify))

(defmacro 4v-sexpr-to-faig-plain-alist (x onoff)
  `(4v-sexpr-to-faig-alist-fn1 ,x ,onoff nil))

(defmacro 4v-sexpr-to-faig-opt-alist (x onoff)
  `(4v-sexpr-to-faig-alist-fn1 ,x ,onoff t))

;; For variants
(defconst *esim-general-wrapper-template*
  '(defun esim-fnname (mod in st)
     (declare (xargs :guard (and (good-esim-modulep mod)
                                 (template :probe (good-esim-probe-modulep
                                                   mod))
                                 (template :new-probe
                                   (new-good-esim-probe-modulep mod)))))
     (b* (((mv general-nst general-out
               (template (or :probe :new-probe) general-int))
           (esim-sexpr-general-fn mod))
          (restrict-al (make-fast-alist (ap in st)))
          (nst ((template :faig-3v 4v-sexpr-to-faig-opt-alist)
                (template :faig 4v-sexpr-to-faig-plain-alist)
                (template :sexpr esim-4v-sexpr-compose-alist)
                general-nst restrict-al))
          (out ((template :faig-3v 4v-sexpr-to-faig-opt-alist)
                (template :faig 4v-sexpr-to-faig-plain-alist)
                (template :sexpr esim-4v-sexpr-compose-alist)
                general-out restrict-al))
          (template (or :probe :new-probe)
            (int ((template :faig-3v 4v-sexpr-to-faig-opt-alist)
                  (template :faig 4v-sexpr-to-faig-plain-alist)
                  (template :sexpr esim-4v-sexpr-compose-alist)
                  general-int restrict-al)))
          (template (not :top-probe)
            ((with-fast out))
            (out
             (fal-extract (pat-flatten1 (gpl :o mod))
                          out))))
       (fast-alist-free restrict-al)
       (clear-memoize-table (template :faig-3v '4v-sexpr-to-faig-opt)
                            (template :faig '4v-sexpr-to-faig-plain)
                            (template :sexpr (esim-4v-sexpr-compose-fn)))
       (mv nst out (template (or :probe :new-probe) int)))))

(defmacro def-esim-general-wrapper (name general-name
                                         &key format probe)
  (b* ((features (list* format
                        (case probe
                          ((t) '(:probe))
                          (:new '(:new-probe))
                          (:top '(:top-probe))))))
    (replace-templates
     features
     (sublis `((esim-fnname . ,name)
               (esim-sexpr-general-fn  . ,general-name))
             *esim-general-wrapper-template*))))


(def-esim-general-wrapper esim-faig esim-sexpr-general
  :format :faig)
(def-esim-general-wrapper esim-faig-3v esim-sexpr-general
  :format :faig-3v)
(def-esim-general-wrapper esim-faig-probe esim-sexpr-general-probe
  :format :faig :probe t)
(def-esim-general-wrapper esim-faig-probe-3v esim-sexpr-general-probe
  :format :faig-3v :probe t)
(def-esim-general-wrapper esim-faig-probe-top esim-sexpr-general
  :format :faig :probe :top)
(def-esim-general-wrapper esim-faig-probe-top-3v esim-sexpr-general
  :format :faig-3v :probe :top)
(def-esim-general-wrapper esim-faig-new-probe esim-sexpr-general-new-probe
  :format :faig :probe :new)
(def-esim-general-wrapper esim-faig-new-probe-3v esim-sexpr-general-new-probe
  :format :faig-3v :probe :new)
(def-esim-general-wrapper esim-sexpr-probe-top esim-sexpr-general
  :format :sexpr :probe :top)
