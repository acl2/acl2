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
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL2014")
(include-book "wirealist")
(include-book "centaur/esim/esim-sexpr-support" :dir :system)
(include-book "centaur/esim/esim-primitives" :dir :system)
(local (include-book "centaur/vl2014/util/arithmetic" :dir :system))
(local (include-book "esim-lemmas"))
(local (non-parallel-book))

(defxdoc resolving-multiple-drivers
  :parents (e-conversion)
  :short "How we replace multiply driven wires with explicit resolution
modules."

  :long "<p>We want every wire in our E modules to have at most one driver, but
the list of occurrences we get from @(see vl-modinstlist-to-eoccs) could easily
have multiple occurrences all driving the same wire.  We now introduce a
transform to simplify a list of E occurrences, eliminating multiply driven
wires by inserting explicit resolution modules.</p>

<p><b>Note:</b> In this transform we assume that the module's primary inputs
are not driven by any occurrence.  This is something we explicitly check for in
@(see vl-module-make-esim); see the warning about @(':vl-backflow') there.</p>

<p>Given this assumption, we basically need to do three things:</p>

<ol>

<li>Identify when a wire @('W') has multiple occurrences driving it.
Fortunately, this is completely trivial:

@({
 (duplicated-members (collect-signal-list :o occs))
})

</li>

<li>Rewrite each occurrence driving @('W') so that it instead drives some new,
unique, freshly generated wire (say @('W_1'), @('W_2'), ...).  We also need to
remember the names we used for each wire, for step 3.  We do this with the
function @(see vl-res-rewrite-occs).</li>

<li>Insert new occurrences that drive @('W') with the @('(RES W_1 W_2 ...)').
This is done with @(see vl-make-res-occs).</li>

</ol>

<p>The top-level function is @(see vl-add-res-modules), and it just stitches
these steps together.</p>")

(local (xdoc::set-default-parents resolving-multiple-drivers))


(defalist vl-res-sigma-p (x)
  :key (vl-emodwire-p x)
  :val (vl-emodwirelist-p x)
  :keyp-of-nil nil
  :valp-of-nil t
  :parents (resolving-multiple-drivers)
  :short "An alist that records the fresh wires we introduce for multiply
driven wires."

  :long "<p>The basic idea is that if @('W') is a multiply-driven wire, and we
are going to rewrite the occurrences so that they drive @('W_1'), @('W_2'),
... instead of @('W'), then this alist should bind</p>

@({
  W --> (W_1 W_2 ...)
})

<p>In short, this alist will end up saying which wires need to be resolved
together to drive @('W'); see @(see vl-make-res-occs).</p>")


(defsection vl-res-rewrite-pat
  :parents (vl-res-rewrite-occs)
  :short "Rewrite an output pattern to eliminate multiple drivers."

  :long "<p><b>Signature</b>: @(call vl-res-rewrite-pat) returns @('(mv pat'
idx' sigma')').</p>

<p>@('PAT') should be the output pattern for some occurrence, e.g., @('(gpl :o
occ)').  The other arguments are as in @(see vl-res-rewrite-occs).</p>

<p>We replace any multiply driven wires with new, freshly generated names, and
update @('IDX') and @('SIGMA') appropriately to account for the newly generated
names.</p>"

  (defund vl-res-rewrite-pat (pat mds idx sigma)
    "Returns (MV PAT' IDX' SIGMA')"
    (declare (xargs :guard (and (natp idx)
                                (vl-emodwirelist-p (alist-keys mds))
                                (vl-res-sigma-p sigma))
                    :verify-guards nil))
    (b* ((idx (lnfix idx))

         ((when (not pat))
          (mv pat idx sigma))

         ((when (atom pat))
          (b* ((look (hons-get pat mds))
               ((unless look)
                ;; Not a multiply driven wire, so don't rewrite it.
                (mv pat idx sigma))
               ;; Multiply driven, so generate a fresh name, bump up the name
               ;; index, and add the newly generated wire to sigma.
               (idx   (+ 1 idx))
               (fresh (make-vl-emodwire :basename "vl_res" :index idx))
               (prev  (cdr (hons-get pat sigma)))
               (sigma (hons-acons pat (cons fresh prev) sigma)))
            (mv fresh idx sigma)))

         ((mv car idx sigma) (vl-res-rewrite-pat (car pat) mds idx sigma))
         ((mv cdr idx sigma) (vl-res-rewrite-pat (cdr pat) mds idx sigma)))
      (mv (cons car cdr) idx sigma)))

  (local (in-theory (enable vl-res-rewrite-pat)))

  (defmvtypes vl-res-rewrite-pat (nil natp nil))

  (defthm vl-res-sigma-p-of-vl-res-rewrite-pat
    (implies (and (vl-emodwirelist-p (alist-keys mds))
                  (vl-res-sigma-p sigma))
             (vl-res-sigma-p (mv-nth 2 (vl-res-rewrite-pat pat mds idx sigma)))))

  (verify-guards vl-res-rewrite-pat)

  (local (defthm l0
           (implies (maybe-natp idx)
                    (iff (vl-emodwire "vl_res" idx)
                         t))
           :hints(("Goal"
                   :in-theory (disable vl-emodwire-p-of-vl-emodwire)
                   :use ((:instance vl-emodwire-p-of-vl-emodwire
                                    (basename "vl_res")
                                    (index idx)))))))

  (defthm similar-patternsp-of-vl-res-rewrite-pat
    (similar-patternsp (mv-nth 0 (vl-res-rewrite-pat pat mds idx sigma))
                       pat)))


(defsection vl-res-rewrite-occ
  :parents (vl-res-rewrite-occs)
  :short "Rewrite an occurrence to eliminate multiple drivers."

  (defund vl-res-rewrite-occ (occ mds idx sigma)
    "Returns (MV OCC' IDX' SIGMA')"
    (declare (xargs :guard (and (natp idx)
                                (vl-emodwirelist-p (alist-keys mds))
                                (vl-res-sigma-p sigma))))
    (b* ((o                (gpl :o occ))
         ((mv o idx sigma) (vl-res-rewrite-pat o mds idx sigma))
         (occ              (acl2::chgpl :o o occ)))
      (mv occ idx sigma)))

  (local (in-theory (enable vl-res-rewrite-occ)))

  (defmvtypes vl-res-rewrite-occ (nil natp nil))

  (defthm vl-res-sigma-p-of-vl-res-rewrite-occ
    (implies (and (vl-emodwirelist-p (alist-keys mds))
                  (vl-res-sigma-p sigma))
             (vl-res-sigma-p (mv-nth 2 (vl-res-rewrite-occ occ mds idx sigma)))))

  (defthm good-esim-occp-of-vl-res-rewrite-occ
    (implies (good-esim-occp occ)
             (good-esim-occp (mv-nth 0 (vl-res-rewrite-occ occ mds idx sigma))))
    :hints(("Goal" :in-theory (enable good-esim-occp)))))


(defsection vl-res-rewrite-occs
  :parents (resolving-multiple-drivers)
  :short "Rewrite occurrences to drive new, fresh wires instead of multiply
driven wires."

  :long "<p><b>Signature:</b> @(call vl-res-rewrite-occs) returns @('(mv occs'
idx' sigma')').</p>

<ul>

<li>@('MDS') (\"multiply drivens\") says which wires have multiple drivers.
Since we need to be able to quickly look up whether a wire needs to be
rewritten, MDS is a fast alist whose keys are the @(see vl-emodwire-p)s that
are multiply driven.  The values are irrelevant.  This alist isn't changed
during the course of the rewriting.</li>

<li>@('IDX') is a name index used for fresh name generation.  We expect that it
is initially set to the highest index of any emodwire in the module whose
basename is @('vl_res').  We increment it whenever we need to create a new,
fresh wire.</li>

<li>@('SIGMA') is a @(see vl-res-sigma-p) that we use to record the names of
the new wires that are being driven.  It starts empty and eventually should
bind every emodwire @('w') in @('MDS') to the list of new names being driven
instead of @('w').</li>

</ul>"

  (defund vl-res-rewrite-occs (occs mds idx sigma)
    "Returns (MV OCCS' IDX' SIGMA')"
    (declare (xargs :guard (and (natp idx)
                                (vl-emodwirelist-p (alist-keys mds))
                                (vl-res-sigma-p sigma))))
    (b* (((when (atom occs))
          (mv nil (lnfix idx) sigma))
         ((mv car idx sigma) (vl-res-rewrite-occ (car occs) mds idx sigma))
         ((mv cdr idx sigma) (vl-res-rewrite-occs (cdr occs) mds idx sigma)))
      (mv (cons car cdr) idx sigma)))

  (local (in-theory (enable vl-res-rewrite-occs)))

  (defmvtypes vl-res-rewrite-occs (true-listp natp nil))

  (defthm vl-res-sigma-p-of-vl-res-rewrite-occs
    (implies (and (vl-emodwirelist-p (alist-keys mds))
                  (vl-res-sigma-p sigma))
             (vl-res-sigma-p (mv-nth 2 (vl-res-rewrite-occs occ mds idx sigma)))))

  (defthm good-esim-occsp-of-vl-res-rewrite-occs
    (implies (good-esim-occsp occ)
             (good-esim-occsp (mv-nth 0 (vl-res-rewrite-occs occ mds idx sigma))))
    :hints(("Goal" :in-theory (enable good-esim-occsp)))))





; Part 3.  We now want to generate the resolution module occurrences that will
; drive each multiply-driven wire with the fresh drivers we've built for it.
; The SIGMA we've built tells us exactly what we need to know: it binds each
; multiply driven wire to the new drivers we've generated for it.

(defsection vl-make-res-sexpr
  :parents (vl-make-res-occs)
  :short "Generate a @(see acl2::4v-res) expression to resolve a list of
emodwires."

  :long "<p>@(call vl-make-res-sexpr) generates a <see topic='@(url
acl2::4v-sexprs)'>4v-sexpr</see> that joins together all of its arguments with
@(see acl2::4v-res) operations.</p>

<p>Note that the RES operation is commutative and associative, so any nest of
RES operations is equivalent.  So, we just resolve the arguments in a
straightforward, right-associative manner.</p>"

  #!ACL2
  (local (defthm 4v-res-commutes ;; just to show it commutes
           (equal (4v-res a b)
                  (4v-res b a))))

  #!ACL2
  (local (defthm 4v-res-is-associative ;; just to show it is associative
           (equal (4v-res (4v-res a b) c)
                  (4v-res a (4v-res b c)))))

  (defund vl-make-res-sexpr (args)
    ;; Builds the 4v-sexpr for (RES ARG1 (RES ARG2 (RES ... ARGN))).
    (declare (xargs :guard (vl-emodwirelist-p args)))
    (cond ((atom args)
           ;; We'll allow no arguments -- resolving nothing gives you Z.
           acl2::*4vz-sexpr*)
          ((atom (cdr args))
           ;; Resolving a single argument just gives you that arg.
           (car args))
          (t
           ;; Resolving anything else gives you a nest of RESes.
           (acl2::hons-list 'acl2::res (car args)
                            (vl-make-res-sexpr (cdr args))))))


  (local (defthm l0
           ;; The vl-emodwirelist-p hyp here ensures that the args are non-nil
           ;; atoms.  The 4v-sexpr-vars function could get confused if NIL was
           ;; permitted, for instance.
           (implies (vl-emodwirelist-p args)
                    (equal (set::in a (acl2::4v-sexpr-vars (vl-make-res-sexpr args)))
                           (if (member-equal a args)
                               t
                             nil)))
           :hints(("Goal"
                   :in-theory (enable vl-make-res-sexpr
                                      acl2::4v-sexpr-vars)
                   :induct (vl-make-res-sexpr args)))))

  (defthm 4v-sexpr-vars-of-vl-make-res-sexpr
    (implies (force (vl-emodwirelist-p args))
             (equal (acl2::4v-sexpr-vars (vl-make-res-sexpr args))
                    (set::mergesort args)))
    :hints((set-reasoning))))



(defsection vl-make-n-bit-res-module
  :parents (vl-make-res-occs)
  :short "Make an E module to resolve together N inputs into a single output."

  :long "<p>@(call vl-make-n-bit-res-module) constructs an E module.  This
models what happens when we drive the same wire with multiple values.  There's
no notion of strengths here; the wires all have to agree on their value (or be
floating) for a good result to come out.</p>

<p>Note that this works even for N=0 (in which case it just always emits Z) and
for N=1 (in which case it acts like an ordinary assignment).</p>"

  (defund vl-make-n-bit-res-module (n)
    (declare (xargs :guard (natp n)))
    (b* ((name      (vl-starname (cat "VL_" (natstr n) "_BIT_RES")))
         (ins       (and (posp n) (vl-emodwires-from-high-to-low "A" (- n 1) 0)))
         (out       (vl-plain-wire-name "O"))
         ;; Note: in-pat and out-pat here must agree with
         ;; vl-make-resolution-occ below.
         (in-pat    (and (posp n) (list ins)))
         (out-pat   (list (list out)))
         (out-alist (list (cons out (vl-make-res-sexpr ins))))
         (x         (list :out out-alist)))
      (list :n name :i in-pat :o out-pat :x x)))

  ;; It's probably silly to memoize this, but it may avoid some consing...
  (memoize 'vl-make-n-bit-res-module)

  (local (in-theory (enable vl-make-n-bit-res-module)))

  (local (in-theory (disable acl2::hons-subset)))

  (local (defthm c0
           (implies (and (atom-listp x)
                         (not (member nil x)))
                    (equal (pat-flatten1 x)
                           x))
           :hints(("Goal" :in-theory (enable atom-listp)))))

  (local (defthm c1
           (implies (vl-emodwirelist-p x)
                    (equal (atom-listp x)
                           (true-listp x)))
           :hints(("Goal" :induct (len x)))))

  (local (defthm c2
           (implies (vl-emodwirelist-p x)
                    (not (member nil x)))))

  (defthm good-esim-primitivep-of-vl-make-n-bit-res-module
    (implies (natp n)
             (good-esim-primitivep (vl-make-n-bit-res-module n)))
    :hints(("Goal" :in-theory (enable good-esim-primitivep))))

  (local (defthm d0
           (implies (member-equal a x)
                    (member-equal (vl-emodwire->basename a) (vl-emodwirelist->basenames x)))
           :hints(("Goal" :induct (len x)))))

  (local (defthm d1
           (implies (not (equal (vl-emodwire->basename a) (string-fix name)))
                    (not (member-equal a (vl-emodwires-from-high-to-low name high low))))
           :hints(("Goal"
                   :in-theory (disable d0)
                   :use ((:instance d0
                                    (a a)
                                    (x (vl-emodwires-from-high-to-low name high low))))))))

  (defthm good-esim-modulep-of-vl-make-n-bit-res-module
    (implies (natp n)
             (good-esim-modulep (vl-make-n-bit-res-module n)))
    :hints(("Goal"
            :in-theory (e/d (good-esim-modulep
                             good-esim-primitivep
                             )
                            ;; BOZO some of this is redundant and can be cleaned up
                            (;NO-DUPLICATESP-EQUAL-WHEN-SAME-LENGTH-MERGESORT
                             ;; leaving this one enabled--- NO-DUPLICATESP-EQUAL-OF-APPEND
                             ACL2::NO-DUPLICATESP-EQUAL-APPEND-IFF
                             acl2::NO-DUPLICATESP-EQUAL-OF-APPEND-OF-APPEND))))))



(defsection vl-make-res-occ
  :parents (vl-make-res-occs)
  :short "Generate and instantiate an appropriate resolution module to drive a
wire to multiple values."

  :long "<p>@(call vl-make-res-occ) builds an E occurrence that simultaneously
drives @('out') to all of the values on @('ins').</p>"

  (defund vl-make-res-occ (name out ins)
    (declare (xargs :guard (and (vl-emodwire-p out)
                                (vl-emodwirelist-p ins)
                                (true-listp ins)
                                (uniquep ins))))
    (b* ((n  (len ins))
         (op (vl-make-n-bit-res-module n))
         ;; Note: The i/o here must agree with in-pat and out-pat from
         ;; vl-make-n-bit-res-module above.
         (i (and (posp n) (list ins)))
         (o (list (list out))))
      (list :u name :op op :i i :o o)))

  (local (in-theory (enable vl-make-res-occ)))

  (local (defthm similar-patternsp-when-emodwires-of-same-length
           (implies (and (vl-emodwirelist-p x)
                         (vl-emodwirelist-p y)
                         (true-listp x)
                         (true-listp y))
                    (equal (similar-patternsp x y)
                           (equal (len x) (len y))))))

  (local (defthm outs-of-vl-make-n-bit-res-module
           (equal (gpl :o (vl-make-n-bit-res-module n))
                  (list (list (vl-plain-wire-name "O"))))
           :hints(("Goal" :in-theory (enable vl-make-n-bit-res-module)))))

  (local (defthm ins-of-vl-make-n-bit-res-module
           (equal (gpl :i (vl-make-n-bit-res-module n))
                  (and (posp n)
                       (list (vl-emodwires-from-high-to-low "A" (- n 1) 0))))
           :hints(("Goal" :in-theory (enable vl-make-n-bit-res-module)))))

  (defthm good-esim-occp-of-vl-make-res-occ
    (implies (and (force (vl-emodwire-p out))
                  (force (vl-emodwirelist-p ins))
                  (force (true-listp ins))
                  (force (uniquep ins))
                  (force name))
             (good-esim-occp (vl-make-res-occ name out ins)))
    :hints(("Goal" :in-theory (enable good-esim-occp)))))


(defsection vl-make-res-occs
  :parents (resolving-multiple-drivers)
  :short "Convert the @(see vl-res-sigma-p) database into a list of E
occurrences to drive each multiply driven wire."

  :long "<p>@(call vl-make-res-occs) takes @('idx'), an index for fresh name
generation, and @('sigma'), which should be the <b>already shrunk</b> @(see
vl-res-sigma-p) obtained from @(see vl-res-rewrite-occs).  Recall that the
alist binds, e.g.,</p>

@({
  W --> (W_1 W_2 ... W_n)
})

<p>Where @('W') was the name of some original, multiply-driven wire, and
@('W_1, \dots') are the freshly generated names that are now being driven
instead of W.  The idea is to build a new occurrence that drives W to the
resolution of W1...Wn, for each such W.</p>"

  (defund vl-make-res-occs (idx sigma)
    ;; Sigma must be pre-shrunk.  We make a driver occurrence for each of its
    ;; entries.  IDX is used for name generation.
    "Returns (MV OCCS IDX')"
    (declare (xargs :guard (and (natp idx)
                                (vl-res-sigma-p sigma))))
    (b* ((idx (lnfix idx))
         ((when (atom sigma))
          (mv nil idx))
         (out1  (caar sigma))
         (ins1  (cdar sigma))
         (idx   (+ 1 idx))
         (fresh (make-vl-emodwire :basename "vl_res" :index idx))
         ((unless (and (true-listp ins1)
                       (uniquep ins1)))
          ;; Should be impossible by how SIGMA is constructed.
          (er hard? 'vl-make-res-occs "Failed to generate unique drivers!")
          (mv nil idx))
         (occ1  (vl-make-res-occ fresh out1 ins1))
         ((mv rest idx) (vl-make-res-occs idx (cdr sigma))))
      (mv (cons occ1 rest) idx)))

  (local (in-theory (enable vl-make-res-occs)))

  (defmvtypes vl-make-res-occs (true-listp natp))

  (local (defthm l0
           (implies (maybe-natp idx)
                    (iff (vl-emodwire "vl_res" idx)
                         t))
           :hints(("Goal"
                   :in-theory (disable vl-emodwire-p-of-vl-emodwire)
                   :use ((:instance vl-emodwire-p-of-vl-emodwire
                                    (basename "vl_res")
                                    (index idx)))))))

  (defthm good-esim-occsp-of-vl-make-res-occs
    (implies (and (force (natp idx))
                  (force (vl-res-sigma-p sigma)))
             (good-esim-occsp (mv-nth 0 (vl-make-res-occs idx sigma))))
    :hints(("Goal" :in-theory (enable good-esim-occsp)))))





(defsection vl-add-res-modules
  :parents (resolving-multiple-drivers)
  :short "Top-level function for resolving multiple drivers in a list of E
occurrences."

  :long "<p><b>Signature:</b> @(call vl-add-res-modules) returns
@('occs'').</p>

<p>@('occs') should be a preliminary list of occurrences, e.g., generated
perhaps by @(see vl-modinst-to-eocc) along with other occurrences for driving
T/F, undriven outputs, etc.  These occurrences are presumably not yet
well-formed because the same wire may be driven by multiple occs.</p>

<p>@('all-names') must be a @(see vl-emodwirelist-p) that captures the module's
namespace.  We expect it to include at least:</p>

<ul>
<li>All signals in :i and :o for the module</li>
<li>All signals used in :i and :o patterns in occs</li>
<li>The names of all occs (i.e., the :u from each occ)</li>
</ul>

<p>However, as a special exception, @('all-names') may exclude names that we
know cannot have the basename @('vl_res'), because any wires we are going to
introduce are either already used in @('occs') or are going to have the form
@('vl_res[k]').  This includes, for instance, the names added during @(see
vl-add-zdrivers) and for driving the T and F wires.</p>"

  (defund vl-add-res-modules (all-names occs)
    "Returns OCCS'"
    (declare (xargs :guard (and (vl-emodwirelist-p all-names)
                                (vl-emodwirelist-p (acl2::collect-signal-list :o occs)))))
    (b* ((multiply-driven
          ;; Note that we don't include :i as drivers because we separately
          ;; insist that no inputs are ever driven.
          (duplicated-members (acl2::collect-signal-list :o occs)))

         ((unless multiply-driven)
          ;; Optimization: when there aren't any multiply driven wires, we don't
          ;; need to do anything.  This possibly saves a lot of string
          ;; comparisons to figure out the max index, a lot of traversal of the
          ;; occs, etc.
          occs)

         (idx   (vl-emodwirelist-highest "vl_res" all-names))
         (mds   (make-lookup-alist multiply-driven))
         (sigma (len multiply-driven)) ;; probably a reasonably good size hint
         ((mv rw-occs idx sigma)
          (vl-res-rewrite-occs occs mds idx sigma))
         (sigma (b* ((tmp (hons-shrink-alist sigma nil)))
                  (fast-alist-free sigma)
                  tmp))
         ((mv res-occs ?idx)
          (vl-make-res-occs idx sigma)))
      (fast-alist-free mds)
      (fast-alist-free sigma)
      (append rw-occs res-occs)))

  (local (in-theory (enable vl-add-res-modules)))

  (defthm true-listp-of-vl-add-res-modules
    (implies (true-listp occs)
             (true-listp (vl-add-res-modules all-names occs)))
    :rule-classes :type-prescription)

  (defthm good-esim-occsp-of-vl-add-res-modules
    (implies (and (force (good-esim-occsp occs))
                  (force (vl-emodwirelist-p (acl2::collect-signal-list :o occs))))
             (good-esim-occsp (vl-add-res-modules all-names occs)))))
