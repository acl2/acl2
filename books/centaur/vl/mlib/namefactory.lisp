; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "../util/namedb")
(include-book "modnamespace")
(local (include-book "../util/arithmetic"))


(defun vl-namefactory-okp (mod namedb)
  ;; Note: we leave this enabled!
  (declare (xargs :guard (and (vl-maybe-module-p mod)
                              (vl-namedb-p namedb))))
  (and (or (not mod)
           (equal (vl-namedb->names namedb) nil)
           (subsetp-equal (vl-module->modnamespace mod)
                          (vl-namedb-allnames namedb)))
       (vl-namedb-okp (vl-namedb->names namedb)
                      (vl-namedb->pmap namedb)
                      (vl-namedb->pset namedb))))

(defaggregate vl-namefactory
  (mod namedb)
  :tag :vl-namefactory
  :legiblep nil
  :require ((vl-maybe-module-p-of-vl-namefactory->mod  (vl-maybe-module-p mod))
            (vl-namedb-p-of-vl-namefactory->namedb (vl-namedb-p namedb))

            (vl-namefactory-okp-when-vl-namefactory-p
             (vl-namefactory-okp mod namedb)))
  :parents (mlib)

  :short "Produces fresh names for a module."

  :long "<p>A <b>name factory</b> allows you to easily and efficiently generate
good, fresh names that are not being used elsewhere in a module.</p>

<h3>Using Name Factories</h3>

<p>Typically, given some module <tt>mod</tt>, the user begins by constructing a
name factory using <tt>(@(see vl-starting-namefactory) mod)</tt>.  Note that it
is quite cheap to construct a name factory in this way; all expense is delayed
until the first use of the factory.</p>

<p>Once constructed, name factories must be used in a single-threaded
discipline.  That is, the functions for generating names actually return
<tt>(mv fresh-name factory-prime)</tt>, and to ensure that a sequence of
generated names are unique, one must always use the most recently returned
factory to generate subsequent names.</p>

<p>Two functions are provided for generating names:</p>

<p><tt>(@(see vl-namefactory-indexed-name) prefix nf)</tt> produces a name that
looks like <tt>prefix_n</tt>, where <tt>n</tt> is the smallest positive natural
number <tt>n</tt> such that the name <tt>prefix_n</tt> is not in use.</p>

<p><tt>(@(see vl-namefactory-plain-name) name nf)</tt> attempts to return
<tt>name</tt> verbatim.  When this is not possible, a name of the form
<tt>name_n</tt>, a note will be printed to standard output and instead we will
produce a name with <tt>vl-namefactory-indexed-name</tt>.</p>

<p>We use these functions for different purposes.  We think that @(see
vl-namefactory-indexed-name) should be used for \"throwaway\" names that don't
need to be reliable or understandable, such as the names of temporary wires to
be generated for split-up expressions.  Meanwhile, @(see
vl-namefactory-plain-name) should be used for splitting up instance names or in
any other cases where a reliable name is desired.</p>

<p>Because name factories make use of fast alists, they should be destroyed
with <tt>(@(see vl-free-namefactory) nf)</tt> when you are done using them.</p>


<h3>Freshness Guarantee</h3>

<p>To establish that name factories generate only fresh names, we introduce the
function <tt>(@(see vl-namefactory-allnames) nf)</tt>.  This function returns a
list of all names that the name factory currently considers to be in use.  We
prove:</p>

<ul>

<li>Every name in the @(see vl-module->modnamespace) of <tt>mod</tt> is among
the <tt>allnames</tt> of the initial name factory produced by
<tt>(vl-starting-namefactory mod).</tt></li>

<li>The <tt>fresh-name</tt>s returned by @(see vl-namefactory-indexed-name) or
@(see vl-namefactory-plain-name) are not members of the <tt>allnames</tt> of
the input factory.</li>

<li>The <tt>allnames</tt> of the resulting <tt>factory-prime</tt> include
exactly the <tt>allnames</tt> of the input <tt>factory</tt>, along with the
generated <tt>fresh-name</tt>.</li>

</ul>

<p>Together, these theorems ensure that, when properly used, the name factory
will only give you fresh names.</p>


<h3>Mod-free Namefactories</h3>

<p>It is also possible to create a name factory without a module using @(see
vl-empty-namefactory).  This is occasionally useful when generating new
modules.  The freshness guarantee is that the <tt>allnames</tt> of the empty
name factory is empty.</p>


<h3>Motivation and History</h3>

<p>Name generation is a surprisingly important and difficult problem.  It needs
to be very efficient: we have sometimes found that tens of thousands of fresh
names are needed.  Toward this goal, our original approach was as follows:</p>

<ul>

<li>Our generated names always looked like <tt>_gen_1</tt>, <tt>_gen_2</tt>,
etc.</li>

<li>When the first name was needed, a transform would examine the module's
namespace for the largest <tt>n</tt> such that <tt>_gen_n</tt> was already in
use.  The name <tt>_gen_{n+1}</tt> would then be used as the first new
name.</li>

<li>Subsequently, any number of fresh names could then be generated by simply
increasing the index.  That is, the second name fresh name would be
<tt>_gen_{n+2}</tt>, the third <tt>_gen_{n+3}</tt>, and so on.</li>

</ul>

<p>This scheme was highly efficient because the module's namespace only needed
to be consulted when generating the first wire's name.  This meant that for
large modules, generating thousands of names was not very expensive.  It also
meant that if no fresh names were needed, then the module's namespace was never
even computed.</p>

<p>But a problem with this scheme is that the generated names are not very good
or predictable.  This was particularly problematic when instance arrays
like:</p>

<code>
basic_flop data [(width - 1):0] (q, ph1, d);
</code>

<p>would be transformed into something like:</p>

<code>
basic_flop _gen_19 (q[0], ph1, d[0]);
basic_flop _gen_18 (q[1], ph1, d[1]);
basic_flop _gen_17 (q[2], ph1, d[2]);
</code>

<p>that is, here the instance name <tt>data</tt> has been entirely lost and
replaced with a bunch of unrelated, stupid names that might easily change when
the module is translated in the future.</p>

<p>Name factories basically extend this scheme to allow much better names to be
generated, while still being quite efficient.</p>


<h3>Implementation</h3>

<p>A name factory has four fields:</p>

<ul>
<li><tt>mod</tt>, the module that we are generating names for, or <tt>nil</tt>
if there is no such module (e.g., for empty name factories).</li>
<li><tt>modns</tt>, a fast alist that associates strings to <tt>t</tt>.</li>
<li><tt>pmap</tt>, a fast alist that associates strings to natural numbers.</li>
<li><tt>plist</tt>, a fast alist that associates strings to <tt>t</tt>.</li>
</ul>

<p><u>Invariant A1</u>.  Either <tt>modns</tt> is <tt>nil</tt>, or, when
<tt>mod</tt> is non-nil, every name in the @(see vl-module->modnamespace) of
<tt>mod</tt> must be bound in it.</p>

<p><u>Invariant B1</u>.  The <tt>pmap</tt> is empty whenever <tt>modns</tt> is
empty.</p>

<p><u>Invariant B2</u>.  Each <tt>prefix</tt> bound in <tt>pmap</tt> is bound
to <tt>(@(see vl-pgenstr-highest) prefix (strip-cars modns))</tt>.</p>

<p><u>Invariant C1</u>.  The <tt>plist</tt> binds exactly those
<tt>prefix</tt>es that are bound in <tt>pmap</tt>.</p>

<p>Intuitively, the <tt>modns</tt> represents the set of all names that are
currently in use.  We use a fast-alist representation so that we can very
quickly determine whether a plain name is available.</p>

<p>Meanwhile, the <tt>pmap</tt> allows us to use something much like the
\"historic scheme\" to quickly generate indexed names.  In particular, it binds
some prefixes with their highest used index.  This way, we only need to scan
the <tt>modns</tt> once per prefix.</p>

<p>The <tt>plist</tt> is really just an optimization that allows us to avoid
needing to shrink the plists.  See the discussion in @(see
vl-compatible-with-prefix-set-p) for details.</p>")

;; (defthm vl-namefactory->pmap-when-no-modns
;;   (implies (and (not (vl-namefactory->modns x))
;;                 (force (vl-namefactory-p x)))
;;            (not (vl-namefactory->pmap x)))
;;   :hints(("Goal"
;;           :in-theory (disable vl-namefactory-okp-when-vl-namefactory-p)
;;           :use ((:instance vl-namefactory-okp-when-vl-namefactory-p)))))

(defthm subsetp-equal-of-modnamespace-when-vl-namefactory-p
  (implies (and (vl-namedb->names (vl-namefactory->namedb x))
                (vl-namefactory->mod x)
                (force (vl-namefactory-p x)))
           (subsetp-equal (vl-module->modnamespace (vl-namefactory->mod x))
                          (vl-namedb-allnames (vl-namefactory->namedb x))))
  :hints(("Goal"
          :in-theory (disable vl-namefactory-okp-when-vl-namefactory-p)
          :use ((:instance vl-namefactory-okp-when-vl-namefactory-p)))))

;; (defthm vl-namefactory->pset-under-subsetp-equiv
;;   (implies (force (vl-namefactory-p x))
;;            (subsetp-equiv (strip-cars (vl-namefactory->pset x))
;;                           (strip-cars (vl-namefactory->pmap x))))
;;   :hints(("Goal"
;;           :in-theory (disable vl-namefactory-okp-when-vl-namefactory-p)
;;           :use ((:instance vl-namefactory-okp-when-vl-namefactory-p)))))

;; (defthm hons-assoc-equal-of-vl-namefactory->pmap
;;   ;; This is better than HONS-ASSOC-EQUAL-WHEN-VL-PREFIX-MAP-CORRECT-P, because
;;   ;; we avoid the free variable NAMES by explicitly saying to consider the cars
;;   ;; of MODNS.
;;   (implies (and (vl-namefactory-p factory)
;;                 (hons-assoc-equal prefix (vl-namefactory->pmap factory)))
;;            (equal (hons-assoc-equal prefix (vl-namefactory->pmap factory))
;;                   (let ((names (strip-cars (vl-namefactory->modns factory))))
;;                     (cons prefix (vl-pgenstr-highest prefix names)))))
;;   :hints(("goal"
;;           :in-theory (disable hons-assoc-equal-when-vl-prefix-map-correct-p)
;;           :use ((:instance hons-assoc-equal-when-vl-prefix-map-correct-p
;;                            (pmap (vl-namefactory->pmap factory))
;;                            (names (strip-cars (vl-namefactory->modns factory))))))))



(defsection vl-namefactory-maybe-initialize

  ;; Make sure that the modnamespace is computed, or generate it if it isn't
  ;; available already.  We could do this as part of vl-starting-namefactory
  ;; instead, but this allows us to make vl-starting-namefactory very cheap and
  ;; avoid computing the modnamespace if it isn't used.
 
  (defund vl-namefactory-maybe-initialize (factory)
    (declare (xargs :guard (vl-namefactory-p factory)
                    :guard-hints (("goal" :in-theory (enable vl-namedb-allnames)))))
    (if (vl-namedb->names (vl-namefactory->namedb factory))
        factory
      (let* ((mod   (vl-namefactory->mod factory))
             (modns (and mod
                         (make-lookup-alist (vl-module->modnamespace mod)))))
        (change-vl-namefactory factory :namedb
                               (change-vl-namedb
                                (vl-namefactory->namedb factory)
                                :names modns)))))

  (local (in-theory (enable vl-namefactory-maybe-initialize)))

  (defthm vl-namefactory-p-of-vl-namefactory-maybe-initialize
    (implies (force (vl-namefactory-p factory))
             (vl-namefactory-p (vl-namefactory-maybe-initialize factory)))
    :hints(("Goal" :in-theory (e/d (vl-namedb-allnames)
                                   (pick-a-point-subsetp-equal-strategy
                                    (force))))))

  (defthm vl-namefactory->mod-of-vl-namefactory-maybe-initialize
    (equal (vl-namefactory->mod (vl-namefactory-maybe-initialize factory))
           (vl-namefactory->mod factory))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm subsetp-equal-of-modnamespace-and-vl-namefactory-maybe-initialize
    (implies (and (vl-namefactory->mod factory)
                  (force (vl-namefactory-p factory)))
             (subsetp-equal
              (vl-module->modnamespace (vl-namefactory->mod factory))
              (vl-namedb-allnames (vl-namefactory->namedb
                                   (vl-namefactory-maybe-initialize
                                    factory)))))
    :hints(("Goal" :in-theory (e/d ()
                                   (pick-a-point-subsetp-equal-strategy)))
           (and stable-under-simplificationp
                '(:in-theory (e/d (vl-namedb-allnames)
                                  (pick-a-point-subsetp-equal-strategy)))))
    :rule-classes ((:rewrite)
                   (:forward-chaining :trigger-terms
                                      ((vl-namefactory-maybe-initialize factory))))))



(defsection vl-namefactory-allnames
  :parents (vl-namefactory-p)

  :short "@(call vl-namefactory-p) returns a list of all names that are
considered to be used by the name factory."

  :long "<p>This function is not particularly efficient, and probably should
not ordinarily be executed in real programs.  Its main purpose is to establish
the freshness guarantee for name factories, described in @(see
vl-namefactory-p).</p>"

  (defund vl-namefactory-allnames (factory)
    (declare (xargs :guard (vl-namefactory-p factory)
                    :verify-guards nil))
    (mbe :logic
         (vl-namedb-allnames
          (vl-namefactory->namedb
           (vl-namefactory-maybe-initialize factory)))
         :exec
         (let ((mod   (vl-namefactory->mod factory))
               (namedb (vl-namefactory->namedb factory)))
           (cond ((vl-namedb->names namedb)
                  (vl-namedb-allnames namedb))
                 (mod
                  (vl-module->modnamespace mod))
                 (t
                  nil)))))

  (local (in-theory (enable vl-namefactory-allnames
                            vl-namedb-allnames
                            vl-namefactory-maybe-initialize)))

  (verify-guards vl-namefactory-allnames)

  (defthm vl-namefactory-allnames-of-vl-namefactory-maybe-initialize
    (equal (vl-namefactory-allnames (vl-namefactory-maybe-initialize factory))
           (vl-namefactory-allnames factory))
    :hints(("Goal" :in-theory (disable (force))))))



(defsection vl-starting-namefactory
  :parents (vl-namefactory-p)
  :short "@(call vl-starting-namefactory) creates a name factory for a module."
  :long "<p>This function is very cheap to call because the real work of
initializing the name factory is deferred to its first use.  See @(see
vl-namefactory-p) for all name factory documentation.</p>"

  (defund vl-starting-namefactory (mod)
    (declare (xargs :guard (vl-module-p mod)
                    :guard-hints (("goal" :in-theory (disable
                                                      pick-a-point-subsetp-equal-strategy))
                                  (and stable-under-simplificationp
                                       '(:in-theory (enable vl-empty-namedb))))))
    (make-vl-namefactory :mod mod :namedb (vl-empty-namedb)))

  (local (in-theory (enable vl-starting-namefactory)))

  (defthm vl-namefactory-p-of-vl-starting-namefactory
    (implies (force (vl-module-p mod))
             (vl-namefactory-p (vl-starting-namefactory mod)))
    :hints(("Goal" :in-theory (e/d (vl-empty-namedb) ((force))))))

  (defthm vl-namefactory-allnames-of-vl-starting-namefactory
    (implies (force (vl-module-p mod))
             (equal (vl-namefactory-allnames (vl-starting-namefactory mod))
                    (vl-module->modnamespace mod)))
    :hints(("Goal" :in-theory (e/d (vl-namefactory-allnames
                                    vl-namedb-allnames
                                    vl-namefactory-maybe-initialize)
                                   ((force))))
           (and stable-under-simplificationp
                '(:in-theory (e/d (vl-empty-namedb) ((force))))))))



(defsection vl-empty-namefactory
  :parents (vl-namefactory-p)
  :short "@(call vl-empty-namefactory) creates an empty name factory without
a module."

  :long "<p>Usually you should use @(see vl-starting-namefactory) instead;
<tt>vl-starting-namefactory</tt> automatically regards all of the names in the
module as used, whereas <tt>vl-empty-namefactory</tt> regards no names as
used.</p>

<p>On the other hand, <tt>vl-empty-namefactory</tt> may be useful when you are
generating modules from scratch and, hence, don't have a module to give to
<tt>vl-starting-namefactory</tt> yet.</p>"

  (defund vl-empty-namefactory ()
    (declare (xargs :guard t))
    (make-vl-namefactory :mod nil :namedb (vl-empty-namedb)))

  (in-theory (disable (:executable-counterpart vl-empty-namefactory)))

  (local (in-theory (enable vl-empty-namefactory
                            vl-empty-namedb)))

  (defthm vl-namefactory-p-of-vl-empty-namefactory
    (vl-namefactory-p (vl-empty-namefactory)))

  (defthm vl-namefactory-allnames-of-vl-empty-namefactory
    (equal (vl-namefactory-allnames (vl-empty-namefactory))
           nil)))



(defsection vl-namefactory-indexed-name
  :parents (vl-namefactory-p)
  :short "@(call vl-namefactory-indexed-name) constructs a fresh name that
looks like <tt>prefix_n</tt> for some natural number <tt>n</tt>, and returns
<tt>(mv fresh-name factory-prime)</tt>."

  (defund vl-namefactory-indexed-name (prefix factory)
    "Returns (MV FRESH-NAME FACTORY-PRIME)"
    (declare (xargs :guard (and (stringp prefix)
                                (vl-namefactory-p factory))
                    :verify-guards nil))
    (b* ((factory (vl-namefactory-maybe-initialize factory))
         ((mv newname db-prime)
          (vl-namedb-indexed-name prefix (vl-namefactory->namedb factory)))

         (factory (change-vl-namefactory factory :namedb db-prime)))
        (mv newname factory)))

  (local (in-theory (enable vl-namefactory-indexed-name)))

  ;; (local (defthm lemma
  ;;          (implies (and (vl-prefix-map-correct-p-aux domain pmap names)
  ;;                        (string-listp domain)
  ;;                        (stringp prefix))
  ;;                   (vl-prefix-map-correct-p-aux
  ;;                    domain
  ;;                    (cons (cons prefix (+ 1 (vl-pgenstr-highest prefix names))) pmap)
  ;;                    (cons (vl-pgenstr prefix (+ 1 (vl-pgenstr-highest prefix names))) names)))
  ;;          :hints(("Goal"
  ;;                  :in-theory (enable vl-prefix-map-correct-p-aux)
  ;;                  :do-not '(generalize fertilize)))))

  (local (defthm lemma2
           (implies (hons-assoc-equal prefix pmap)
                    (member-equal prefix (strip-cars pmap)))))

  ;; (local (defthm lemma3
  ;;          (implies (and (vl-prefix-map-correct-p pmap names)
  ;;                        (vl-string-keys-p pmap)
  ;;                        (stringp prefix))
  ;;                   (vl-prefix-map-correct-p
  ;;                    (cons (cons prefix (+ 1 (vl-pgenstr-highest prefix names))) pmap)
  ;;                    (cons (vl-pgenstr prefix (+ 1 (vl-pgenstr-highest prefix names))) names)))
  ;;          :hints(("goal" :in-theory (enable vl-prefix-map-correct-p)))))

  (verify-guards vl-namefactory-indexed-name)

  (defthm stringp-of-vl-namefactory-indexed-name
    (stringp (mv-nth 0 (vl-namefactory-indexed-name prefix factory)))
    :rule-classes :type-prescription)

  (defthm vl-namefactory-p-of-vl-namefactory-indexed-name
    (implies (and (force (vl-namefactory-p factory))
                  (force (stringp prefix)))
             (vl-namefactory-p (mv-nth 1 (vl-namefactory-indexed-name prefix factory)))))

  (defthm vl-namefactory-allnames-of-vl-namefactory-indexed-name
    (implies (force (vl-namefactory-p factory))
             (equal (vl-namefactory-allnames
                     (mv-nth 1 (vl-namefactory-indexed-name prefix factory)))
                    (cons
                     (mv-nth 0 (vl-namefactory-indexed-name prefix factory))
                     (vl-namefactory-allnames factory))))
    :hints (("Goal"
             :in-theory (enable vl-namefactory-maybe-initialize
                                vl-namefactory-allnames)
             :do-not-induct t))
    :otf-flg t)

  (defthm vl-namefactory-indexed-name-is-fresh
    (implies (and (force (stringp prefix))
                  (force (vl-namefactory-p factory)))
             (not (member-equal
                   (mv-nth 0 (vl-namefactory-indexed-name prefix factory))
                   (vl-namefactory-allnames factory))))
    :hints(("Goal" :in-theory (enable vl-namefactory-allnames
                                      vl-namefactory-maybe-initialize)))))



;; (defsection vl-unlike-any-prefix-p
;;   :parents (vl-namefactory-p)
;;   :short "@(call vl-unlike-any-prefix-p) determines whether for all <tt>p</tt>
;; in <tt>prefixes</tt>, <tt>(@(see vl-pgenstr-p) p name)</tt> is false."

;;   :long "<p>We use this function in the implementation of @(see
;; vl-namefactory-plain-name).  When requesting a plain name, one might ask for a
;; name like <tt>foo_3</tt>, which could screw up the prefix map if we are using
;; <tt>foo</tt> as a prefix.</p>

;; <p>One solution would be to fix up the prefix map when this occurs.  But we
;; take the easier approach of just not allowing you to request any name that
;; matches a current prefix.</p>

;; @(def vl-unlike-any-prefix-p)"

;;   (defund vl-unlike-any-prefix-p (name prefixes)
;;     ;; Ensure that NAME does not look like a PGENSTR for any of these prefixes.
;;     (declare (xargs :guard (and (stringp name)
;;                                 (string-listp prefixes))))
;;     (or (atom prefixes)
;;         (and (not (vl-pgenstr-p (car prefixes) name))
;;              (vl-unlike-any-prefix-p name (cdr prefixes)))))

;;   (local (in-theory (enable vl-unlike-any-prefix-p)))

;;   (defthm vl-unlike-any-prefix-p-when-atom
;;     (implies (atom prefixes)
;;              (vl-unlike-any-prefix-p name prefixes)))

;;   (defthm vl-unlike-any-prefix-p-of-cons
;;     (equal (vl-unlike-any-prefix-p name (cons a x))
;;            (and (not (vl-pgenstr-p a name))
;;                 (vl-unlike-any-prefix-p name x))))

;;   (defthm vl-pgenstr-p-when-vl-unlike-any-prefix-p
;;     (implies (and (member-equal key prefixes)
;;                   (vl-unlike-any-prefix-p name prefixes))
;;              (not (vl-pgenstr-p key name))))

;;   (encapsulate
;;    ()
;;    (local (defthm lemma
;;             (implies (and (subsetp-equal x y)
;;                           (vl-unlike-any-prefix-p name y))
;;                      (vl-unlike-any-prefix-p name x))
;;             :hints(("Goal" :induct (len x)))))

;;    (defcong subsetp-equiv equal (vl-unlike-any-prefix-p name prefixes) 2
;;      :hints(("Goal"
;;              :in-theory (e/d (subsetp-equiv)
;;                              (vl-unlike-any-prefix-p))
;;              :cases ((vl-unlike-any-prefix-p name prefixes))))))

;;   (encapsulate
;;    ()
;;    (local (defthm lemma1
;;             (implies (not (vl-pgenstr-p key name))
;;                      (equal (vl-pgenstr-highest key (cons name modns))
;;                             (vl-pgenstr-highest key modns)))
;;             :hints(("Goal" :in-theory (enable vl-pgenstr-highest)))))

;;    (local (defthm lemma2
;;             (implies (and (hons-assoc-equal key pset)
;;                           (vl-unlike-any-prefix-p name (strip-cars pset)))
;;                      (equal (vl-pgenstr-highest key (cons name modns))
;;                             (vl-pgenstr-highest key modns)))))

;;    (local (defthm lemma3
;;             ;; This might not be a terrible rule to have in general.
;;             (implies (cdr (hons-assoc-equal a x))
;;                      (hons-assoc-equal a x))
;;             :rule-classes :forward-chaining))

;;    (defthm vl-prefix-map-correct-p-aux-when-vl-unlike-any-prefix-p
;;      (implies (and (vl-prefix-map-correct-p-aux domain pmap names)
;;                    (vl-unlike-any-prefix-p name (strip-cars pmap)))
;;               (vl-prefix-map-correct-p-aux domain pmap (cons name names)))
;;      :hints(("Goal" :in-theory (enable vl-prefix-map-correct-p-aux)))))

;;   (defthm vl-prefix-map-correct-p-when-vl-unlike-any-prefix-p
;;     (implies (and (vl-prefix-map-correct-p pset modns)
;;                   (vl-unlike-any-prefix-p name (strip-cars pset)))
;;              (vl-prefix-map-correct-p pset (cons name modns)))
;;     :hints(("Goal" :in-theory (enable vl-prefix-map-correct-p)))))



;; (defun vl-unlike-any-prefix-p-of-strip-cars (name pmap)
;;   (declare (xargs :guard (and (stringp name)
;;                               (alistp pmap)
;;                               (vl-string-keys-p pmap))
;;                   :verify-guards nil))
;;   (mbe :logic
;;        (vl-unlike-any-prefix-p name (strip-cars pmap))
;;        :exec
;;        (or (atom pmap)
;;            (and (not (vl-pgenstr-p (caar pmap) name))
;;                 (vl-unlike-any-prefix-p-of-strip-cars name (cdr pmap))))))

;; (verify-guards vl-unlike-any-prefix-p-of-strip-cars
;;                ;; Again, can't give this directly as a :guard-hints...  stupid,
;;                ;; stupid.
;;                :hints(("Goal" :in-theory (enable vl-unlike-any-prefix-p))))



(defsection vl-namefactory-plain-name
  :parents (vl-namefactory-p)
  :short "@(call vl-namefactory-plain-name) returns <tt>(mv fresh-name
factory-prime)</tt>.  When possible, <tt>fresh-name</tt> is just <tt>name</tt>.
When this is not possible, a note is printed and <tt>fresh-name</tt> looks like
<tt>name_n</tt> instead."

  (defund vl-namefactory-plain-name (name factory)
    "Returns (MV FRESH-NAME FACTORY-PRIME)"
    (declare (xargs :guard (and (stringp name)
                                (vl-namefactory-p factory))
                    :verify-guards nil))
    (b* ((factory (vl-namefactory-maybe-initialize factory))
         ((mv newname db-prime)
          (vl-namedb-plain-name name (vl-namefactory->namedb factory)))

         (factory (change-vl-namefactory factory :namedb db-prime)))
        (mv newname factory)))

  (local (in-theory (enable vl-namefactory-plain-name)))

  (verify-guards vl-namefactory-plain-name)

  (defthm stringp-of-vl-namefactory-plain-name
    (implies (force (stringp name))
             (stringp (mv-nth 0 (vl-namefactory-plain-name name factory))))
    :rule-classes :type-prescription)

  (defthm vl-namefactory-p-of-vl-namefactory-plain-name
    (implies (and (force (vl-namefactory-p factory))
                  (force (stringp name)))
             (vl-namefactory-p (mv-nth 1 (vl-namefactory-plain-name name factory)))))

  (defthm vl-namefactory-allnames-of-vl-namefactory-plain-name
    (implies (force (vl-namefactory-p factory))
             (equal (vl-namefactory-allnames
                     (mv-nth 1 (vl-namefactory-plain-name name factory)))
                    (cons
                     (mv-nth 0 (vl-namefactory-plain-name name factory))
                     (vl-namefactory-allnames factory))))
    :hints(("Goal" :in-theory (enable vl-namefactory-allnames
                                      vl-namefactory-maybe-initialize))))

   (defthm vl-namefactory-plain-name-is-fresh
     (implies (and (force (stringp name))
                   (force (vl-namefactory-p factory)))
              (not (member-equal
                    (mv-nth 0 (vl-namefactory-plain-name name factory))
                    (vl-namefactory-allnames factory))))
     :hints(("Goal" :in-theory (enable vl-namefactory-allnames)))))



(defsection vl-free-namefactory
  :parents (vl-namefactory-p)
  :short "@(call vl-free-namefactory) frees the fast alists associated with a
name factory and returns <tt>nil</tt>."
  :long "<p>The name factory should never be used after this function is
called, since doing so will result in fast-alist discipline failures.</p>

<p>Note that we leave this function enabled.</p>"

  (defun vl-free-namefactory (factory)
    (declare (xargs :guard (vl-namefactory-p factory)))
    (progn$ (vl-free-namedb (vl-namefactory->namedb factory))
            nil)))



(defsection vl-namefactory-plain-names
  :parents (vl-namefactory-p)
  :short "@(call vl-namefactory-plain-names) returns <tt>(mv fresh-names
factory-prime)</tt>.  When possible, <tt>fresh-names</tt> are just
<tt>names</tt>.  If this is not possible due to name collisions, then some of
the <tt>fresh_names</tt> may have additional indexes as in @(see
vl-namefactory-indexed-name) and some notes may be printed."

  (defund vl-namefactory-plain-names (names factory)
    "Returns (MV NAMES' FACTORY')"
    (declare (xargs :guard (and (string-listp names)
                                (vl-namefactory-p factory))
                    :guard-hints (("goal" :in-theory
                                   (e/d () ((force)))))))
    (b* (((when (atom names))
          (mv nil factory))
         ((mv name factory)
          (vl-namefactory-plain-name (car names) factory))
         ((mv rest factory)
          (vl-namefactory-plain-names (cdr names) factory)))
      (mv (cons name rest) factory)))

  (local (in-theory (enable vl-namefactory-plain-names)))

  (defthm string-listp-of-vl-namefactory-plain-names
    (implies (force (string-listp names))
             (string-listp (mv-nth 0 (vl-namefactory-plain-names names factory)))))

  (defthm vl-namefactory-p-of-vl-namefactory-plain-names
    (implies (and (force (string-listp names))
                  (force (vl-namefactory-p factory)))
             (vl-namefactory-p (mv-nth 1 (vl-namefactory-plain-names names factory)))))

  (defthm vl-namefactory-plain-names-are-fresh
    (implies (and (member-equal a (vl-namefactory-allnames factory))
                  (force (string-listp names))
                  (force (vl-namefactory-p factory)))
             (not (member-equal a (mv-nth 0 (vl-namefactory-plain-names names
                                                                        factory))))))

  (defthm len-vl-namefactory-plain-names
    (equal (len (mv-nth 0 (vl-namefactory-plain-names names factory)))
           (len names)))

  (defthm true-listp-vl-namefactory-plain-names
    (true-listp (mv-nth 0 (vl-namefactory-plain-names names factory)))
    :hints(("Goal" :in-theory (disable (force))))
    :rule-classes :type-prescription))


