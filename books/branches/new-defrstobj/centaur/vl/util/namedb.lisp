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
(include-book "str/top" :dir :system)
(include-book "string-alists")
(include-book "nat-alists")
(local (include-book "arithmetic"))



(define vl-pgenstr ((prefix stringp)
                    (n natp))
  :parents (vl-namedb-p)
  :short "@(call vl-pgenstr) creates the string \"@('prefix')_@('n')\"."
  :long "<p>We @(see hons-copy) the result because generated names are
frequently used in fast alists.  See also @(see vl-pgenstr-p) and @(see
vl-pgenstr->val).</p>"
  (hons-copy (cat prefix "_" (natstr n))))


(define vl-pgenstr-p ((prefix stringp)
                      (str stringp))
  :parents (vl-namedb-p)
  :short "@(call vl-pgenstr-p) recognizes strings of the form
\"@('prefix')_n\"."

  (b* ((plen (length prefix))
       (slen (length str)))
    (and (< (+ 1 plen) slen)
         (str::strprefixp prefix str)
         (eql (char str plen) #\_)
         (str::digit-string-p-aux str (+ 1 plen) slen)))

  ///

  (local (in-theory (enable vl-pgenstr string-append)))

  (defthm vl-pgenstr-p-of-vl-pgenstr
    (implies (and (force (stringp prefix))
                  (force (natp n)))
             (vl-pgenstr-p prefix (vl-pgenstr prefix n))))

  (local (defthm nth-underscore-when-digit-listp
           (implies (str::digit-listp chars)
                    (not (equal (nth n chars) #\_)))))

  (local (in-theory (disable nthcdr-of-increment)))

  (defthm vl-pgenstr-p-of-vl-pgenstr-other
    (implies (and (not (equal other prefix))
                  (force (stringp prefix))
                  (force (stringp other)))
             (not (vl-pgenstr-p other (vl-pgenstr prefix n))))
    :hints(("Goal" :in-theory (enable list-equiv)))))



(define vl-pgenstr->val ((prefix stringp)
                         (str stringp))
  :parents (vl-namedb-p)
  :short "@(call vl-pgenstr->val) retrieves @('n') from the string @('str'),
which must have the form \"@('prefix')_@('n')\"; we return @('n') as a natural
number."

  :guard (vl-pgenstr-p prefix str)

  (b* (((mv val ?len)
        (str::parse-nat-from-string str 0 0
                                    (+ 1 (length prefix))
                                    (length str))))
    (lnfix val))

  :guard-hints (("Goal" :in-theory (enable vl-pgenstr-p)))

  ///

  (local (in-theory (enable vl-pgenstr string-append)))

  (defthm vl-pgenstr->val-of-vl-pgenstr
    (implies (and (force (stringp prefix))
                  (force (natp n)))
             (equal (vl-pgenstr->val prefix (vl-pgenstr prefix n))
                    n))))



(define vl-pgenstr-highest ((prefix stringp)
                            (names string-listp))
  :parents (vl-namedb-p)
  :short "@(call vl-pgenstr-highest) returns the largest @('n') such that
\"@('prefix')_n\" occurs in @('names')."

  (cond ((atom names)
         0)
        ((vl-pgenstr-p prefix (car names))
         (max (vl-pgenstr->val prefix (car names))
              (vl-pgenstr-highest prefix (cdr names))))
        (t
         (vl-pgenstr-highest prefix (cdr names))))

  ///

  (defthm none-greater-than-vl-pgenstr-highest
    (implies (and (< (vl-pgenstr-highest prefix names) n)
                  (force (stringp prefix))
                  (force (natp n)))
             (equal (member-equal (vl-pgenstr prefix n) names)
                    nil)))

  (defthm vl-pgenstr-highest-of-incremental-extension
    (implies (force (stringp prefix))
             (EQUAL (VL-PGENSTR-HIGHEST
                     PREFIX
                     (CONS (VL-PGENSTR PREFIX (+ 1 (VL-PGENSTR-HIGHEST PREFIX MODNS)))
                           MODNS))
                    (+ 1 (VL-PGENSTR-HIGHEST PREFIX MODNS)))))

  (defthm vl-pgenstr-highest-of-irrelevant-extension
    (implies (and (not (equal other prefix))
                  (force (stringp prefix))
                  (force (stringp other)))
             (equal (vl-pgenstr-highest other (CONS (VL-PGENSTR PREFIX k) MODNS))
                    (vl-pgenstr-highest other modns)))
    :hints(("Goal" :in-theory (disable (force))))))


(define vl-pgenstr-highest-of-strip-cars ((prefix stringp)
                                          (modns (and (alistp modns)
                                                      (vl-string-keys-p modns))))
  :parents (vl-namedb-p)
  :short "Fusion of vl-pgenstr-highest and strip-cars, for efficiency."
  :enabled t
  :verify-guards nil

  (mbe :logic
       (vl-pgenstr-highest prefix (strip-cars modns))
       :exec
       (cond ((atom modns)
              0)
             ((vl-pgenstr-p prefix (caar modns))
              (max (vl-pgenstr->val prefix (caar modns))
                   (vl-pgenstr-highest-of-strip-cars prefix (cdr modns))))
             (t
              (vl-pgenstr-highest-of-strip-cars prefix (cdr modns)))))

  ///
  (local (in-theory (enable vl-pgenstr-highest)))
  (verify-guards vl-pgenstr-highest-of-strip-cars))


(defsection vl-prefix-map-correct-p

  (defund vl-prefix-map-correct-p-aux (domain pmap names)
    ;; Ensure PMAP[KEY] = (VL-PGENSTR-HIGHEST KEY NAMES) forall KEY in DOMAIN.
    (declare (xargs :guard (and (string-listp domain)
                                (alistp pmap)
                                (vl-string-keys-p pmap)
                                (vl-nat-values-p pmap)
                                (string-listp names))))
    (if (atom domain)
        t
      (let ((lookup (hons-get (car domain) pmap)))
        (and (equal (cdr lookup) (vl-pgenstr-highest (car domain) names))
             (vl-prefix-map-correct-p-aux (cdr domain) pmap names)))))

  (defund vl-prefix-map-correct-p (pmap names)
    ;; Ensure PMAP[KEY] = (VL-PGENSTR-HIGHEST KEY NAMES) forall KEY bound in PMAP.
    (declare (xargs :guard (and (alistp pmap)
                                (vl-string-keys-p pmap)
                                (vl-nat-values-p pmap)
                                (string-listp names))))
    (vl-prefix-map-correct-p-aux (strip-cars pmap) pmap names))

  (defthm vl-prefix-map-correct-p-aux-of-atom
    (implies (atom domain)
             (vl-prefix-map-correct-p-aux domain pmap names))
    :hints(("Goal" :in-theory (enable vl-prefix-map-correct-p-aux))))

  (defthm vl-prefix-map-correct-p-aux-of-cons
    (equal (vl-prefix-map-correct-p-aux (cons key domain) pmap names)
           (and (equal (cdr (hons-get key pmap)) (vl-pgenstr-highest key names))
                (vl-prefix-map-correct-p-aux domain pmap names)))
    :hints(("Goal" :in-theory (enable vl-prefix-map-correct-p-aux))))

  (defthm vl-prefix-map-correct-p-when-atom
    (implies (atom pmap)
             (vl-prefix-map-correct-p pmap names))
    :hints(("Goal" :in-theory (enable vl-prefix-map-correct-p))))


  (local (defthm lemma
           (implies (and (vl-prefix-map-correct-p-aux domain pmap names)
                         (member-equal key domain))
                    (hons-assoc-equal key pmap))
           :hints(("Goal" :in-theory (enable vl-prefix-map-correct-p-aux)))))

  (local (defthm lemma2
           (equal (equal x (cons a b))
                  (and (consp x)
                       (equal (car x) a)
                       (equal (cdr x) b)))))

  (local (defthm lemma3
           (implies (not (member-equal key (strip-cars alist)))
                    (not (hons-assoc-equal key alist)))
           :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

  (defthm hons-assoc-equal-when-vl-prefix-map-correct-p-aux
    (implies (and (vl-prefix-map-correct-p-aux domain pmap names)
                  (member-equal key domain))
             (equal (hons-assoc-equal key pmap)
                    (cons key (vl-pgenstr-highest key names))))
    :hints(("Goal" :in-theory (enable vl-prefix-map-correct-p-aux))))

  (defthm hons-assoc-equal-when-vl-prefix-map-correct-p
    (implies (and (vl-prefix-map-correct-p pmap names)
                  (hons-assoc-equal prefix pmap))
             (equal (hons-assoc-equal prefix pmap)
                    (cons prefix (vl-pgenstr-highest prefix names))))
    :hints(("Goal"
            :in-theory (e/d (vl-prefix-map-correct-p)
                            (hons-assoc-equal-when-vl-prefix-map-correct-p-aux))
            :use ((:instance hons-assoc-equal-when-vl-prefix-map-correct-p-aux
                             (domain (strip-cars pmap))
                             (pmap pmap)
                             (names names)
                             (key prefix))))))

  (defthm vl-prefix-map-correct-p-aux-when-subset
    (implies (and (subsetp-equal x y)
                  (vl-prefix-map-correct-p-aux y pmap names))
             (vl-prefix-map-correct-p-aux x pmap names))
    :hints(("Goal" :induct (len x))))

  (defcong set-equiv equal (vl-prefix-map-correct-p-aux x pmap names) 1
    :hints(("goal"
            :in-theory (enable set-equiv)
            :cases ((vl-prefix-map-correct-p-aux x pmap names)))))

  (defthm vl-prefix-map-correct-p-aux-of-hons-shrink-alist
    (implies (vl-prefix-map-correct-p-aux domain pmap names)
             (vl-prefix-map-correct-p-aux domain (hons-shrink-alist pmap nil) names))
    :hints(("Goal" :in-theory (enable vl-prefix-map-correct-p-aux))))

  (defthm vl-prefix-map-correct-p-of-hons-shrink-alist
    (implies (vl-prefix-map-correct-p pmap names)
             (vl-prefix-map-correct-p (hons-shrink-alist pmap nil) names))
    :hints(("Goal"
            :in-theory (e/d (vl-prefix-map-correct-p)
                            (vl-prefix-map-correct-p-aux-of-hons-shrink-alist
                             vl-prefix-map-correct-p-aux-when-subset))
            :use ((:instance vl-prefix-map-correct-p-aux-of-hons-shrink-alist
                             (domain (strip-cars pmap)))
                  (:instance vl-prefix-map-correct-p-aux-when-subset
                             (x (STRIP-CARS (HONS-SHRINK-ALIST PMAP NIL)))
                             (y (STRIP-CARS PMAP))
                             (pmap (HONS-SHRINK-ALIST PMAP NIL))))))))



(defun vl-namedb-okp (names pmap pset)
  ;; Note: we leave this enabled!
  (declare (xargs :guard (and (alistp names)
                              (vl-string-keys-p names)

                              (alistp pmap)
                              (vl-string-keys-p pmap)
                              (vl-nat-values-p pmap)

                              (alistp pset)
                              (vl-string-keys-p pset))))
  (and (or names (not pmap))
       (set-equiv (strip-cars pset) (strip-cars pmap))))

(defaggregate vl-namedb
  (names pmap pset)
  :tag :vl-namedb
  :legiblep nil
  :require ((alistp-of-vl-namedb->names           (alistp names))
            (vl-string-keys-p-of-vl-namedb->names (vl-string-keys-p names))

            (alistp-of-vl-namedb->pmap            (alistp pmap))
            (vl-string-keys-p-of-vl-namedb->pmap  (vl-string-keys-p pmap))
            (vl-nat-values-p-of-vl-namedb->pmap   (vl-nat-values-p pmap))

            (alistp-of-vl-namedb-pset             (alistp pset))
            (vl-string-keys-p-of-vl-namedb->pset  (vl-string-keys-p pset))

            (vl-prefix-map-correct-p-when-vl-namedb-p
             (vl-prefix-map-correct-p pmap (strip-cars names)))

            (vl-namedb-okp-when-vl-namedb-p
             (vl-namedb-okp names pmap pset))
            )
  :parents (utilities)

  :short "Produces fresh names for a module."

  :long "<p>A <b>name db</b> allows you to easily and efficiently generate
good, fresh names that are not being used elsewhere.</p>

<p>Name DBs are a general-purpose construct that isn't Verilog specific.  When
we want to generate fresh wire names for Verilog modules, we usually use a
@(see vl-namefactory-p) instead.  A name factory is specific to Verilog
modules, and often allows us to avoid constructing the list of all wire names
for a module.</p>


<h3>Using Name DBs</h3>

<p>Typically, the user begins by constructing a name db using
@('(vl-starting-namedb names)'), where @('names') are just a list of the
strings that are \"in use.\"</p>

<p>Once constructed, name DBs must be used in a single-threaded discipline.
That is, the functions for generating names actually return @('(mv fresh-name
db-prime)'), and to ensure that a sequence of generated names are unique, one
must always use the most recently returned db to generate subsequent names.</p>

<p>Two functions are provided for generating names:</p>

<p>@('(vl-namedb-indexed-name prefix nf)') produces a name that looks like
@('prefix_n'), where @('n') is the smallest positive natural number @('n') such
that the name @('prefix_n') is not in use.</p>

<p>@('(vl-namedb-plain-name name nf)') attempts to return @('name') verbatim.
When this is not possible, a name of the form @('name_n'), a note will be
printed to standard output and instead we will produce a name with
@('vl-namedb-indexed-name').</p>

<p>We use these functions for different purposes.  We think that @(see
vl-namedb-indexed-name) should be used for \"throwaway\" names that don't need
to be reliable or understandable, such as the names of temporary wires to be
generated for split-up expressions.  Meanwhile, @(see vl-namedb-plain-name)
should be used for splitting up instance names or in any other cases where a
reliable name is desired.</p>

<p>Because name DBs make use of fast alists, they should be destroyed with
@('(vl-free-namedb nf)') when you are done using them.</p>


<h3>Freshness Guarantee</h3>

<p>To establish that name DBs generate only fresh names, we introduce the
function @('(vl-namedb-allnames nf)').  This function returns a list of
all names that the name db currently considers to be in use.  We prove:</p>

<ul>

<li>Every name in @('names') is among the @('allnames') of the initial name db
produced by @('(vl-starting-namedb names).')</li>

<li>The @('fresh-name')s returned by @(see vl-namedb-indexed-name) or @(see
vl-namedb-plain-name) are not members of the @('allnames') of the input
db.</li>

<li>The @('allnames') of the resulting @('db-prime') include exactly the
@('allnames') of the input @('db'), along with the generated
@('fresh-name').</li>

</ul>

<p>Together, these theorems ensure that, when properly used, the name db will
only give you fresh names.</p>


<h3>Implementation</h3>

<p>A name db has three fields:</p>

<ul> <li>@('names'), a fast alist that associates strings to @('t').</li>
<li>@('pmap'), a fast alist that associates strings to natural numbers.</li>
<li>@('plist'), a fast alist that associates strings to @('t').</li> </ul>

<p><u>Invariant B1</u>.  The @('pmap') is empty whenever @('names') is
empty.</p>

<p><u>Invariant B2</u>.  Each @('prefix') bound in @('pmap') is bound to
@('(vl-pgenstr-highest prefix (strip-cars names))').</p>

<p><u>Invariant C1</u>.  The @('plist') binds exactly those @('prefix')es that
are bound in @('pmap').</p>

<p>Intuitively, the @('names') represents the set of all names that are
currently in use.  We use a fast-alist representation so that we can very
quickly determine whether a plain name is available.</p>

<p>Meanwhile, the @('pmap') allows us to use something much like the \"historic
scheme\" to quickly generate indexed names.  In particular, it binds some
prefixes with their highest used index.  This way, we only need to scan the
@('names') once per prefix.</p>

<p>The @('plist') is really just an optimization that allows us to avoid
needing to shrink the plists.  See the discussion in @(see
vl-compatible-with-prefix-set-p) for details.</p>")

(defthm vl-namedb->pmap-when-no-names
  (implies (and (not (vl-namedb->names x))
                (force (vl-namedb-p x)))
           (not (vl-namedb->pmap x)))
  :hints(("Goal"
          :in-theory (disable vl-namedb-okp-when-vl-namedb-p)
          :use ((:instance vl-namedb-okp-when-vl-namedb-p)))))

(defthm vl-namedb->pset-under-set-equiv
  (implies (force (vl-namedb-p x))
           (set-equiv (strip-cars (vl-namedb->pset x))
                          (strip-cars (vl-namedb->pmap x))))
  :hints(("Goal"
          :in-theory (disable vl-namedb-okp-when-vl-namedb-p)
          :use ((:instance vl-namedb-okp-when-vl-namedb-p)))))

(defthm hons-assoc-equal-of-vl-namedb->pmap
  ;; This is better than HONS-ASSOC-EQUAL-WHEN-VL-PREFIX-MAP-CORRECT-P, because
  ;; we avoid the free variable NAMES by explicitly saying to consider the cars
  ;; of NAMES.
  (implies (and (vl-namedb-p db)
                (hons-assoc-equal prefix (vl-namedb->pmap db)))
           (equal (hons-assoc-equal prefix (vl-namedb->pmap db))
                  (let ((names (strip-cars (vl-namedb->names db))))
                    (cons prefix (vl-pgenstr-highest prefix names)))))
  :hints(("goal"
          :in-theory (disable hons-assoc-equal-when-vl-prefix-map-correct-p)
          :use ((:instance hons-assoc-equal-when-vl-prefix-map-correct-p
                           (pmap (vl-namedb->pmap db))
                           (names (strip-cars (vl-namedb->names db))))))))




(defsection vl-namedb-allnames
  :parents (vl-namedb-p)

  :short "@(call vl-namedb-p) returns a list of all names that are
considered to be used by the name db."

  :long "<p>This function is not particularly efficient, and probably should
not ordinarily be executed in real programs.  Its main purpose is to establish
the freshness guarantee for name DBs, described in @(see vl-namedb-p).</p>"

  (defund vl-namedb-allnames (db)
    (declare (xargs :guard (vl-namedb-p db)
                    :verify-guards nil))
    (strip-cars (vl-namedb->names db)))

  (local (in-theory (enable vl-namedb-allnames)))

  (verify-guards vl-namedb-allnames))




(defsection vl-empty-namedb
  :parents (vl-namedb-p)
  :short "@(call vl-empty-namedb) creates an empty name db."

  (defund vl-empty-namedb ()
    (declare (xargs :guard t))
    (make-vl-namedb :names nil :pmap nil :pset nil))

  (in-theory (disable (:executable-counterpart vl-empty-namedb)))

  (local (in-theory (enable vl-empty-namedb)))

  (defthm vl-namedb-p-of-vl-empty-namedb
    (vl-namedb-p (vl-empty-namedb)))

  (defthm vl-namedb-allnames-of-vl-empty-namedb
    (equal (vl-namedb-allnames (vl-empty-namedb))
           nil)))



(defsection vl-starting-namedb
  :parents (vl-namedb-p)
  :short "@(call vl-starting-namedb) creates a name database that regards
@('names') as already in use."

  (defund vl-starting-namedb (names)
    (declare (xargs :guard (string-listp names)))
    (make-vl-namedb :names (make-lookup-alist names)
                    :pmap nil
                    :pset nil))

  (in-theory (disable (:executable-counterpart vl-starting-namedb)))

  (local (in-theory (enable vl-starting-namedb)))

  (defthm vl-namedb-p-of-vl-starting-namedb
    (implies (force (string-listp names))
             (vl-namedb-p (vl-starting-namedb names))))

  (defthm vl-namedb-allnames-of-vl-starting-namedb
    (equal (vl-namedb-allnames (vl-starting-namedb names))
           (list-fix names))
    :hints(("Goal" :in-theory (enable vl-namedb-allnames)))))



(defsection vl-namedb-indexed-name
  :parents (vl-namedb-p)
  :short "@(call vl-namedb-indexed-name) constructs a fresh name that looks
like @('prefix_n') for some natural number @('n'), and returns @('(mv
fresh-name db-prime)')."

  (defund vl-namedb-indexed-name (prefix db)
    "Returns (MV FRESH-NAME DB-PRIME)"
    (declare (xargs :guard (and (stringp prefix)
                                (vl-namedb-p db))
                    :verify-guards nil))
    (b* (

         ;; Now, look up the highest index associated with the desired name.  If
         ;; there's an entry in the pmap, we can use it.  Otherwise, we have to
         ;; scan the namespace.
         (names   (vl-namedb->names db))
         (pmap    (vl-namedb->pmap db))
         (pset    (vl-namedb->pset db))

         (lookup  (hons-get prefix pmap))
         (maxidx  (if lookup
                      (cdr lookup)
                    (vl-pgenstr-highest-of-strip-cars prefix names)))
         (newidx  (+ maxidx 1))
         (newname (vl-pgenstr prefix newidx))

         (names   (hons-acons newname t names))
         (pmap    (hons-acons prefix newidx pmap))
         (pset    (if lookup
                      pset
                    (hons-acons prefix t pset)))

         (db (change-vl-namedb db :names names :pmap pmap :pset pset)))
        (mv newname db)))

  (local (in-theory (enable vl-namedb-indexed-name)))

  (local (defthm lemma
           (implies (and (vl-prefix-map-correct-p-aux domain pmap names)
                         (string-listp domain)
                         (stringp prefix))
                    (vl-prefix-map-correct-p-aux
                     domain
                     (cons (cons prefix (+ 1 (vl-pgenstr-highest prefix names))) pmap)
                     (cons (vl-pgenstr prefix (+ 1 (vl-pgenstr-highest prefix names))) names)))
           :hints(("Goal"
                   :in-theory (enable vl-prefix-map-correct-p-aux)
                   :do-not '(generalize fertilize)))))

  (local (defthm lemma2
           (implies (hons-assoc-equal prefix pmap)
                    (member-equal prefix (strip-cars pmap)))
           :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

  (local (defthm lemma3
           (implies (and (vl-prefix-map-correct-p pmap names)
                         (vl-string-keys-p pmap)
                         (stringp prefix))
                    (vl-prefix-map-correct-p
                     (cons (cons prefix (+ 1 (vl-pgenstr-highest prefix names))) pmap)
                     (cons (vl-pgenstr prefix (+ 1 (vl-pgenstr-highest prefix names))) names)))
           :hints(("goal" :in-theory (enable vl-prefix-map-correct-p)))))

  (verify-guards vl-namedb-indexed-name)

  (defthm stringp-of-vl-namedb-indexed-name
    (stringp (mv-nth 0 (vl-namedb-indexed-name prefix db)))
    :rule-classes :type-prescription)

  (defthm vl-namedb-p-of-vl-namedb-indexed-name
    (implies (and (force (vl-namedb-p db))
                  (force (stringp prefix)))
             (vl-namedb-p (mv-nth 1 (vl-namedb-indexed-name prefix db)))))

  (defthm vl-namedb-allnames-of-vl-namedb-indexed-name
    (implies (force (vl-namedb-p db))
             (equal (vl-namedb-allnames
                     (mv-nth 1 (vl-namedb-indexed-name prefix db)))
                    (cons
                     (mv-nth 0 (vl-namedb-indexed-name prefix db))
                     (vl-namedb-allnames db))))
    :hints(("Goal" :in-theory (enable vl-namedb-allnames))))

  (defthm vl-namedb->names-of-vl-namedb-indexed-name
    (vl-namedb->names (mv-nth 1 (vl-namedb-indexed-name prefix db))))

  (defthm vl-namedb-indexed-name-is-fresh
    (implies (and (force (stringp prefix))
                  (force (vl-namedb-p db)))
             (not (member-equal
                   (mv-nth 0 (vl-namedb-indexed-name prefix db))
                   (vl-namedb-allnames db))))
    :hints(("Goal" :in-theory (enable vl-namedb-allnames)))))



(defsection vl-unlike-any-prefix-p
  :parents (vl-namedb-p)
  :short "@(call vl-unlike-any-prefix-p) determines whether for all @('p') in
@('prefixes'), @('(vl-pgenstr-p p name)') is false."

  :long "<p>We use this function in the implementation of @(see
vl-namedb-plain-name).  When requesting a plain name, one might ask for a name
like @('foo_3'), which could screw up the prefix map if we are using @('foo')
as a prefix.</p>

<p>One solution would be to fix up the prefix map when this occurs.  But we
take the easier approach of just not allowing you to request any name that
matches a current prefix.</p>"

  (defund vl-unlike-any-prefix-p (name prefixes)
    ;; Ensure that NAME does not look like a PGENSTR for any of these prefixes.
    (declare (xargs :guard (and (stringp name)
                                (string-listp prefixes))))
    (or (atom prefixes)
        (and (not (vl-pgenstr-p (car prefixes) name))
             (vl-unlike-any-prefix-p name (cdr prefixes)))))

  (local (in-theory (enable vl-unlike-any-prefix-p)))

  (defthm vl-unlike-any-prefix-p-when-atom
    (implies (atom prefixes)
             (vl-unlike-any-prefix-p name prefixes)))

  (defthm vl-unlike-any-prefix-p-of-cons
    (equal (vl-unlike-any-prefix-p name (cons a x))
           (and (not (vl-pgenstr-p a name))
                (vl-unlike-any-prefix-p name x))))

  (defthm vl-pgenstr-p-when-vl-unlike-any-prefix-p
    (implies (and (member-equal key prefixes)
                  (vl-unlike-any-prefix-p name prefixes))
             (not (vl-pgenstr-p key name))))

  (encapsulate
   ()
   (local (defthm lemma
            (implies (and (subsetp-equal x y)
                          (vl-unlike-any-prefix-p name y))
                     (vl-unlike-any-prefix-p name x))
            :hints(("Goal" :induct (len x)))))

   (defcong set-equiv equal (vl-unlike-any-prefix-p name prefixes) 2
     :hints(("Goal"
             :in-theory (e/d (set-equiv)
                             (vl-unlike-any-prefix-p))
             :cases ((vl-unlike-any-prefix-p name prefixes))))))

  (encapsulate
   ()
   (local (defthm lemma1
            (implies (not (vl-pgenstr-p key name))
                     (equal (vl-pgenstr-highest key (cons name names))
                            (vl-pgenstr-highest key names)))
            :hints(("Goal" :in-theory (enable vl-pgenstr-highest)))))

   (local (defthm lemma2
            (implies (and (hons-assoc-equal key pset)
                          (vl-unlike-any-prefix-p name (strip-cars pset)))
                     (equal (vl-pgenstr-highest key (cons name names))
                            (vl-pgenstr-highest key names)))
            :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

   (local (defthm lemma3
            ;; This might not be a terrible rule to have in general.
            (implies (cdr (hons-assoc-equal a x))
                     (hons-assoc-equal a x))
            :rule-classes :forward-chaining))

   (defthm vl-prefix-map-correct-p-aux-when-vl-unlike-any-prefix-p
     (implies (and (vl-prefix-map-correct-p-aux domain pmap names)
                   (vl-unlike-any-prefix-p name (strip-cars pmap)))
              (vl-prefix-map-correct-p-aux domain pmap (cons name names)))
     :hints(("Goal" :in-theory (enable vl-prefix-map-correct-p-aux)))))

  (defthm vl-prefix-map-correct-p-when-vl-unlike-any-prefix-p
    (implies (and (vl-prefix-map-correct-p pset names)
                  (vl-unlike-any-prefix-p name (strip-cars pset)))
             (vl-prefix-map-correct-p pset (cons name names)))
    :hints(("Goal" :in-theory (enable vl-prefix-map-correct-p)))))



(defun vl-unlike-any-prefix-p-of-strip-cars (name pmap)
  (declare (xargs :guard (and (stringp name)
                              (alistp pmap)
                              (vl-string-keys-p pmap))
                  :verify-guards nil))
  (mbe :logic
       (vl-unlike-any-prefix-p name (strip-cars pmap))
       :exec
       (or (atom pmap)
           (and (not (vl-pgenstr-p (caar pmap) name))
                (vl-unlike-any-prefix-p-of-strip-cars name (cdr pmap))))))

(verify-guards vl-unlike-any-prefix-p-of-strip-cars
               ;; Again, can't give this directly as a :guard-hints...  stupid,
               ;; stupid.
               :hints(("Goal" :in-theory (enable vl-unlike-any-prefix-p))))



(defsection vl-namedb-plain-name
  :parents (vl-namedb-p)
  :short "@(call vl-namedb-plain-name) returns @('(mv fresh-name db-prime)').
When possible, @('fresh-name') is just @('name').  When this is not possible, a
note is printed and @('fresh-name') looks like @('name_n') instead."

  (defund vl-namedb-plain-name (name db)
    "Returns (MV FRESH-NAME DB-PRIME)"
    (declare (xargs :guard (and (stringp name)
                                (vl-namedb-p db))
                    :verify-guards nil))
    (b* ((name    (string-fix name))
         (names   (vl-namedb->names db))
         (pset    (vl-namedb->pset db))

         ((when (hons-get name names))
          (mv-let (fresh-name db)
                  (vl-namedb-indexed-name name db)
                  (prog2$
                   (cw "; Name db note: ~x0 is not available; made ~x1 instead.~%"
                       name fresh-name)
                   (mv fresh-name db))))

         ((unless (vl-unlike-any-prefix-p-of-strip-cars name pset))
          (mv-let (fresh-name db)
                  (vl-namedb-indexed-name name db)
                  (prog2$
                   (cw "; Name db note: ~x0 is like an existing prefix; made ~x1 instead.~%"
                       name fresh-name)
                   (mv fresh-name db))))

         (names   (hons-acons name t names))
         (db (change-vl-namedb db :names names)))
        (mv name db)))

  (local (in-theory (enable vl-namedb-plain-name)))

  (verify-guards vl-namedb-plain-name)

  (defthm stringp-of-vl-namedb-plain-name
    (stringp (mv-nth 0 (vl-namedb-plain-name name db)))
    :hints(("Goal" :in-theory (disable vl-namedb->pset-under-set-equiv)))
    :rule-classes :type-prescription)

  (defthm vl-namedb-p-of-vl-namedb-plain-name
    (implies (and (force (vl-namedb-p db))
                  (force (stringp name)))
             (vl-namedb-p (mv-nth 1 (vl-namedb-plain-name name db)))))

  (encapsulate
   ()
   (local (defthm lemma
            ;; Ugh, kind of ugly, but not too bad really.  This is just addressing
            ;; the particular case that doesn't default to indexed name generation
            (IMPLIES
             (AND
              (VL-NAMEDB-P DB)
              (NOT
               (HONS-ASSOC-EQUAL
                NAME
                (VL-NAMEDB->NAMES DB)))
              (VL-UNLIKE-ANY-PREFIX-P
               NAME
               (STRIP-CARS
                (VL-NAMEDB->PMAP DB))))
             (EQUAL
              (VL-NAMEDB-ALLNAMES
               (VL-NAMEDB
                (CONS (CONS NAME T)
                      (VL-NAMEDB->NAMES DB))
                (VL-NAMEDB->PMAP DB)
                (VL-NAMEDB->PSET DB)))
              (CONS NAME (VL-NAMEDB-ALLNAMES DB))))
            :hints(("Goal" :in-theory (enable vl-namedb-allnames)))))

   (defthm vl-namedb-allnames-of-vl-namedb-plain-name
     (implies (force (vl-namedb-p db))
              (equal (vl-namedb-allnames
                      (mv-nth 1 (vl-namedb-plain-name name db)))
                     (cons
                      (mv-nth 0 (vl-namedb-plain-name name db))
                      (vl-namedb-allnames db))))))


  (defthm vl-namedb->names-of-vl-namedb-plain-name
    (vl-namedb->names (mv-nth 1 (vl-namedb-plain-name name db)))
    :hints(("Goal" :in-theory (disable (force)))))


  (encapsulate
   ()
   (local (defthm crock
            (implies (alistp alist)
                     (iff (member-equal prefix (strip-cars alist))
                          (hons-assoc-equal prefix alist)))
            :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

   (local (defthm lemma
            (IMPLIES
             (AND
              (STRINGP NAME)
              (VL-NAMEDB-P DB)
              (NOT
               (HONS-ASSOC-EQUAL
                NAME
                (VL-NAMEDB->NAMES DB)))
              (VL-UNLIKE-ANY-PREFIX-P
               NAME
               (STRIP-CARS
                (VL-NAMEDB->PMAP DB))))
             (NOT (MEMBER-EQUAL NAME
                                (VL-NAMEDB-ALLNAMES DB))))
            :hints(("Goal" :in-theory (enable vl-namedb-allnames)))))

   (defthm vl-namedb-plain-name-is-fresh
     (implies (and (force (stringp name))
                   (force (vl-namedb-p db)))
              (not (member-equal
                    (mv-nth 0 (vl-namedb-plain-name name db))
                    (vl-namedb-allnames db))))
     :hints((and stable-under-simplificationp
                 '(:in-theory (disable vl-namedb-indexed-name-is-fresh)
                  :use ((:instance vl-namedb-indexed-name-is-fresh
                                   (prefix name)))))))))


(defun vl-namedb-plain-name-quiet (name db)
    "Returns (MV FRESH-NAME DB-PRIME)"
    (declare (xargs :guard (and (stringp name)
                                (vl-namedb-p db))
                    :guard-hints(("Goal" :in-theory (enable vl-namedb-plain-name)))))
    (mbe :logic (vl-namedb-plain-name name db)
         :exec
         (b* ((names   (vl-namedb->names db))
              (pset    (vl-namedb->pset db))

              ((when (hons-get name names))
               (mv-let (fresh db)
                 (vl-namedb-indexed-name name db)
                 (mv fresh db)))

              ((unless (vl-unlike-any-prefix-p-of-strip-cars name pset))
               (mv-let (fresh db)
                 (vl-namedb-indexed-name name db)
                 (mv fresh db)))

              (names   (hons-acons name t names))
              (db (change-vl-namedb db :names names)))
           (mv name db))))


(defsection vl-free-namedb
  :parents (vl-namedb-p)
  :short "@(call vl-free-namedb) frees the fast alists associated with a name
db and returns @('nil')."
  :long "<p>The name db should never be used after this function is called,
since doing so will result in fast-alist discipline failures.</p>

<p>Note that we leave this function enabled.</p>"

  (defun vl-free-namedb (db)
    (declare (xargs :guard (vl-namedb-p db)))
    (progn$ (fast-alist-free (vl-namedb->names db))
            (fast-alist-free (vl-namedb->pmap db))
            (fast-alist-free (vl-namedb->pset db))
            nil)))



(defsection vl-namedb-plain-names
  :parents (vl-namedb-p)
  :short "Generate a list of fresh names."

  :long "<p>@(call vl-namedb-plain-names) returns @('(mv fresh-names
db-prime)').</p>

<p>When possible, @('fresh-names') are just @('names').  When this is not
possible due to name collisions, some of the @('fresh_names') may have
additional indexes as in @(see vl-namedb-indexed-name), and notes may be
printed.</p>"

  (defund vl-namedb-plain-names (names db)
    "Returns (MV NAMES' DB')"
    (declare (xargs :guard (and (string-listp names)
                                (vl-namedb-p db))))
    (b* (((when (atom names))
          (mv nil db))
         ((mv name1 db)
          (vl-namedb-plain-name (car names) db))
         ((mv rest db)
          (vl-namedb-plain-names (cdr names) db)))
        (mv (cons name1 rest) db)))

  (local (in-theory (enable vl-namedb-plain-names)))

  (defthm string-listp-of-vl-namedb-plain-names
    (implies (force (string-listp names))
             (string-listp (mv-nth 0 (vl-namedb-plain-names names db)))))

  (defthm vl-namedb-p-of-vl-namedb-plain-names
    (implies (and (force (string-listp names))
                  (force (vl-namedb-p db)))
             (vl-namedb-p (mv-nth 1 (vl-namedb-plain-names names db)))))

  (defthm vl-namedb-plain-names-are-fresh
    (implies (and (member-equal a (vl-namedb-allnames db))
                  (force (string-listp names))
                  (force (vl-namedb-p db)))
             (not (member-equal a (mv-nth 0 (vl-namedb-plain-names names
                                                                   db))))))

  (defthm vl-namedb-allnames-of-vl-namedb-plain-names
    (implies (and (force (vl-namedb-p db))
                  (force (string-listp names)))
             (equal (vl-namedb-allnames
                     (mv-nth 1 (vl-namedb-plain-names names db)))
                    (revappend
                     (mv-nth 0 (vl-namedb-plain-names names db))
                     (vl-namedb-allnames db))))))





