; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "VL")
(include-book "defs")
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(local (include-book "arithmetic"))

(defxdoc name-database
  :parents (utilities)
  :short "A general utility for generating fresh names."

  :long "<p>A <b>name database</b> allows you to easily and efficiently
generate good, fresh names that are not being used elsewhere.</p>

<p>Name databases are a general-purpose mechanism that has nothing to do with
Verilog.  This was not always true; historically name databases were originally
part of a larger @('vl-namefactory') structure that had a deep understanding of
Verilog modules, but that mechanism no longer exists.</p>

<h3>Using Name Databases</h3>

<p>Typically, the user begins by constructing a name database using
@('(vl-starting-namedb names)'), where @('names') are just a list of the
names (strings) that are \"in use.\"</p>

<p>Once constructed, name databases must be used in a single-threaded
discipline.  That is, the functions for generating names actually return @('(mv
fresh-name db-prime)'), and to ensure that a sequence of generated names are
unique, one must always use the most recently returned database to generate
subsequent names.</p>

<p>Two functions are provided for generating names:</p>

<p>@('(vl-namedb-indexed-name prefix db)') produces a name that looks like
@('prefix_n'), where @('n') is the smallest positive natural number @('n') such
that the name @('prefix_n') is not in use.</p>

<p>@('(vl-namedb-plain-name name db)') attempts to return @('name') verbatim.
When this is not possible, a name of the form @('name_n'), a note will be
printed to standard output and instead we will produce a name with
@('vl-namedb-indexed-name').</p>

<p>We use these functions for different purposes.  We think that @(see
vl-namedb-indexed-name) should be used for \"throwaway\" names that don't need
to be reliable or understandable, such as the names of temporary wires to be
generated for split-up expressions.  Meanwhile, @(see vl-namedb-plain-name)
should be used for splitting up instance names or in any other cases where a
reliable name is desired.</p>

<p>Because name databases make use of fast alists, they should be destroyed
with @('(vl-free-namedb nf)') when you are done using them.</p>


<h3>Freshness Guarantee</h3>

<p>To establish that name databases generate only fresh names, we introduce the
function @('(vl-namedb-allnames db)').  This function returns a list of all
names that the name database currently considers to be in use.  We prove:</p>

<ul>

<li>Every name in @('names') is among the @('allnames') of the initial name
database produced by @('(vl-starting-namedb names).')</li>

<li>The @('fresh-name')s returned by @(see vl-namedb-indexed-name) or @(see
vl-namedb-plain-name) are not members of the @('allnames') of the input
database.</li>

<li>The @('allnames') of the resulting @('db-prime') include exactly the
@('allnames') of the input @('db'), along with the generated
@('fresh-name').</li>

</ul>

<p>Together, these theorems ensure that, when properly used, the name database
will only give you fresh names.</p>")

(local (xdoc::set-default-parents name-database))

(define vl-pgenstr ((prefix stringp)
                    (n natp))
  :short "@(call vl-pgenstr) creates the string \"@('prefix')_@('n')\"."
  :long "<p>We @(see hons-copy) the result because generated names are
frequently used in fast alists.  See also @(see vl-pgenstr-p) and @(see
vl-pgenstr->val).</p>"
  (hons-copy (cat prefix "_" (natstr n))))

(define vl-pgenstr-p ((prefix stringp)
                      (str stringp))
  :short "@(call vl-pgenstr-p) recognizes strings of the form
\"@('prefix')_n\"."

  (b* ((plen (length prefix))
       (slen (length str)))
    (and (< (+ 1 plen) slen)
         (str::strprefixp prefix str)
         (eql (char str plen) #\_)
         (str::dec-digit-string-p-aux str (+ 1 plen) slen)))

  ///

  (local (in-theory (enable vl-pgenstr string-append)))

  (defthm vl-pgenstr-p-of-vl-pgenstr
    (implies (and (force (stringp prefix))
                  (force (natp n)))
             (vl-pgenstr-p prefix (vl-pgenstr prefix n))))

  (local (defthm nth-underscore-when-dec-digit-char-listp
           (implies (str::dec-digit-char-listp chars)
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




(encapsulate
  ()
  (local (in-theory (disable (:t true-fix)
                             (:t true-equiv)
                             (true-fix)
                             true-fix)))

  (fty::defalist vl-namedb-nameset
    :key-type stringp
    :val-type true-p
    :keyp-of-nil nil
    :valp-of-nil nil))

(defthm string-listp-of-alist-keys-when-vl-namedb-nameset-p
  (implies (vl-namedb-nameset-p x)
           (string-listp (alist-keys x)))
  :hints(("Goal" :induct (len x))))

(defthm vl-namedb-nameset-p-of-make-lookup-alist
  (implies (string-listp names)
           (vl-namedb-nameset-p (make-lookup-alist names)))
  :hints(("Goal" :in-theory (enable make-lookup-alist))))



(fty::defalist vl-namedb-prefixmap
  :key-type stringp
  :val-type natp
  :keyp-of-nil nil
  :valp-of-nil nil)

(defthm string-listp-of-alist-keys-when-vl-namedb-prefixmap-p
  (implies (vl-namedb-prefixmap-p x)
           (string-listp (alist-keys x)))
  :hints(("Goal" :induct (len x))))




(define vl-pgenstr-highest-of-alist-keys ((prefix stringp)
                                          (names  vl-namedb-nameset-p))
  :short "Fusion of vl-pgenstr-highest and alist-keys, for efficiency."
  :enabled t
  :verify-guards nil

  (mbe :logic
       (vl-pgenstr-highest prefix (alist-keys names))
       :exec
       (cond ((atom names)
              0)
             ((vl-pgenstr-p prefix (caar names))
              (max (vl-pgenstr->val prefix (caar names))
                   (vl-pgenstr-highest-of-alist-keys prefix (cdr names))))
             (t
              (vl-pgenstr-highest-of-alist-keys prefix (cdr names)))))

  ///
  (local (in-theory (enable vl-pgenstr-highest)))
  (verify-guards vl-pgenstr-highest-of-alist-keys))


(defsection vl-prefix-map-correct-p

  (defund vl-prefix-map-correct-p-aux (domain pmap names)
    ;; Ensure PMAP[KEY] = (VL-PGENSTR-HIGHEST KEY NAMES) forall KEY in DOMAIN.
    (declare (xargs :guard (and (string-listp domain)
                                (vl-namedb-prefixmap-p pmap)
                                (string-listp names))))
    (if (atom domain)
        t
      (let ((lookup (hons-get (car domain) pmap)))
        (and (equal (cdr lookup) (vl-pgenstr-highest (car domain) names))
             (vl-prefix-map-correct-p-aux (cdr domain) pmap names)))))

  (defund vl-prefix-map-correct-p (pmap names)
    ;; Ensure PMAP[KEY] = (VL-PGENSTR-HIGHEST KEY NAMES) forall KEY bound in PMAP.
    (declare (xargs :guard (and (vl-namedb-prefixmap-p pmap)
                                (string-listp names))))
    (vl-prefix-map-correct-p-aux (alist-keys pmap) pmap names))

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
           (implies (not (member-equal key (alist-keys alist)))
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
                   (domain (alist-keys pmap))
                   (pmap pmap)
                   (names names)
                   (key prefix))))))

  (defthm vl-prefix-map-correct-p-aux-when-subset
    (implies (and (subsetp-equal x y)
                  (vl-prefix-map-correct-p-aux y pmap names))
             (vl-prefix-map-correct-p-aux x pmap names))
    :hints(("Goal" :induct (len x))))

  (defcong set-equiv equal (vl-prefix-map-correct-p-aux x pmap names) 1
    :event-name vl-prefix-map-correct-p-aux-preserves-set-equiv-x
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
                   (domain (alist-keys pmap)))
                  (:instance vl-prefix-map-correct-p-aux-when-subset
                   (x (alist-keys (HONS-SHRINK-ALIST PMAP NIL)))
                   (y (alist-keys PMAP))
                   (pmap (HONS-SHRINK-ALIST PMAP NIL))))))))



(define vl-namedb-pmap-okp ((names vl-namedb-nameset-p)
                            (pmap  vl-namedb-prefixmap-p))
  (b* ((names (vl-namedb-nameset-fix names))
       (pmap  (vl-namedb-prefixmap-fix pmap)))
    (vl-prefix-map-correct-p pmap (alist-keys names)))
  ///
  (defthm vl-namedb-pmap-okp-of-nil
    (implies (not pmap)
             (vl-namedb-pmap-okp names pmap)))
  (deffixequiv vl-namedb-pmap-okp))

(define vl-namedb-pmap-fix ((names vl-namedb-nameset-p)
                            (pmap  vl-namedb-prefixmap-p))
  :guard (vl-namedb-pmap-okp names pmap)
  :returns (pmap-fix (and (vl-namedb-prefixmap-p pmap-fix)
                          (vl-namedb-pmap-okp names pmap-fix)))
  :inline t
  (mbe :logic (b* ((names (vl-namedb-nameset-fix names))
                   (pmap  (vl-namedb-prefixmap-fix pmap)))
                (if (vl-namedb-pmap-okp names pmap)
                    pmap
                  nil))
       :exec pmap)
  :prepwork ((local (in-theory (enable vl-namedb-pmap-okp))))
  ///
  (defthm vl-namedb-pmap-fix-when-vl-namedb-pmap-okp
    (implies (vl-namedb-pmap-okp names pmap)
             (equal (vl-namedb-pmap-fix names pmap)
                    (vl-namedb-prefixmap-fix pmap))))
  (defthm vl-namedb-pmap-okp-of-vl-namedb-pmap-fix
    (implies (vl-namedb-nameset-p names)
             (vl-namedb-pmap-okp names
                                 (vl-namedb-pmap-fix names pmap))))
  (deffixequiv vl-namedb-pmap-fix))

(define vl-namedb-pset-okp ((pmap  vl-namedb-prefixmap-p)
                            (pset  vl-namedb-nameset-p))
  (b* ((pmap (vl-namedb-prefixmap-fix pmap))
       (pset (vl-namedb-nameset-fix pset)))
    (set-equiv (alist-keys pset) (alist-keys pmap)))
  ///
  (deffixequiv vl-namedb-pset-okp))

(define vl-namedb-pset-fix ((names vl-namedb-nameset-p)
                            (pmap  vl-namedb-prefixmap-p)
                            (pset  vl-namedb-nameset-p))
  :guard (and (vl-namedb-pmap-okp names pmap)
              (vl-namedb-pset-okp pmap pset))
  :returns (pset-fix (and (vl-namedb-nameset-p pset-fix)
                          (vl-namedb-pset-okp (vl-namedb-pmap-fix names pmap) pset-fix)))
  :inline t
  (mbe :logic (b* ((pmap (vl-namedb-pmap-fix names pmap))
                   (pset (vl-namedb-nameset-fix pset)))
                (if (vl-namedb-pset-okp pmap pset)
                    pset
                  (make-lookup-alist (alist-keys (vl-namedb-prefixmap-fix pmap)))))
       :exec pset)
  :prepwork ((local (in-theory (enable vl-namedb-pset-okp))))
  ///
  (defthm vl-namedb-pset-fix-when-vl-namedb-pset-okp
    (implies (and (vl-namedb-pmap-okp names pmap)
                  (vl-namedb-pset-okp pmap pset))
             (equal (vl-namedb-pset-fix names pmap pset)
                    (vl-namedb-nameset-fix pset))))

  (deffixequiv vl-namedb-pset-fix))


(defprod vl-namedb
  :tag :vl-namedb
  :layout :tree
  ((names  vl-namedb-nameset-p)
   (pmap   vl-namedb-prefixmap-p :reqfix (vl-namedb-pmap-fix names pmap))
   (pset   vl-namedb-nameset-p   :reqfix (vl-namedb-pset-fix names pmap pset)))
  :require (and (vl-namedb-pmap-okp names pmap)
                (vl-namedb-pset-okp pmap pset))

  :short "Name database structure."

  :long "<p>A name db has three fields:</p>

<ul> <li>@('names'), a fast alist that associates strings to @('t').</li>
<li>@('pmap'), a fast alist that associates strings to natural numbers.</li>
<li>@('pset'), a fast alist that associates strings to @('t').</li> </ul>

<p><u>Invariant</u>.  Each @('prefix') bound in @('pmap') is bound to
@('(vl-pgenstr-highest prefix (alist-keys names))').</p>

<p><u>Invariant</u>.  The @('pset') binds exactly those @('prefix')es that are
bound in @('pmap').</p>

<p>Intuitively, the @('names') represents the set of all names that are
currently in use.  We use a fast-alist representation so that we can very
quickly determine whether a plain name is available.</p>

<p>Meanwhile, the @('pmap') allows us to quickly generate indexed names.  In
particular, it binds some prefixes with their highest used index.  This way, we
only need to scan the @('names') once per prefix.</p>

<p>The @('pset') is really just an optimization that allows us to avoid needing
to shrink the psets.</p>")

(defthm vl-namedb->pset-under-set-equiv
  (set-equiv (alist-keys (vl-namedb->pset x))
             (alist-keys (vl-namedb->pmap x)))
  :hints(("Goal"
          :in-theory (e/d (vl-namedb-pset-okp)
                          (vl-namedb-requirements))
          :use ((:instance vl-namedb-requirements)))))

(defthm vl-prefix-map-correct-p-when-vl-namedb-p
  (vl-prefix-map-correct-p (vl-namedb->pmap x)
                           (alist-keys (vl-namedb->names x)))
  :hints(("Goal"
          :in-theory (e/d (vl-namedb-pmap-okp)
                          (vl-namedb-requirements))
          :use ((:instance vl-namedb-requirements)))))


(defthm hons-assoc-equal-of-vl-namedb->pmap
  ;; This is better than HONS-ASSOC-EQUAL-WHEN-VL-PREFIX-MAP-CORRECT-P, because
  ;; we avoid the free variable NAMES by explicitly saying to consider the cars
  ;; of NAMES.
  (implies (hons-assoc-equal prefix (vl-namedb->pmap db))
           (equal (hons-assoc-equal prefix (vl-namedb->pmap db))
                  (let ((names (alist-keys (vl-namedb->names db))))
                    (cons prefix (vl-pgenstr-highest prefix names)))))
  :hints(("goal"
          :in-theory (disable hons-assoc-equal-when-vl-prefix-map-correct-p)
          :use ((:instance hons-assoc-equal-when-vl-prefix-map-correct-p
                           (pmap (vl-namedb->pmap db))
                           (names (alist-keys (vl-namedb->names db))))))))


(define vl-namedb-allnames
  :short "@(call vl-namedb-p) returns a list of all names that are
considered to be used by the name db."
  ((db vl-namedb-p))
  :returns (allnames string-listp)
  :long "<p>This function is not particularly efficient, and probably should
not ordinarily be executed in real programs.  Its main purpose is to establish
the freshness guarantee for name DBs, described in @(see vl-namedb-p).</p>"
  (alist-keys (vl-namedb->names db))
  ///
  (deffixequiv vl-namedb-allnames))



(define vl-empty-namedb ()
  :short "@(call vl-empty-namedb) creates an empty name db."
  :returns (db vl-namedb-p)
  (make-vl-namedb :names nil :pmap nil :pset nil)
  ///
  (in-theory (disable (:executable-counterpart vl-empty-namedb)))

  (defthm vl-namedb-allnames-of-vl-empty-namedb
    (equal (vl-namedb-allnames (vl-empty-namedb))
           nil)))


(define vl-starting-namedb ((names string-listp))
  :short "@(call vl-starting-namedb) creates a name database that regards
@('names') as already in use."
  :returns (db vl-namedb-p)
  (make-vl-namedb :names (make-lookup-alist (string-list-fix names))
                  :pmap nil
                  :pset nil)
  ///
  (in-theory (disable (:executable-counterpart vl-starting-namedb)))

  (defthm vl-namedb-allnames-of-vl-starting-namedb
    (equal (vl-namedb-allnames (vl-starting-namedb names))
           (string-list-fix names))
    :hints(("Goal" :in-theory (enable vl-namedb-allnames))))

  (deffixequiv vl-starting-namedb))


(define vl-namedb-indexed-name
  :short "@(call vl-namedb-indexed-name) constructs a fresh name that looks
like @('prefix_n') for some natural number @('n')."
  ((prefix stringp)
   (db     vl-namedb-p))
  :returns (mv fresh-name new-db)
  :verify-guards nil
  (b* ((prefix (string-fix prefix))

       ;; Now, look up the highest index associated with the desired name.  If
       ;; there's an entry in the pmap, we can use it.  Otherwise, we have to
       ;; scan the namespace.
       (names   (vl-namedb->names db))
       (pmap    (vl-namedb->pmap db))
       (pset    (vl-namedb->pset db))

       (lookup  (hons-get prefix pmap))
       (maxidx  (if lookup
                    (cdr lookup)
                  (vl-pgenstr-highest-of-alist-keys prefix names)))
       (newidx  (+ maxidx 1))
       (newname (vl-pgenstr prefix newidx))

       (names   (hons-acons newname t names))
       (pmap    (hons-acons prefix newidx pmap))
       (pset    (if lookup
                    pset
                  (hons-acons prefix t pset)))

       (db (change-vl-namedb db :names names :pmap pmap :pset pset)))
    (mv newname db))
  ///
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
                    (member-equal prefix (alist-keys pmap)))
           :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

  (local (defthm lemma3
           (implies (and (vl-prefix-map-correct-p pmap names)
                         (vl-namedb-prefixmap-p pmap)
                         (stringp prefix))
                    (vl-prefix-map-correct-p
                     (cons (cons prefix (+ 1 (vl-pgenstr-highest prefix names))) pmap)
                     (cons (vl-pgenstr prefix (+ 1 (vl-pgenstr-highest prefix names))) names)))
           :hints(("goal" :in-theory (enable vl-prefix-map-correct-p)))))

  (encapsulate
    ()
    (local (in-theory (enable vl-namedb-pset-okp
                              vl-namedb-pmap-okp)))
    (verify-guards vl-namedb-indexed-name))

  (defthm stringp-of-vl-namedb-indexed-name
    (stringp (mv-nth 0 (vl-namedb-indexed-name prefix db)))
    :rule-classes :type-prescription)

  (defthm vl-namedb-p-of-vl-namedb-indexed-name
    (vl-namedb-p (mv-nth 1 (vl-namedb-indexed-name prefix db)))
    :hints(("Goal" :in-theory (enable vl-namedb-pset-okp
                                      vl-namedb-pmap-okp))))

  (defthm vl-namedb-allnames-of-vl-namedb-indexed-name
    (equal (vl-namedb-allnames (mv-nth 1 (vl-namedb-indexed-name prefix db)))
           (cons (mv-nth 0 (vl-namedb-indexed-name prefix db))
                 (vl-namedb-allnames db)))
    :hints(("Goal" :in-theory (enable vl-namedb-allnames))))

  (defthm vl-namedb->names-of-vl-namedb-indexed-name
    (vl-namedb->names (mv-nth 1 (vl-namedb-indexed-name prefix db))))

  (local (in-theory (disable ACL2::ALIST-KEYS-MEMBER-HONS-ASSOC-EQUAL)))

  (defthm vl-namedb-indexed-name-is-fresh
    (b* (((mv fresh-name ?new-db)
          (vl-namedb-indexed-name prefix db)))
      (not (member-equal fresh-name (vl-namedb-allnames db))))
    :hints(("Goal" :in-theory (enable vl-namedb-allnames))))

  (deffixequiv vl-namedb-indexed-name))


(defsection vl-unlike-any-prefix-p
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
     :event-name vl-unlike-any-prefix-p-preserves-set-equiv-prefixes
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
                          (vl-unlike-any-prefix-p name (alist-keys pset)))
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
                   (vl-unlike-any-prefix-p name (alist-keys pmap)))
              (vl-prefix-map-correct-p-aux domain pmap (cons name names)))
     :hints(("Goal" :in-theory (enable vl-prefix-map-correct-p-aux)))))

  (defthm vl-prefix-map-correct-p-when-vl-unlike-any-prefix-p
    (implies (and (vl-prefix-map-correct-p pset names)
                  (vl-unlike-any-prefix-p name (alist-keys pset)))
             (vl-prefix-map-correct-p pset (cons name names)))
    :hints(("Goal" :in-theory (enable vl-prefix-map-correct-p)))))



(define vl-unlike-any-prefix-p-of-alist-keys ((name stringp)
                                              (pset vl-namedb-nameset-p))
  :enabled t
  (mbe :logic
       (vl-unlike-any-prefix-p name (alist-keys pset))
       :exec
       (or (atom pset)
           (and (not (vl-pgenstr-p (caar pset) name))
                (vl-unlike-any-prefix-p-of-alist-keys name (cdr pset))))))


(define vl-namedb-plain-name
  :short "Safely try to generate a particular name."
  ((name stringp     "The desired name to use, if available.")
   (db   vl-namedb-p "The name database."))
  :returns
  (mv (fresh-name stringp :rule-classes :type-prescription
                  "When possible this is just @('name').  When @('name') is
                   already in use, we instead produce, e.g., @('name_1'),
                   @('name_2'), or similar.")
      (new-db vl-namedb-p
              "Extended name database with @('fresh-name') being marked as
               used."))
  :prepwork((local (in-theory (enable vl-namedb-pmap-okp))))

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

       ((unless (vl-unlike-any-prefix-p-of-alist-keys name pset))
        (mv-let (fresh-name db)
          (vl-namedb-indexed-name name db)
          (prog2$
           (cw "; Name db note: ~x0 is like an existing prefix; made ~x1 instead.~%"
               name fresh-name)
           (mv fresh-name db))))

       (names   (hons-acons name t names))
       (db (change-vl-namedb db :names names)))
    (mv name db))
  ///
  (encapsulate
    ()
    (local (defthm lemma
             ;; Ugh, kind of ugly, but not too bad really.  This is just addressing
             ;; the particular case that doesn't default to indexed name generation
             (implies (and (not (hons-assoc-equal name (vl-namedb->names db)))
                           (vl-unlike-any-prefix-p name (alist-keys (vl-namedb->pmap db))))
                      (equal
                       (vl-namedb-allnames (vl-namedb (cons (cons name t) (vl-namedb->names db))
                                                      (vl-namedb->pmap db)
                                                      (vl-namedb->pset db)))
                       (cons (str-fix name) (vl-namedb-allnames db))))
             :hints(("Goal" :in-theory (enable vl-namedb-allnames)))))

    (defthm vl-namedb-allnames-of-vl-namedb-plain-name
      (b* (((mv fresh-name new-db) (vl-namedb-plain-name name db)))
        (equal (vl-namedb-allnames new-db)
               (cons fresh-name
                     (vl-namedb-allnames db))))
      :hints(("Goal" :in-theory (disable
                                 CONS-OF-STR-FIX-K-UNDER-VL-NAMEDB-NAMESET-EQUIV
; Matt K. mod, 11/28/2020: Accommodate fix for storing patterned congruences.
                                 (:congruence cons-streqv-congruence-on-k-under-vl-namedb-nameset-equiv)
      ))))

    (defthm vl-namedb->names-of-vl-namedb-plain-name
      (vl-namedb->names (mv-nth 1 (vl-namedb-plain-name name db)))))

  (encapsulate
    ()
    (local (defthm crock
             (implies (alistp alist)
                      (iff (member-equal prefix (alist-keys alist))
                           (hons-assoc-equal prefix alist)))
             :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

    (local (defthm lemma
             (implies (and (not (hons-assoc-equal name (vl-namedb->names db)))
                           (vl-unlike-any-prefix-p name (alist-keys (vl-namedb->pmap db))))
                      (not (member-equal name (vl-namedb-allnames db))))
             :hints(("Goal" :in-theory (enable vl-namedb-allnames)))))

    (defthm vl-namedb-plain-name-is-fresh
      (not (member-equal (mv-nth 0 (vl-namedb-plain-name name db))
                         (vl-namedb-allnames db)))
      :hints((and stable-under-simplificationp
                  '(:in-theory (disable vl-namedb-indexed-name-is-fresh)
                    :use ((:instance vl-namedb-indexed-name-is-fresh
                           (prefix name))))))))

  (local (defthm crock
           ;; bozo gross....
           (implies (not (stringp name))
                    (equal (VL-NAMEDB-INDEXED-NAME NAME DB)
                           (VL-NAMEDB-INDEXED-NAME "" db)))
           :hints(("Goal"
                   :in-theory (e/d (streqv) (vl-namedb-indexed-name-streqv-congruence-on-prefix))
                   :use ((:instance vl-namedb-indexed-name-streqv-congruence-on-prefix
                          (prefix name)
                          (prefix-equiv "")))))))

  (deffixequiv vl-namedb-plain-name))


(define vl-namedb-plain-name-quiet
  :short "Same as @(see vl-namedb-plain-name), but doesn't print messages when
names aren't available."
  ((name stringp)
   (db   vl-namedb-p))
  :returns (mv fresh-name new-db)
  :enabled t
  :guard-hints(("Goal" :in-theory (enable vl-namedb-plain-name
                                          vl-namedb-pmap-okp)))
  (mbe :logic (vl-namedb-plain-name name db)
       :exec
       (b* ((names   (vl-namedb->names db))
            (pset    (vl-namedb->pset db))

            ((when (hons-get name names))
             (mv-let (fresh db)
               (vl-namedb-indexed-name name db)
               (mv fresh db)))

            ((unless (vl-unlike-any-prefix-p-of-alist-keys name pset))
             (mv-let (fresh db)
               (vl-namedb-indexed-name name db)
               (mv fresh db)))

            (names   (hons-acons name t names))
            (db (change-vl-namedb db :names names)))
         (mv name db))))


(define vl-free-namedb ((db vl-namedb-p))
  :short "@(call vl-free-namedb) frees the fast alists associated with a name
db and returns @('nil')."
  :long "<p>The name db should never be used after this function is called,
since doing so will result in fast-alist discipline failures.</p>

<p>Note that we leave this function enabled.</p>"

  (progn$ (fast-alist-free (vl-namedb->names db))
          (fast-alist-free (vl-namedb->pmap db))
          (fast-alist-free (vl-namedb->pset db))
          nil))


(define vl-namedb-plain-names
  :short "Generate a list of fresh names."
  ((names string-listp)
   (db    vl-namedb-p))
  :returns (mv (fresh-names string-listp)
               (new-db vl-namedb-p))
  :long "<p>When possible, @('fresh-names') are just @('names').  When this is
not possible due to name collisions, some of the @('fresh_names') may have
additional indexes as in @(see vl-namedb-indexed-name), and notes may be
printed.</p>"

  (b* (((when (atom names))
        (mv nil (vl-namedb-fix db)))
       ((mv name1 db)
        (vl-namedb-plain-name (car names) db))
       ((mv rest db)
        (vl-namedb-plain-names (cdr names) db)))
    (mv (cons name1 rest) db))
  ///
  (defthm vl-namedb-plain-names-are-fresh
    (implies (member-equal a (vl-namedb-allnames db))
             (not (member-equal a (mv-nth 0 (vl-namedb-plain-names names db))))))

  (defthm vl-namedb-allnames-of-vl-namedb-plain-names
    (equal (vl-namedb-allnames (mv-nth 1 (vl-namedb-plain-names names db)))
           (revappend (mv-nth 0 (vl-namedb-plain-names names db))
                      (vl-namedb-allnames db))))

  (deffixequiv vl-namedb-plain-names))
