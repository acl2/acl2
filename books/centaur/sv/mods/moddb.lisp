; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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

(in-package "SV")
(include-book "svmods")
(include-book "../svex/lists")
(include-book "centaur/misc/numlist" :dir :system)
(include-book "add-ons/hash-stobjs" :dir :system)
(include-book "std/stobjs/absstobjs" :dir :system)
(include-book "std/stobjs/clone" :dir :system)
(include-book "misc/records" :dir :system)
(include-book "centaur/misc/stobj-swap" :dir :system)
(include-book "std/lists/index-of" :dir :system)
(include-book "coi/nary/nary" :dir :system)
(include-book "std/strings/eqv" :dir :system)
(include-book "std/stobjs/nested-stobjs" :dir :system)
(include-book "centaur/misc/duplicates" :dir :system)
(local (include-book "std/lists/acl2-count" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "std/lists/update-nth" :dir :system))
(local (include-book "std/alists/hons-assoc-equal" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "clause-processors/generalize" :dir :system))
(local (include-book "clause-processors/find-subterms" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "std/lists/sets" :dir :System))
(local (acl2::use-trivial-ancestors-check))


(local (in-theory (disable nth update-nth
                           acl2::nth-when-zp
                           acl2::update-nth-when-zp)))

(local (std::add-default-post-define-hook :fix))

(local (defthm my-nth-of-take
         (equal (nth m (take n x))
                (and (< (nfix m) (nfix n))
                     (nth m x)))))

(local (defthm hons-assoc-equal-of-hons-remove-assoc
         (equal (hons-assoc-equal k1 (acl2::hons-remove-assoc k2 a))
                (and (not (equal k1 k2))
                     (hons-assoc-equal k1 a)))))

(local (defsection my-open-take
         (defthmd my-open-take
           (equal (take n x)
                  (if (zp n)
                      nil
                    (cons (car x) (take (1- n) (cdr x)))))
           :rule-classes ((:definition :controller-alist ((take t nil)))))

         (in-theory (disable acl2::take))))

(local (defun count-down (idx min)
         (declare (xargS :measure (nfix (- (nfix idx) (nfix min)))))
         (if (zp (- (nfix idx) (nfix min)))
             min
           (count-down (1- (nfix idx)) min))))

(local (in-theory (disable acl2::nth-of-take)))

(defmacro patbind-stobj-get (&rest args)
  `(acl2::patbind-stobj-get . ,args))


(defxdoc moddb
  :parents (sv)
  :short "A database object that provides a unique numbering of all the wires in
          a module hierarchy."
  :long "<p>A moddb is a stobj that provides a fast method of enumerating wires
and a compact, high-performance mapping between these indices and their
names/declarations.  It is used in @(see svex-compilation) to avoid more memory
hungry methods of mapping hierarchical wire names to values.</p>

<p>A moddb is a nested stobj structure defined as follows:</p>

@(def moddb)

<p>where:</p>
<ul>
<li>@('moddb->nmods') contains the number of modules in the database.</li>
<li>@('moddb->mods') is an array of @(see elab-mod) structures, which we
describe below, of which @('moddb->nmods') are valid.</li>
<li>@('moddb->modname-idxes') is a hash table mapping module names to indices.</li>
</ul>

<p>Together, @('moddb->mods') and @('moddb->modname-idxes') constitute a
two-way mapping between module names and module indices.  It is a requirement
of a well-formed moddb that both of the following hold:</p>

@({
  (implies (and (natp i) (< i (moddb->nmods moddb)))
           (equal (moddb->modname-idxes-get
                   (elab-mod->name (moddb->modsi i moddb))
                   moddb)
                  i))

  (implies (moddb->modname-idxes-get name moddb)
           (equal (elab-mod->name
                   (moddb->modsi
                    (moddb->modname-idxes-get name moddb)
                    moddb))
                  name))
 })

<p>The @('moddb->mods') field is an array of @(see elab-mod) stobjs.  Thus, a
moddb is a nested stobj -- see @(see acl2::nested-stobjs).  An elab-mod is an
abstract stobj; more detailed documentation of its accessors/updaters is in
@(see elab-mod).  Generally speaking, an elab-mod has a name, an array of
wires, and an array of submodule instances, as well as a count of the total
number of wires/instances in itself its instances.  For each submodule
instance, it also has a wire offset and an instance offset, which say where
that submodule instance falls in the module-wide ordering of wires and
instances.</p>

<h3>Usage</h3>

<p>To create a moddb, users should always use @(see module->db) to put the
dependencies of some module in a @(see modalist) into the database.  Any other
updates to a moddb require careful consideration of well-formedness
invariants.</p>")


(defxdoc elab-mod
  :parents (moddb)
  :short "Part of a moddb representing a single module."
  :long "<p>Note: This is partly implementation-level documentation for moddb.
Specifically, none of the updater functions listed here should be used in the
context of operating on a moddb -- rather, a moddb should be built from a @(see
modalist) using one or more calls of @(see module->db), and treated as
read-only thereafter.  It is fine to use the (read-only) accessor
functions.</p>

<p>An elab-mod is an abstract stobj whose logical story is that it is a
record (accessed using @(see g)/@(see s) -- see @(see acl2::misc/records))
containing the following fields:</p>

<ul>
<li><i>name</i> -- the name of the module, a @(see modname-p) object</li>
<li><i>totalwires</i> -- the total number of wires in the module and all its
instances, a natural</li>
<li><i>totalinsts</i> -- the total number of instances in the module and all
its instances, a natural</li>
<li><i>orig-mod</i> -- the @(see module) that this was generated from</li>
<li><i>wires</i> -- the list of @(see wire)s local to the module</li>
<li><i>insts</i> -- the list of @(see modinst)s local to the module.</li>
</ul>

<p>The executable accessors/updaters of these (except for wires and insts; see
below) are named, e.g., @('elab-mod->name')/@('update-elab-mod->name').</p>

<p>The wires and insts fields are special in that they cannot be accessed
directly in execution; in fact, they are not actually lists, but arrays.  They
are also backed by hash tables so that wire or instance indices may be looked
up by wire/instance name.  (Well-formedness enforced by the abstract stobj
representation makes this mapping invertible.)  The following accessors are
used to access information about the wires/instances:</p>

<ul>

<li>@('(elab-mod-nwires elab-mod)') -- the number of local wires</li>

<li>@('(elab-mod-wiretablei wire-idx elab-mod)') -- the nth wire</li>

<li>@('(elab-mod-wirename->idx name elab-mod)') -- the index for the named
wire</li>

<li>@('(elab-mod-add-wire wire elab-mod)') -- add a wire to the table</li>

<li>@('(elab-mod-ninsts elab-mod)') -- the number of local module
instances</li>

<li>@('(elab-mod->instname inst-idx elab-mod)') -- the instname of the nth
module instance</li>

<li>@('(elab-mod->inst-modidx inst-idx elab-mod)') -- the index of the module
instantiated by the nth instance</li>

<li>@('(elab-mod->inst-wireoffset inst-idx elab-mod)') -- the total number of
wires in the module up until this instance -- i.e. the number of local wires
plus the sum of the totalwires of the modules of lower-numbered instances</li>

<li>@('(elab-mod->inst-instoffset inst-idx elab-mod)') -- the total number of
instances in the module up until this instance -- i.e., inst-idx plus the sum
of the totalinsts of the modules of lower-numbered instances</li>

<li>@('(elab-mod-instname->idx name elab-mod)') -- the index for the named
instance</li>

<li>@('(elab-mod-add-inst elab-modinst$c elab-mod)') -- copy an elab-modinst$c
stobj into the elab-mod as a new instance.</li>

</ul>

<p>All of the above functions execute in constant time, even though several of
their logical definitions are linear in the number of wires/insts.</p>

<p>A wire or instance cannot be removed once added.  There isn't even any way
to clear out the wires or instances; just start over with a new elab-mod.</p>")

(defxdoc moddb.lisp :parents (moddb))
(local (xdoc::set-default-parents moddb.lisp))


(defsection wirelist->names

  (defthm len-of-wirelist->names
    (equal (len (wirelist->names x))
           (len x)))

  (defthm nth-of-wirelist->names
    (implies (< (nfix n) (len x))
             (equal (nth n (wirelist->names x))
                    (wire->name (nth n x))))
    :hints(("Goal" :in-theory (enable nth wirelist->names))))

  (defthmd member-when-nth-of-wirelist->names
    (implies (and (equal k (wire->name (nth n x)))
                  (< (nfix n) (len x)))
             (member k (wirelist->names x)))
    :hints(("Goal" :in-theory (enable wirelist->names nth))))

  (defthmd nth-index-of-wirelist->names
    (implies (member k (wirelist->names x))
             (equal (wire->name (nth (index-of k (wirelist->names x)) x))
                    k))
    :hints(("Goal" :in-theory (enable index-of wirelist->names))))

  (defthmd member-of-wirelist->names
    (implies (member k (wirelist->names x))
             (name-p k))
    :hints(("Goal" :in-theory (enable wirelist->names)))
    :rule-classes :forward-chaining)

  (defthmd wirelist-p-implies-true-listp
    (implies (wirelist-p x)
             (true-listp x))
    :hints(("Goal" :in-theory (enable wirelist-p))))

  (defthmd index-of-when-nth-of-wirelist->names
    (implies (and (equal k (wire->name (nth n x)))
                  (< (nfix n) (len x)))
             (<= (index-of k (wirelist->names x)) (nfix n)))
    :hints(("Goal" :in-theory (enable index-of nth wirelist->names))
           (and stable-under-simplificationp
                (not (acl2::access acl2::clause-id id :pool-lst))
                '(:induct (nth n x))))
    :rule-classes :linear))

(local (in-theory (enable wirelist-p-implies-true-listp
                          member-when-nth-of-wirelist->names
                          nth-index-of-wirelist->names
                          member-of-wirelist->names
                          index-of-when-nth-of-wirelist->names)))



(defsection elab-modinst$c
  (defstobj elab-modinst$c
    ;; must be unique in the parent module
    (elab-modinst$c->instname :type (satisfies name-p) :initially "")

    ;; must be a module index less than that of the parent module (??)
    (elab-modinst$c->modidx :type (integer 0 *) :initially 0)

    ;; for modinst[0], must parent mod's nwires
    ;; for modinst[n] n>0, must be modinst[n-1].offset + mod[modinst[n-1].modidx].totalwires.
    (elab-modinst$c->wire-offset :type (integer 0 *) :initially 0)
    (elab-modinst$c->inst-offset :type (integer 0 *) :initially 0)
    :inline t)

  (acl2::defstobj-clone elab-modinst$c2 elab-modinst$c
    :suffix "2")

  (define elab-modinst-fix ((x elab-modinst$cp))
    :returns (xx elab-modinst$cp)
    :hooks nil
    :prepwork ((local (defthm equal-of-len
                        (implies (syntaxp (quotep y))
                                 (equal (equal (len x) y)
                                        (if (zp y)
                                            (and (equal y 0)
                                                 (atom x))
                                          (and (consp x)
                                               (equal (len (cdr x)) (1- y)))))))))
    (mbe :logic (list (name-fix (nth 0 x))
                      (nfix (nth 1 x))
                      (nfix (nth 2 x))
                      (nfix (nth 3 x)))
         :exec x)
    ///
    (defthm elab-modinst-fix-when-elab-modinst$cp
      (implies (elab-modinst$cp x)
               (equal (elab-modinst-fix x) x)))

    (deffixtype elab-modinst$c :pred elab-modinst$cp :fix elab-modinst-fix
      :equiv elab-modinst$c-equiv :define t :forward t)


    (defthm len-of-elab-modinst-fix
      (equal (len (elab-modinst-fix x)) 4))

    (defthm true-listp-of-elab-modinst-fix
      (true-listp (elab-modinst-fix x))
      :rule-classes (:rewrite :type-prescription))

    (defthm nths-of-elab-modinst-fix
      (and (equal (nth 0 (elab-modinst-fix x))
                  (name-fix (nth 0 x)))
           (equal (nth 1 (elab-modinst-fix x))
                  (nfix (nth 1 x)))
           (equal (nth 2 (elab-modinst-fix x))
                  (nfix (nth 2 x)))
           (equal (nth 3 (elab-modinst-fix x))
                  (nfix (nth 3 x))))))

  (define elab-modinst$c-fix (elab-modinst$c)
    :inline t
    :enabled t
    (mbe :logic (non-exec (elab-modinst-fix elab-modinst$c))
         :exec elab-modinst$c))

  (define elab-modinst$c-copy (elab-modinst$c elab-modinst$c2)
    :guard-hints(("Goal" :in-theory (enable elab-modinst$c-fix)
                  :do-not-induct t))
    :prepwork ((local (defthm equal-of-len
                        (implies (syntaxp (quotep y))
                                 (equal (equal (len x) y)
                                        (if (zp y)
                                            (and (equal y 0)
                                                 (atom x))
                                          (and (consp x)
                                               (equal (len (cdr x)) (1- y))))))))
               (local (in-theory (enable update-nth))))
    :enabled t
    (mbe :logic (non-exec (elab-modinst$c-fix elab-modinst$c))
         :exec (b* ((elab-modinst$c2 (update-elab-modinst$c->instname
                                      (elab-modinst$c->instname elab-modinst$c)
                                      elab-modinst$c2))
                    (elab-modinst$c2 (update-elab-modinst$c->modidx
                                      (elab-modinst$c->modidx elab-modinst$c)
                                      elab-modinst$c2))
                    (elab-modinst$c2 (update-elab-modinst$c->wire-offset
                                      (elab-modinst$c->wire-offset elab-modinst$c)
                                      elab-modinst$c2)))
                 (update-elab-modinst$c->inst-offset
                  (elab-modinst$c->inst-offset elab-modinst$c)
                  elab-modinst$c2)))
    ///
    (deffixequiv elab-modinst$c-copy)))

(defsection remove-later-duplicates
  (local (in-theory (enable acl2::remove-later-duplicates)))


  (defthm modnamelist-p-of-remove-later-duplicates
    (implies (modnamelist-p x)
             (modnamelist-p (acl2::remove-later-duplicates x)))
    :hints(("Goal" :in-theory (enable modnamelist-p))))

  (defthm namelist-p-of-remove-later-duplicates
    (implies (namelist-p x)
             (namelist-p (acl2::remove-later-duplicates x)))
    :hints(("Goal" :in-theory (enable namelist-p)))))


(defsection elab-modinst-list
  (deflist elab-modinst-list :elt-type elab-modinst$cp :true-listp t)

  (defthm len-elab-modinst-list-fix
    (equal (len (elab-modinst-list-fix x))
           (len x)))

  (define elab-modinst-list-names ((x elab-modinst-list-p))
    :returns (names namelist-p)
    (if (atom x)
        nil
      (cons (name-fix (nth *elab-modinst$c->instname* (car x)))
            (elab-modinst-list-names (cdr x))))
    ///
    (local (Defthm elab-modinst-list-names-of-replicate
             (equal (elab-modinst-list-names (replicate n x))
                    (replicate n (name-fix (nth *elab-modinst$c->instname* x))))
             :hints(("Goal" :in-theory (enable replicate)))))
    (defthm elab-modinst-list-names-of-take
      (equal (elab-modinst-list-names (take n x))
             (namelist-fix (take n (elab-modinst-list-names x))))
      :hints(("Goal" :in-theory (e/d (replicate take)))))

    (defthm len-of-elab-modinst-list-names
      (equal (len (elab-modinst-list-names x))
             (len x)))

    (local (defthmd name-p-when-equal-name-fix
             (implies (equal (name-fix x) y)
                      (name-p y))))

    (defthm instname-of-nth-index-of-elab-modinst-list-names
      (implies (member k (elab-modinst-list-names x))
               (and (equal (name-fix
                            (nth *elab-modinst$c->instname*
                                 (nth (index-of k (elab-modinst-list-names x))
                                      x)))
                           k)
                    (implies (name-p (nth *elab-modinst$c->instname*
                                          (nth (index-of k (elab-modinst-list-names x))
                                               x)))
                             (equal (nth *elab-modinst$c->instname*
                                         (nth (index-of k (elab-modinst-list-names x))
                                              x))
                                    k))))
      :hints(("Goal" :in-theory (enable index-of name-p-when-equal-name-fix))))

    (defthm member-of-names-when-nth
      (implies (and (equal (nth *elab-modinst$c->instname* (nth n x))
                           k)
                    (name-p k)
                    (< (nfix n) (len x)))
               (member k (elab-modinst-list-names x)))
      :hints(("Goal" :in-theory (enable nth)
              :induct (nth n x))))

    (defthm nth-of-elab-modinst-list-names
      (implies (< (nfix n) (len x))
               (equal (nth n (elab-modinst-list-names x))
                      (name-fix (nth *elab-modinst$c->instname* (nth n x)))))
      :hints(("Goal" :in-theory (enable nth))))

    (deffixequiv elab-modinst-list-names
      :hints(("Goal" :in-theory (enable elab-modinst-list-fix))))

    (defthm elab-modinst-list-names-of-append
      (equal (elab-modinst-list-names (append a b))
             (append (elab-modinst-list-names a)
                     (elab-modinst-list-names b)))))

  (define elab-modinst-remove-name ((name name-p) (x elab-modinst-list-p))
    :returns (xx elab-modinst-list-p)
    (if (atom x)
        nil
      (if (equal (name-fix (nth *elab-modinst$c->instname* (car x)))
                 (name-fix name))
          (elab-modinst-remove-name name (cdr x))
        (cons (elab-modinst-fix (car x))
              (elab-modinst-remove-name name (cdr x)))))
    ///
    (deffixequiv elab-modinst-remove-name)

    (defthm elab-modinst-list-names-of-remove-name
      (equal (elab-modinst-list-names (elab-modinst-remove-name name x))
             (remove (name-fix name) (elab-modinst-list-names x)))
      :hints(("Goal" :in-theory (enable elab-modinst-list-names))))

    (defthm elab-modinst-remove-name-when-not-member
      (implies (not (member (name-fix x)
                            (elab-modinst-list-names y)))
               (equal (elab-modinst-remove-name x y)
                      (elab-modinst-list-fix y)))
      :hints(("Goal" :in-theory (enable elab-modinst-list-names
                                        elab-modinst-list-fix)))))

  (define elab-modinst-remove-names ((names namelist-p) (x elab-modinst-list-p))
    :returns (xx elab-modinst-list-p)
    (if (atom names)
        (elab-modinst-list-fix x)
      (elab-modinst-remove-name (car names)
                                (elab-modinst-remove-names (cdr names) x)))
    ///
    (defthm elab-modinst-remove-names-of-nil
      (equal (elab-modinst-remove-names nil x)
             (elab-modinst-list-fix x)))

    (defthm elab-modinst-remove-names-of-nil-second
      (equal (elab-modinst-remove-names x nil)
             nil))

    (defthm elab-modinst-remove-names-of-cons-second
      (equal (elab-modinst-remove-names x (cons y z))
             (if (member (name-fix (nth *elab-modinst$c->instname* y))
                         (namelist-fix x))
                 (elab-modinst-remove-names x z)
               (cons (elab-modinst-fix y)
                     (elab-modinst-remove-names x z))))
      :hints(("Goal" :in-theory (enable namelist-fix
                                        elab-modinst-remove-name)))))

  (define elab-modinsts-nodups-p (x)
    (and (elab-modinst-list-p x)
         (no-duplicatesp-equal (elab-modinst-list-names x)))
    ///
    (defthm elab-modinsts-nodups-p-implies-elab-modinst-list-p
      (implies (elab-modinsts-nodups-p x)
               (elab-modinst-list-p x)))

    (local (defthm no-duplicates-of-append
             (equal (no-duplicatesp-equal (append a b))
                    (and (no-duplicatesp-equal a)
                         (no-duplicatesp-equal b)
                         (not (intersection$ a b))))))

    (defthm elab-modinsts-nodups-p-of-append
      (implies (and (elab-modinsts-nodups-p a)
                    (elab-modinsts-nodups-p b)
                    (not (intersection$ (elab-modinst-list-names a)
                                        (elab-modinst-list-names b))))
               (elab-modinsts-nodups-p (append a b))))

    (defthm elab-modinsts-nodups-p-of-cons
      (equal (elab-modinsts-nodups-p (cons a b))
             (and (elab-modinst$cp a)
                  (elab-modinsts-nodups-p b)
                  (not (member (nth *elab-modinst$c->instname* a)
                               (elab-modinst-list-names b)))))
      :hints(("Goal" :in-theory (enable elab-modinst-list-names)))))



  (define elab-modinsts-rem-dups ((x elab-modinst-list-p))
    :verify-guards nil
    :returns (xx elab-modinsts-nodups-p
                 :hints(("Goal" :in-theory (enable elab-modinsts-nodups-p
                                                   elab-modinst-list-names))))
    (if (atom x)
        nil
      (cons (elab-modinst-fix (car x))
            (elab-modinst-remove-name (nth *elab-modinst$c->instname* (car x))
                                      (elab-modinsts-rem-dups (cdr x)))))
    ///
    (verify-guards elab-modinsts-rem-dups)

    (defthm elab-modinst-list-names-of-remove-duplicate-names
      (equal (elab-modinst-list-names (elab-modinsts-rem-dups x))
             (acl2::remove-later-duplicates (elab-modinst-list-names x)))
      :hints(("Goal" :in-theory (enable elab-modinst-list-names
                                        acl2::remove-later-duplicates)
              :induct t)
             (and stable-under-simplificationp
                  '(:expand ((:free (a b) (acl2::remove-later-duplicates (cons a b))))))))

    (defthm elab-modinsts-rem-dups-when-no-duplicates
      (implies (no-duplicatesp (elab-modinst-list-names x))
               (equal (elab-modinsts-rem-dups x)
                      (elab-modinst-list-fix x)))
      :hints(("Goal" :in-theory (enable elab-modinst-list-names
                                        elab-modinst-list-fix))))

    (defthm elab-modinsts-rem-dups-when-elab-modinsts-nodups-p
      (implies (elab-modinsts-nodups-p x)
               (equal (elab-modinsts-rem-dups x)
                      x))
      :hints(("Goal" :in-theory (enable elab-modinsts-nodups-p))))

    (defthm no-duplicate-names-of-elab-modinsts-rem-dups
      (no-duplicatesp (elab-modinst-list-names (elab-modinsts-rem-dups x)))
      :hints(("Goal" :in-theory (enable elab-modinst-list-names
                                        elab-modinst-list-fix))))

    (deffixequiv elab-modinsts-rem-dups
      :hints(("Goal" :in-theory (enable elab-modinst-list-fix))))

    (deffixtype elab-modinsts-nodups
      :pred elab-modinsts-nodups-p :fix elab-modinsts-rem-dups
      :equiv elab-modinsts-nodups-equiv :define t :forward t)

    (local (defthm elab-modinst-remove-name-of-equal-to-append
             (implies (equal a (append b c))
                      (equal (elab-modinst-remove-name d a)
                             (append (elab-modinst-remove-name d b)
                                     (elab-modinst-remove-name d c))))
             :hints(("Goal" :in-theory (enable elab-modinst-remove-name)))))

    (defthm elab-modinsts-rem-dups-of-append
      (equal (elab-modinsts-rem-dups (append a b))
             (append (elab-modinsts-rem-dups a)
                     (elab-modinst-remove-names
                      (elab-modinst-list-names a)
                      (elab-modinsts-rem-dups b))))
      :hints(("Goal" :in-theory (enable elab-modinst-list-names
                                        elab-modinst-remove-names))))))

(defsection elab-mod$c
  (defconst *default-orig-mod* (make-module))

  (make-event
   `(defstobj elab-mod$c
      ;; must be unique in the moddb
      (elab-mod$c->name :type (satisfies modname-p) :initially "default-modname")

      ;; wire names<->indices must be bijective (and therefore names/indices unique)
      (elab-mod$c->nwires :type (integer 0 *) :initially 0)
      (elab-mod$c->wiretable :type (array (satisfies wire-p) (0))
                             :initially ,(make-wire :name "" :width 1 :low-idx 0) :resizable t)
      (elab-mod$c->wirename-idxes :type (hash-table equal))

      ;; instance names<->indices must be bijective
      (elab-mod$c->ninsts :type (integer 0 *) :initially 0)
      (elab-mod$c->modinsttable :type (array elab-modinst$c (0)) :resizable t)
      (elab-mod$c->modinstname-idxes :type (hash-table equal))

      ;; totalwires is (mod-wirecount orig-mod)
      (elab-mod$c->totalwires :type (integer 0 *) :initially 0)
      (elab-mod$c->totalinsts :type (integer 0 *) :initially 0)

      (elab-mod$c->orig-mod :type (satisfies module-p)
                            :initially ,(make-module)))))

(local (defthm wirelist->names-of-replicate
         (equal (wirelist->names (replicate n x))
                (replicate n (wire->name x)))
         :hints(("Goal" :in-theory (enable wirelist->names replicate)))))







(defsection elab-mod$c-wires-ok
  (defun-sk elab-mod$c-wire-indices-ok (elab-mod$c)
    (forall idx
            (let ((names->idxes (nth *elab-mod$c->wirename-idxes-get* elab-mod$c))
                  (idxes->wires (nth *elab-mod$c->wiretablei* elab-mod$c)))
              (implies (and (natp idx)
                            (< idx (nfix (nth *elab-mod$c->nwires* elab-mod$c))))
                       (let ((name (wire->name (nth idx idxes->wires))))
                         (and (hons-assoc-equal name names->idxes)
                              (equal (cdr (hons-assoc-equal name names->idxes))
                                     idx))))))
    :rewrite :direct)

  (in-theory (disable elab-mod$c-wire-indices-ok))

  (defun-sk elab-mod$c-wire-names-ok (elab-mod$c)
    (forall name
            (let* ((names->idxes (nth *elab-mod$c->wirename-idxes-get* elab-mod$c))
                   (idxes->wires (nth *elab-mod$c->wiretablei* elab-mod$c)))
              (implies (hons-assoc-equal name names->idxes)
                       (let ((idx (cdr (hons-assoc-equal name names->idxes))))
                         (and (natp idx)
                              (< idx (nfix (nth *elab-mod$c->nwires* elab-mod$c)))
                              (equal (wire->name (nth idx idxes->wires))
                                     name))))))
    :rewrite :direct)

  (defthm elab-mod$c-wire-names-ok-linear
    (implies (and (elab-mod$c-wire-names-ok elab-mod$c)
                  (hons-assoc-equal name (nth *elab-mod$c->wirename-idxes-get* elab-mod$c)))
             (< (cdr (hons-assoc-equal name (nth *elab-mod$c->wirename-idxes-get* elab-mod$c)))
                (nfix (nth *elab-mod$c->nwires* elab-mod$c))))
    :rule-classes :linear)

  (in-theory (disable elab-mod$c-wire-names-ok))

  (define wirelist-remove-name ((name name-p) (x wirelist-p))
    :returns (xx wirelist-p)
    (if (atom x)
        nil
      (if (mbe :logic (name-equiv (wire->name (car x))
                                  name)
               :exec (equal (wire->name (car x)) name))
          (wirelist-remove-name name (cdr x))
        (cons (wire-fix (car x))
              (wirelist-remove-name name (cdr x)))))
    ///
    (deffixequiv wirelist-remove-name)

    (defthm wirelist->names-of-remove-name
      (equal (wirelist->names (wirelist-remove-name name x))
             (remove (name-fix name) (wirelist->names x)))
      :hints(("Goal" :in-theory (enable wirelist->names acl2::streqv))))

    (defthm wirelist-remove-name-when-not-member
      (implies (not (member (name-fix x)
                            (wirelist->names y)))
               (equal (wirelist-remove-name x y)
                      (wirelist-fix y)))
      :hints(("Goal" :in-theory (enable wirelist->names
                                        wirelist-fix)))))

  (define wirelist-remove-names ((names namelist-p) (x wirelist-p))
    :returns (xx wirelist-p)
    (if (atom names)
        (wirelist-fix x)
      (wirelist-remove-name (car names)
                            (wirelist-remove-names (cdr names) x)))
    ///
    (defthm wirelist-remove-names-of-nil
      (equal (wirelist-remove-names nil x)
             (wirelist-fix x)))

    (defthm wirelist-remove-names-of-nil-second
      (equal (wirelist-remove-names x nil)
             nil))

    (defthm wirelist-remove-names-of-cons-second
      (equal (wirelist-remove-names x (cons y z))
             (if (member (wire->name y)
                         (namelist-fix x))
                 (wirelist-remove-names x z)
               (cons (wire-fix y)
                     (wirelist-remove-names x z))))
      :hints(("Goal" :in-theory (enable namelist-fix
                                        acl2::streqv
                                        wirelist-remove-name))))

    (defthm wirelist-remove-name-commute
      (equal (wirelist-remove-name b (wirelist-remove-name a x))
             (wirelist-remove-name a (wirelist-remove-name b x)))
      :hints(("Goal" :in-theory (enable wirelist-remove-name)))
      :rule-classes ((:rewrite :loop-stopper ((b a)))))

    (defthmd wirelist-remove-name-of-remove-names
      (equal (wirelist-remove-name a (wirelist-remove-names names x))
             (wirelist-remove-names names (wirelist-remove-name a x))))

    (defthmd wirelist-remove-name-of-remove-names-rev
      (equal (wirelist-remove-names names (wirelist-remove-name a x))
             (wirelist-remove-name a (wirelist-remove-names names x))))

    (defthm wirelist-remove-names-of-remove-name
      (implies (not (member (name-fix name) (wirelist->names x)))
               (equal (wirelist-remove-names (remove-equal name names) x)
                      (wirelist-remove-names names x)))
      :hints(("Goal" :in-theory (enable wirelist-remove-name-of-remove-names))))

    (defthm wirelist-remove-names-of-remove-later-duplicates
      (equal (wirelist-remove-names (acl2::remove-later-duplicates names) x)
             (wirelist-remove-names names x))
      :hints(("Goal" :in-theory (enable acl2::remove-later-duplicates)
              :induct (acl2::remove-later-duplicates names))
             (and stable-under-simplificationp
                  '(:in-theory (enable wirelist-remove-name-of-remove-names)))
             (and stable-under-simplificationp
                  '(:in-theory (enable wirelist-remove-name-of-remove-names-rev))))))

  (define wirelist-nodups-p (x)
    (and (wirelist-p x)
         (no-duplicatesp-equal (wirelist->names x)))
    ///
    (defthm wirelist-nodups-p-implies-wirelist-p
      (implies (wirelist-nodups-p x)
               (wirelist-p x)))

    (local (in-theory (enable acl2::no-duplicates-of-append)))

    (defthm wirelist-nodups-p-of-append
      (implies (and (wirelist-nodups-p a)
                    (wirelist-nodups-p b)
                    (not (intersection$ (wirelist->names a)
                                        (wirelist->names b))))
               (wirelist-nodups-p (append a b))))

    (defthm wirelist-nodups-p-of-cons
      (equal (wirelist-nodups-p (cons a b))
             (and (wire-p a)
                  (wirelist-nodups-p b)
                  (not (member (wire->name a)
                               (wirelist->names b)))))
      :hints(("Goal" :in-theory (enable wirelist->names)))))

  (define wirelist-rem-dups ((x wirelist-p))
    :verify-guards nil
    :returns (xx wirelist-nodups-p
                 :hints(("Goal" :in-theory (enable wirelist-nodups-p
                                                   wirelist->names))))
    (if (atom x)
        nil
      (cons (wire-fix (car x))
            (wirelist-remove-name (wire->name (car x))
                                  (wirelist-rem-dups (cdr x)))))
    ///
    (verify-guards wirelist-rem-dups)

    (defthm wirelist->names-of-remove-duplicate-names
      (equal (wirelist->names (wirelist-rem-dups x))
             (acl2::remove-later-duplicates (wirelist->names x)))
      :hints(("Goal" :in-theory (enable wirelist->names
                                        acl2::remove-later-duplicates)
              :induct t)
             (and stable-under-simplificationp
                  '(:expand ((:free (a b) (acl2::remove-later-duplicates (cons a b))))))))

    (defthm wirelist-rem-dups-when-no-duplicates
      (implies (no-duplicatesp (wirelist->names x))
               (equal (wirelist-rem-dups x)
                      (wirelist-fix x)))
      :hints(("Goal" :in-theory (enable wirelist->names
                                        wirelist-fix))))

    (defthm wirelist-rem-dups-when-wirelist-nodups-p
      (implies (wirelist-nodups-p x)
               (equal (wirelist-rem-dups x)
                      x))
      :hints(("Goal" :in-theory (enable wirelist-nodups-p))))

    (defthm no-duplicate-names-of-wirelist-rem-dups
      (no-duplicatesp (wirelist->names (wirelist-rem-dups x)))
      :hints(("Goal" :in-theory (enable wirelist->names
                                        wirelist-fix))))

    (deffixequiv wirelist-rem-dups
      :hints(("Goal" :in-theory (enable wirelist-fix))))

    (deffixtype wirelist-nodups
      :pred wirelist-nodups-p :fix wirelist-rem-dups
      :equiv wirelist-nodups-equiv :define t :forward t)

    (local (defthm wirelist-remove-name-of-equal-to-append
             (implies (equal a (append b c))
                      (equal (wirelist-remove-name d a)
                             (append (wirelist-remove-name d b)
                                     (wirelist-remove-name d c))))
             :hints(("Goal" :in-theory (enable wirelist-remove-name)))))

    (defthm wirelist-rem-dups-of-append
      (equal (wirelist-rem-dups (append a b))
             (append (wirelist-rem-dups a)
                     (wirelist-remove-names
                      (wirelist->names a)
                      (wirelist-rem-dups b))))
      :hints(("Goal" :in-theory (enable wirelist->names
                                        wirelist-remove-names)))))

  (define elab-mod$c-wires-ok (elab-mod$c)
    (and (<= (nfix (elab-mod$c->nwires elab-mod$c))
             (elab-mod$c->wiretable-length elab-mod$c))
         (ec-call (elab-mod$c-wire-indices-ok elab-mod$c))
         (ec-call (elab-mod$c-wire-names-ok elab-mod$c)))
    ///
    (defthm elab-mod$c-wires-ok-when-empty
      (implies (and (nat-equiv (nth *elab-mod$c->nwires* elab-mod$c) 0)
                    (not (consp (nth *elab-mod$c->wirename-idxes-get* elab-mod$c))))
               (elab-mod$c-wires-ok elab-mod$c))
      :hints(("Goal" :in-theory (enable elab-mod$c-wire-indices-ok
                                        elab-mod$c-wire-names-ok))))

    (defthm elab-mod$c-wires-ok-implies-lookup-name
      (let ((look (hons-assoc-equal k (nth *elab-mod$c->wirename-idxes-get* elab-mod$c)))
            (idx (index-of k (wirelist->names (nth *elab-mod$c->wiretablei* elab-mod$c)))))
        (implies (elab-mod$c-wires-ok elab-mod$c)
                 (equal look
                        (and idx
                             (< idx (nfix (nth *elab-mod$c->nwires* elab-mod$c)))
                             (cons k idx)))))
      :hints (("goal" :use ((:instance elab-mod$c-wire-names-ok-necc
                             (name k))
                            (:instance elab-mod$c-wire-indices-ok-necc
                             (idx (index-of k (wirelist->names
                                               (nth *elab-mod$c->wiretablei*
                                                    elab-mod$c))))))
               :in-theory (disable elab-mod$c-wire-indices-ok-necc
                                   elab-mod$c-wire-names-ok-necc))))

    (defthm elab-mod$c-indices-ok-in-terms-of-index-of
      (implies (and (elab-mod$c-wires-ok elab-mod$c)
                    (< (nfix idx) (nfix (nth *elab-mod$c->nwires* elab-mod$c))))
               (let ((idxes->wires (nth *elab-mod$c->wiretablei* elab-mod$c)))
                 (equal (index-of (wire->name (nth idx idxes->wires))
                                  (wirelist->names idxes->wires))
                        (nfix idx))))
      :hints (("goal" :use ((:instance elab-mod$c-wire-indices-ok-necc
                             (idx (nfix idx))))
               :in-theory (disable elab-mod$c-wire-indices-ok-necc))))

    (defthm elab-mod$c-wires-ok-linear
      (implies (elab-mod$c-wires-ok elab-mod$c)
               (and (<= (nfix (nth *elab-mod$c->nwires* elab-mod$c))
                        (len (nth *elab-mod$c->wiretablei* elab-mod$c)))
                    (implies (natp (nth *elab-mod$c->nwires* elab-mod$c))
                             (<= (nth *elab-mod$c->nwires* elab-mod$c)
                                 (len (nth *elab-mod$c->wiretablei* elab-mod$c))))))
      :rule-classes :linear)

    (defthmd elab-mod$c-wires-ok-implies-no-duplicated-names
      (implies (and (elab-mod$c-wires-ok elab-mod$c)
                    (< (nfix n) (nfix (nth *elab-mod$c->nwires* elab-mod$c)))
                    (< (nfix m) (nfix (nth *elab-mod$c->nwires* elab-mod$c))))
               (equal (equal (wire->name (nth n (nth *elab-mod$c->wiretablei* elab-mod$c)))
                             (wire->name (nth m (nth *elab-mod$c->wiretablei* elab-mod$c))))
                      (nat-equiv n m)))
      :hints (("goal" :use ((:instance elab-mod$c-wire-indices-ok-necc
                             (idx (nfix n)))
                            (:instance elab-mod$c-wire-indices-ok-necc
                             (idx (nfix m))))
               :in-theory (e/d* (acl2::arith-equiv-forwarding)
                                (elab-mod$c-wire-indices-ok-necc
                                 ELAB-MOD$C-INDICES-OK-IN-TERMS-OF-INDEX-OF
                                 ELAB-MOD$C-WIRES-OK-IMPLIES-LOOKUP-NAME))))))

  (define elab-mod$c-wire-abstraction (elabmod)
    :verify-guards nil
    :returns (wires wirelist-p)
    (wirelist-fix
     (take (nth *elab-mod$c->nwires* elabmod)
           (nth *elab-mod$c->wiretablei* elabmod)))
    ///


    (local (defthm member-take
             (implies (<= (nfix n) (len x))
                      (iff (member k (take n x))
                           (and (member k x)
                                (< (index-of k x)
                                   (nfix n)))))
             :hints(("Goal" :in-theory (enable index-of take)))))

    (local (defthm member-when-nth
             (implies (and (equal k (nth n x))
                           (< (nfix n) (len x)))
                      (member k x))))


    (defthmd member-of-abstraction-when-wires-ok
      (implies (and (elab-mod$c-wires-ok elab-mod$c)
                    (name-p x))
               (iff (hons-assoc-equal x (nth *elab-mod$c->wirename-idxes-get* elab-mod$c))
                    (member x (wirelist->names (elab-mod$c-wire-abstraction elab-mod$c)))))
      :hints (("goal" :do-not-induct t
               :in-theory (e/d (elab-mod$c-wires-ok)
                               (elab-mod$c-wire-names-ok-necc
                                elab-mod$c-wire-indices-ok-necc))
               :use ((:instance elab-mod$c-wire-names-ok-necc
                      (name x))
                     (:instance elab-mod$c-wire-indices-ok-necc
                      (idx (index-of x (wirelist->names (nth *elab-mod$c->wiretablei* elab-mod$c))))))))
      :otf-flg t)

    (defthm no-duplicatesp-of-abstraction-when-wires-ok
      (implies (elab-mod$c-wires-ok elab-mod$c)
               (no-duplicatesp (wirelist->names (elab-mod$c-wire-abstraction elab-mod$c))))
      :hints (("goal" :use ((:instance acl2::no-duplicatesp-by-indices-of-dup-witness
                             (x (wirelist->names
                                 (elab-mod$c-wire-abstraction elab-mod$c)))))
               :in-theory (enable elab-mod$c-wires-ok-implies-no-duplicated-names)))
      :otf-flg t)

    (defthm wirelist-nodups-p-of-abstraction-when-wires-ok
      (implies (elab-mod$c-wires-ok elab-mod$c)
               (wirelist-nodups-p (elab-mod$c-wire-abstraction elab-mod$c)))
      :hints(("Goal" :in-theory (e/d (wirelist-nodups-p)
                                     (elab-mod$c-wire-abstraction)))))))


(define elab-mod$c-add-wire ((wire wire-p) elab-mod$c)
  :guard (elab-mod$c-wires-ok elab-mod$c)
  :guard-hints (("goal" :in-theory (enable elab-mod$c-wires-ok)))
  (b* ((idx (lnfix (elab-mod$c->nwires elab-mod$c)))
       (wire (wire-fix wire))
       (name (wire->name wire))
       ((when (elab-mod$c->wirename-idxes-boundp name elab-mod$c))
        (cw "In ~x2: Wire already exists in ~s0: ~x1~%"
            (elab-mod$c->name elab-mod$c) name __function__)
        elab-mod$c)
       (elab-mod$c (if (<= (elab-mod$c->wiretable-length elab-mod$c) idx)
                     (resize-elab-mod$c->wiretable (max 16 (* 2 idx)) elab-mod$c)
                   elab-mod$c))
       (elab-mod$c (update-elab-mod$c->nwires (1+ idx) elab-mod$c))
       (elab-mod$c (update-elab-mod$c->wiretablei idx wire elab-mod$c)))
    (elab-mod$c->wirename-idxes-put name idx elab-mod$c))
  ///

  (defthm elab-mod$c-wires-ok-of-elab-mod$c-add-wire
    (implies (elab-mod$c-wires-ok elab-mod$c)
             (elab-mod$c-wires-ok (elab-mod$c-add-wire wire elab-mod$c)))
    :hints(("Goal" :in-theory (enable elab-mod$c-wires-ok))
           (and stable-under-simplificationp
                `(:computed-hint-replacement
                  ('(:clause-processor
                     (acl2::generalize-termlist-cp
                      clause (list (append (acl2::find-calls-lst
                                            'elab-mod$c-wire-indices-ok-witness clause)
                                           (acl2::find-calls-lst
                                            'elab-mod$c-wire-names-ok-witness clause))
                                   'w))))
                  :expand (,(car (last clause))))))
    :otf-flg t)

  (local (in-theory (disable acl2::take)))

  (defthm wirelist-fix-of-update-nth
    (implies (<= (nfix n) (len x))
             (equal (wirelist-fix (update-nth n v x))
                    (update-nth n (wire-fix v) (wirelist-fix x))))
    :hints(("Goal" :in-theory (enable wirelist-fix update-nth))))

  (defthm wirelist-fix-of-take
    (implies (<= (nfix n) (len x))
             (equal (wirelist-fix (take n x))
                    (take n (wirelist-fix x))))
    :hints(("Goal" :in-theory (enable wirelist-fix take))))

  (local (defthm member-take
           (implies (<= (nfix n) (len x))
                    (iff (member k (take n x))
                         (and (member k x)
                              (< (index-of k x)
                                 (nfix n)))))
           :hints(("Goal" :in-theory (enable index-of take)))))

  (defthm elab-mod$c-add-wire-update
    (implies (elab-mod$c-wires-ok elab-mod$c)
             (equal (elab-mod$c-wire-abstraction (elab-mod$c-add-wire wire elab-mod$c))
                    (let ((orig-wires (elab-mod$c-wire-abstraction elab-mod$c)))
                      (if (member (wire->name wire) (wirelist->names orig-wires))
                          orig-wires
                        (append orig-wires (list (wire-fix wire)))))))
    :hints(("Goal" :do-not-induct t
            :in-theory (e/d (member-of-abstraction-when-wires-ok)))
           (and stable-under-simplificationp
                '(:in-theory (enable elab-mod$c-wire-abstraction)))
           (and stable-under-simplificationp
                (acl2::equal-by-nths-hint)))
    :otf-flg t)

  (local (defthm wireidx-namesp-of-replicate
           (implies (wire-p d)
                    (elab-mod$c->wiretablep (replicate n d)))
           :hints(("Goal" :in-theory (enable replicate)))))

  (local (defthm wireidx-namesp-of-resize-list
           (implies (and (wire-p d)
                         (elab-mod$c->wiretablep x))
                    (elab-mod$c->wiretablep (resize-list x n d)))))

  (local (defthm wireidx-namesp-of-update-nth
           (implies (and (wire-p v)
                         (elab-mod$c->wiretablep x)
                         (<= (nfix n) (len x)))
                    (elab-mod$c->wiretablep
                     (update-nth n v x)))
           :hints(("Goal" :in-theory (enable update-nth)))))

  (defthm elab-mod$cp-of-add-wire
    (implies (elab-mod$cp elab-mod$c)
             (elab-mod$cp (elab-mod$c-add-wire name elab-mod$c))))

  (defthm elab-mod$cp-add-wire-frame
    (implies (and (not (equal n *elab-mod$c->nwires*))
                  (not (equal n *elab-mod$c->wiretablei*))
                  (not (equal n *elab-mod$c->wirename-idxes-get*)))
             (equal (nth n (elab-mod$c-add-wire wire elab-mod$c))
                    (nth n elab-mod$c))))

  (defthm elab-mod$cp-add-wire-irrel
    (implies (and (not (equal n *elab-mod$c->nwires*))
                  (not (equal n *elab-mod$c->wiretablei*))
                  (not (equal n *elab-mod$c->wirename-idxes-get*)))
             (equal (elab-mod$c-add-wire wire (update-nth n v elab-mod$c))
                    (update-nth n v (elab-mod$c-add-wire wire elab-mod$c))))))






(defsection elab-mod$c-insts-ok

  (defun-sk elab-mod$c-inst-indices-ok (elab-mod$c)
    (forall idx
            (let ((names->idxes (nth *elab-mod$c->modinstname-idxes-get* elab-mod$c))
                  (idxes->insts (nth *elab-mod$c->modinsttablei* elab-mod$c)))
              (implies (and (natp idx)
                            (< idx (nfix (nth *elab-mod$c->ninsts* elab-mod$c))))
                       (let* ((modinst (nth idx idxes->insts))
                              (name (nth *elab-modinst$c->instname* modinst)))
                         (and (name-p name)
                              (hons-assoc-equal name names->idxes)
                              (equal (cdr (hons-assoc-equal name names->idxes))
                                     idx))))))
    :rewrite :direct)

  (in-theory (disable elab-mod$c-inst-indices-ok))

  (defun-sk elab-mod$c-inst-names-ok (elab-mod$c)
    (forall name
            (let* ((names->idxes (nth *elab-mod$c->modinstname-idxes-get* elab-mod$c))
                   (idxes->insts (nth *elab-mod$c->modinsttablei* elab-mod$c)))
              (implies (hons-assoc-equal name names->idxes)
                       (let ((idx (cdr (hons-assoc-equal name names->idxes))))
                         (and (natp idx)
                              (< idx (nfix (nth *elab-mod$c->ninsts* elab-mod$c)))
                              (equal (nth *elab-modinst$c->instname* (nth idx idxes->insts))
                                     name))))))
    :rewrite :direct)

  (defthm elab-mod$c-inst-names-ok-linear
    (implies (and (elab-mod$c-inst-names-ok elab-mod$c)
                  (hons-assoc-equal name (nth *elab-mod$c->modinstname-idxes-get* elab-mod$c)))
             (< (cdr (hons-assoc-equal name (nth *elab-mod$c->modinstname-idxes-get* elab-mod$c)))
                (nfix (nth *elab-mod$c->ninsts* elab-mod$c))))
    :rule-classes :linear)

  (in-theory (disable elab-mod$c-inst-names-ok))

  (define elab-mod$c-modinsts-ok (elab-mod$c)
    (and (<= (nfix (elab-mod$c->ninsts elab-mod$c))
             (elab-mod$c->modinsttable-length elab-mod$c))
         (ec-call (elab-mod$c-inst-indices-ok elab-mod$c))
         (ec-call (elab-mod$c-inst-names-ok elab-mod$c)))
    ///
    (defthm elab-mod$c-modinsts-ok-when-empty
      (implies (and (nat-equiv (nth *elab-mod$c->ninsts* elab-mod$c) 0)
                    (not (consp (nth *elab-mod$c->modinstname-idxes-get* elab-mod$c))))
               (elab-mod$c-modinsts-ok elab-mod$c))
      :hints(("Goal" :in-theory (enable elab-mod$c-inst-indices-ok
                                        elab-mod$c-inst-names-ok))))

    (local (defthm member-when-nth
             (implies (and (equal k (nth n x))
                           (< (nfix n) (len x)))
                      (member k x))))

    (local (defthm index-of-when-nth-of-elab-modinst-list-names
             (implies (and (equal k (nth *elab-modinst$c->instname* (nth n x)))
                           (name-p k)
                           (< (nfix n) (len x)))
                      (<= (index-of
                           k (elab-modinst-list-names x)) (nfix n)))
             :hints(("Goal" :in-theory (enable elab-modinst-list-names
                                               index-of nth)))
             :rule-classes :linear))


    (defthmd elab-mod$c-modinsts-ok-implies-lookup-name
      (let ((look (hons-assoc-equal k (nth *elab-mod$c->modinstname-idxes-get* elab-mod$c)))
            (idx (index-of k (elab-modinst-list-names
                              (nth *elab-mod$c->modinsttablei* elab-mod$c)))))
        (implies (and (elab-mod$c-modinsts-ok elab-mod$c)
                      (name-p k))
                 (equal look
                        (and idx
                             (< idx (nfix (nth *elab-mod$c->ninsts* elab-mod$c)))
                             (cons k idx)))))
      :hints (("goal" :use ((:instance elab-mod$c-inst-names-ok-necc
                             (name k))
                            (:instance elab-mod$c-inst-indices-ok-necc
                             (idx (index-of k (elab-modinst-list-names
                                               (nth *elab-mod$c->modinsttablei*
                                                    elab-mod$c))))))
               :in-theory (disable elab-mod$c-inst-indices-ok-necc
                                   elab-mod$c-inst-names-ok-necc))))

    (defthm elab-mod$c-inst-indices-ok-in-terms-of-index-of
      (implies (and (elab-mod$c-modinsts-ok elab-mod$c)
                    (< (nfix idx) (nfix (nth *elab-mod$c->ninsts* elab-mod$c))))
               (let ((idxes->insts (nth *elab-mod$c->modinsttablei* elab-mod$c)))
                 (equal (index-of (nth *elab-modinst$c->instname* (nth idx idxes->insts))
                                  (elab-modinst-list-names idxes->insts))
                        (nfix idx))))
      :hints (("goal" :use ((:instance elab-mod$c-inst-indices-ok-necc
                             (idx (nfix idx))))
               :in-theory (e/d (elab-mod$c-modinsts-ok-implies-lookup-name)
                               (elab-mod$c-inst-indices-ok-necc)))))

    (defthm elab-mod$c-modinsts-ok-linear
      (implies (elab-mod$c-modinsts-ok elab-mod$c)
               (and (<= (nfix (nth *elab-mod$c->ninsts* elab-mod$c))
                        (len (nth *elab-mod$c->modinsttablei* elab-mod$c)))
                    (implies (natp (nth *elab-mod$c->ninsts* elab-mod$c))
                             (<= (nth *elab-mod$c->ninsts* elab-mod$c)
                                 (len (nth *elab-mod$c->modinsttablei* elab-mod$c))))))
      :rule-classes :linear)

    (defthmd elab-mod$c-insts-ok-implies-no-duplicated-names
      (implies (and (elab-mod$c-modinsts-ok elab-mod$c)
                    (< (nfix n) (nfix (nth *elab-mod$c->ninsts* elab-mod$c)))
                    (< (nfix m) (nfix (nth *elab-mod$c->ninsts* elab-mod$c))))
               (and (equal (equal (name-fix
                                   (nth *elab-modinst$c->instname*
                                        (nth n (nth *elab-mod$c->modinsttablei* elab-mod$c))))
                                  (name-fix
                                   (nth *elab-modinst$c->instname*
                                        (nth m (nth *elab-mod$c->modinsttablei* elab-mod$c)))))
                           (nat-equiv n m))
                    (equal (equal (nth n (nth *elab-mod$c->modinsttablei* elab-mod$c))
                                  (nth m (nth *elab-mod$c->modinsttablei* elab-mod$c)))
                           (nat-equiv n m))))
      :hints (("goal" :use ((:instance elab-mod$c-inst-indices-ok-necc
                             (idx (nfix n)))
                            (:instance elab-mod$c-inst-indices-ok-necc
                             (idx (nfix m))))
               :in-theory (e/d* (acl2::arith-equiv-forwarding)
                                (elab-mod$c-inst-indices-ok-necc
                                 ELAB-MOD$C-INDICES-OK-IN-TERMS-OF-INDEX-OF
                                 ELAB-MOD$C-modINSTS-OK-IMPLIES-LOOKUP-NAME))))))

  (define elab-mod$c-inst-abstraction (elab-mod$c)
    :verify-guards nil
    :non-executable t
    :returns (insts elab-modinst-list-p)
    (elab-modinst-list-fix
     (take (nth *elab-mod$c->ninsts* elab-mod$c)
           (nth *elab-mod$c->modinsttablei* elab-mod$c)))
    ///

    (local (defthm member-take
             (implies (<= (nfix n) (len x))
                      (iff (member k (take n x))
                           (and (member k x)
                                (< (index-of k x)
                                   (nfix n)))))
             :hints(("Goal" :in-theory (enable index-of take)))))

    (local (defthm member-when-nth
             (implies (and (equal k (nth n x))
                           (< (nfix n) (len x)))
                      (member k x))))

    (local (defthm index-of-when-nth-of-elab-modinst-list-names
             (implies (and (equal k (nth *elab-modinst$c->instname* (nth n x)))
                           (name-p k)
                           (< (nfix n) (len x)))
                      (<= (index-of
                           k (elab-modinst-list-names x)) (nfix n)))
             :hints(("Goal" :in-theory (enable elab-modinst-list-names
                                               index-of nth)))
             :rule-classes :linear))

    (defthmd member-of-abstraction-when-modinsts-ok
      (implies (and (elab-mod$c-modinsts-ok elab-mod$c)
                    (name-p x))
               (iff (hons-assoc-equal x (nth *elab-mod$c->modinstname-idxes-get* elab-mod$c))
                    (member x (elab-modinst-list-names
                               (elab-mod$c-inst-abstraction elab-mod$c)))))
      :hints (("goal" :do-not-induct t
               :in-theory (e/d (elab-mod$c-modinsts-ok)
                               (elab-mod$c-inst-names-ok-necc
                                elab-mod$c-inst-indices-ok-necc))
               :use ((:instance elab-mod$c-inst-names-ok-necc
                      (name x))
                     (:instance elab-mod$c-inst-indices-ok-necc
                      (idx (index-of x
                                     (elab-modinst-list-names
                                      (nth *elab-mod$c->modinsttablei* elab-mod$c))))))))
      :otf-flg t)

    (defthm no-duplicatesp-of-abstraction-when-modinsts-ok
      (implies (elab-mod$c-modinsts-ok elab-mod$c)
               (no-duplicatesp (elab-modinst-list-names
                                (elab-mod$c-inst-abstraction elab-mod$c))))
      :hints (("goal" :use ((:instance acl2::no-duplicatesp-by-indices-of-dup-witness
                             (x (elab-modinst-list-names
                                 (elab-mod$c-inst-abstraction elab-mod$c)))))
               :in-theory (enable elab-mod$c-insts-ok-implies-no-duplicated-names)))
      :otf-flg t)

    (defthm elab-modinsts-nodups-p-of-abstraction-when-modinsts-ok
      (implies (elab-mod$c-modinsts-ok elab-mod$c)
               (elab-modinsts-nodups-p (elab-mod$c-inst-abstraction elab-mod$c)))
      :hints(("Goal" :in-theory (e/d (elab-modinsts-nodups-p)
                                     (elab-mod$c-inst-abstraction)))))))

(define elab-mod$c-add-inst (elab-modinst$c elab-mod$c)
  :prepwork ((local (defthm true-listp-of-modinsttable-lookup
                      (implies (ELAB-MOD$C->MODINSTTABLEP x)
                               (and (true-listp (nth n x))
                                    (implies (< (nfix n) (len x))
                                             (equal (len (nth n x)) 4))))
                      :hints(("Goal" :in-theory (enable elab-mod$c->modinsttablep
                                                        nth))))))
  :guard (elab-mod$c-modinsts-ok elab-mod$c)
  :guard-hints (("goal" :in-theory (enable elab-mod$c-modinsts-ok)))
  (b* ((idx (lnfix (elab-mod$c->ninsts elab-mod$c)))
       (iname (elab-modinst$c->instname elab-modinst$c))
       (iname (mbe :logic (name-fix iname) :exec iname))
       ((when (elab-mod$c->modinstname-idxes-boundp iname elab-mod$c))
        (raise "Inst already exists in ~s0: ~x1"
               (elab-mod$c->name elab-mod$c) iname)
        elab-mod$c)
       (elab-mod$c (if (<= (elab-mod$c->modinsttable-length elab-mod$c) idx)
                     (resize-elab-mod$c->modinsttable (max 16 (* 2 idx)) elab-mod$c)
                   elab-mod$c))
       (elab-mod$c (update-elab-mod$c->ninsts (1+ idx) elab-mod$c))
       (elab-mod$c (elab-mod$c->modinstname-idxes-put iname idx elab-mod$c)))
    (stobj-let ((elab-modinst$c2 (elab-mod$c->modinsttablei idx elab-mod$c)))
               (elab-modinst$c2)
               (elab-modinst$c-copy elab-modinst$c elab-modinst$c2)
               elab-mod$c))
  ///
  (local (in-theory (disable acl2::take
                             elab-mod$c-modinsts-ok-implies-lookup-name)))

  (defthm elab-mod$c-modinsts-ok-of-elab-mod$c-add-inst
    (implies (elab-mod$c-modinsts-ok elab-mod$c)
             (elab-mod$c-modinsts-ok (elab-mod$c-add-inst inst elab-mod$c)))
    :hints(("Goal" :in-theory (e/d* (elab-mod$c-modinsts-ok
                                     acl2::arith-equiv-forwarding)
                                    (acl2::nth-when-too-large-cheap)))
           (and stable-under-simplificationp
                `(:computed-hint-replacement
                  ('(:clause-processor
                     (acl2::generalize-termlist-cp
                      clause (list (append (acl2::find-calls-lst
                                            'elab-mod$c-inst-indices-ok-witness clause)
                                           (acl2::find-calls-lst
                                            'elab-mod$c-inst-names-ok-witness clause))
                                   'w))))
                  :expand (,(car (last clause))))))
    :otf-flg t)

  (defthm elab-mod$c-add-inst-update
    (implies (elab-mod$c-modinsts-ok elab-mod$c)
             (equal (elab-mod$c-inst-abstraction (elab-mod$c-add-inst inst elab-mod$c))
                    (let ((orig-insts (elab-mod$c-inst-abstraction elab-mod$c)))
                      (if (member (name-fix (nth *elab-modinst$c->instname* inst))
                                  (elab-modinst-list-names orig-insts))
                          orig-insts
                        (append orig-insts (list (elab-modinst$c-fix inst)))))))
    :hints(("Goal" :do-not-induct t
            :in-theory (e/d* (acl2::arith-equiv-forwarding
                              member-of-abstraction-when-modinsts-ok)))
           (and stable-under-simplificationp
                '(:in-theory (enable elab-mod$c-inst-abstraction)))
           (and stable-under-simplificationp
                (acl2::equal-by-nths-hint)))
    :otf-flg t)

  (local (defthm modinsttablep-of-replicate
           (implies (elab-modinst$cp d)
                    (elab-mod$c->modinsttablep (replicate n d)))
           :hints(("Goal" :in-theory (enable replicate)))))

  (local (defthm modinsttablep-of-resize-list
           (implies (and (elab-modinst$cp d)
                         (elab-mod$c->modinsttablep x))
                    (elab-mod$c->modinsttablep (resize-list x n d)))))

  (local (defthm modinsttablep-of-update-nth
           (implies (and (elab-modinst$cp v)
                         (elab-mod$c->modinsttablep x)
                         (<= (nfix n) (len x)))
                    (elab-mod$c->modinsttablep
                     (update-nth n v x)))
           :hints(("Goal" :in-theory (enable update-nth)))))

  (defthm elab-mod$cp-of-add-inst
    (implies (elab-mod$cp elab-mod$c)
             (elab-mod$cp (elab-mod$c-add-inst name elab-mod$c))))


  (defthm elab-mod$cp-add-inst-frame
    (implies (and (not (equal n *elab-mod$c->ninsts*))
                  (not (equal n *elab-mod$c->modinsttablei*))
                  (not (equal n *elab-mod$c->modinstname-idxes-get*)))
             (equal (nth n (elab-mod$c-add-inst inst elab-mod$c))
                    (nth n elab-mod$c))))

  (defthm elab-mod$cp-add-inst-irrel
    (implies (and (not (equal n *elab-mod$c->ninsts*))
                  (not (equal n *elab-mod$c->modinsttablei*))
                  (not (equal n *elab-mod$c->modinstname-idxes-get*)))
             (equal (elab-mod$c-add-inst inst (update-nth n v elab-mod$c))
                    (update-nth n v (elab-mod$c-add-inst inst elab-mod$c))))))


(defsection elab-mod-accessor-defs

  (local (defthm namelist-p-implies-true-listp
           (implies (namelist-p x)
                    (true-listp x))))
  (local (defthm elab-modinst-list-p-implies-true-listp
           (implies (elab-modinst-list-p x)
                    (true-listp x))))

  (define elab-mod$ap (elab-mod$a)
    (b* ((name (g :name elab-mod$a))
         (totalwires (g :totalwires elab-mod$a))
         (totalinsts (g :totalinsts elab-mod$a))
         (orig-mod (g :orig-mod elab-mod$a))
         (wires (g :wires elab-mod$a))
         (insts (g :insts elab-mod$a)))
      (and (modname-p name)
           (natp totalwires)
           (natp totalinsts)
           (module-p orig-mod)
           (wirelist-nodups-p wires)
           (elab-modinsts-nodups-p insts)
           (equal elab-mod$a
                  (s :name name
                     (s :totalwires totalwires
                        (s :totalinsts totalinsts
                           (s :orig-mod orig-mod
                              (s :wires wires
                                 (s :insts insts nil))))))))))

  (define elab-mod$a-fix ((elab-mod$a elab-mod$ap))
    :hooks nil
    :prepwork ((local (in-theory (e/d (elab-mod$ap)
                                      (module-fix-when-module)))))
    :returns (em elab-mod$ap)
    (mbe :logic (s :name (modname-fix (g :name elab-mod$a))
                   (s :totalwires (nfix (g :totalwires elab-mod$a))
                      (s :totalinsts (nfix (g :totalinsts elab-mod$a))
                         (s :orig-mod (module-fix (g :orig-mod elab-mod$a))
                            (s :wires (wirelist-rem-dups (g :wires elab-mod$a))
                               (s :insts (elab-modinsts-rem-dups (g :insts elab-mod$a))
                                  nil))))))
         :exec elab-mod$a)
    ///
    (defthm elab-mod$a-fix-when-elab-mod$ap
      (implies (elab-mod$ap x)
               (equal (elab-mod$a-fix x) x)))

    (deffixtype elab-mod :pred elab-mod$ap :fix elab-mod$a-fix :equiv elab-mod$a-equiv
      :define t :forward t)

    (fty::deffixcong elab-mod$a-equiv elab-mod$a-equiv (s k v x) x
      :hints(("Goal" :in-theory (enable elab-mod$a-fix
                                        acl2::g-of-s-redux))))

    (defthm g-of-elab-mod$a-fix
      (and (equal (g :name (elab-mod$a-fix x)) (modname-fix (g :name x)))
           (equal (g :totalinsts (elab-mod$a-fix x)) (nfix (g :totalinsts x)))
           (equal (g :totalwires (elab-mod$a-fix x)) (nfix (g :totalwires x)))
           (equal (g :orig-mod (elab-mod$a-fix x)) (module-fix (g :orig-mod x)))))

    (defthm g-of-elab-mod$a-fix-wires
      (equal (g :wires (elab-mod$a-fix x))
             (wirelist-rem-dups (g :wires x))))

    (defthm g-of-elab-mod$a-fix-insts
      (equal (g :insts (elab-mod$a-fix x))
             (elab-modinsts-rem-dups
              (g :insts x)))))

  (local (set-default-hints
          '((and stable-under-simplificationp
                 '(:in-theory (enable elab-mod$ap)))
            (and stable-under-simplificationp
                 '(:in-theory (enable elab-mod$a-fix))))))

  (define elab-mod$a-nwires ((elab-mod$a elab-mod$ap))
    (len (g :wires (elab-mod$a-fix elab-mod$a)))
    ///
    (deffixequiv elab-mod$a-nwires))

  (local (defthm nth-of-wirelist
           (implies (and (wirelist-p x)
                         (< (nfix n) (len x)))
                    (wire-p (nth n x)))
           :hints(("Goal" :in-theory (enable wirelist-p nth)
                   :induct (nth n x)))))

  (define elab-mod$a-wiretablei ((idx natp) (elab-mod$a elab-mod$ap))
    :prepwork ((local (in-theory (enable elab-mod$a-nwires))))
    :guard (< idx (elab-mod$a-nwires elab-mod$a))
    :returns (wire wire-p)
    (wire-fix (nth idx (g :wires (elab-mod$a-fix elab-mod$a))))
    ///
    (deffixequiv elab-mod$a-wiretablei))

  (define elab-mod$a-wirename->idx ((name name-p) (elab-mod$a elab-mod$ap))
    (index-of (name-fix name)
              (wirelist->names (g :wires (elab-mod$a-fix elab-mod$a))))
    ///
    (deffixequiv elab-mod$a-wirename->idx))

  (local (defthm intersection-of-single
           (iff (intersection-equal x (list y))
                (member y x))))

  (define elab-mod$a-add-wire ((wire wire-p) (elab-mod$a elab-mod$ap))
    :returns (elab-mod$a2 elab-mod$ap)
    (let* ((wire (wire-fix wire))
           (elab-mod$a (elab-mod$a-fix elab-mod$a))
           (wires (g :wires elab-mod$a)))
      (s :wires
         (if (member-equal (wire->name wire) (wirelist->names wires))
             wires
           (append wires (list wire)))
         elab-mod$a))
    ///
    (deffixequiv elab-mod$a-add-wire))

  (define elab-mod$a-ninsts ((elab-mod$a elab-mod$ap))
    (len (g :insts (elab-mod$a-fix elab-mod$a)))
    ///
    (deffixequiv elab-mod$a-ninsts))

  ;; (local (defthm elab-modinst$cp-of-nth-of-elab-modinst-list
  ;;          (implies (and (elab-modinst-list-p x)
  ;;                        (< (nfix n) (len x)))
  ;;                   (elab-modinst$cp (nth n x)))
  ;;          :hints(("Goal" :in-theory (enable nth elab-modinst-list-p)))))

  (define elab-mod$a->instname ((idx natp) (elab-mod$a elab-mod$ap))
    :prepwork ((local (in-theory (enable elab-mod$a-ninsts))))
    :guard-hints (("goal" :use ((:instance elab-modinst$cp-of-nth-when-elab-modinst-list-p
                                 (x (g :insts (elab-mod$a-fix elab-mod$a)))
                                 (acl2::n idx)))
                   :in-theory (disable elab-modinst$cp-of-nth-when-elab-modinst-list-p)))
    :guard (< idx (elab-mod$a-ninsts elab-mod$a))
    :returns (name name-p)
    (name-fix (nth *elab-modinst$c->instname*
                           (nth idx (g :insts (elab-mod$a-fix elab-mod$a)))))
    ///
    (deffixequiv elab-mod$a->instname))

  (define elab-mod$c->instname ((idx natp) elab-mod$c)
    :guard (and (elab-mod$c-modinsts-ok elab-mod$c)
                (< idx (elab-mod$c->ninsts elab-mod$c)))
    :prepwork ((local (defthm name-p-of-instname-of-elab-modinst
                        (implies (and (elab-mod$c->modinsttablep x)
                                      (< (nfix idx) (len x)))
                                 (name-p (nth *elab-modinst$c->instname*
                                               (nth idx x))))
                        :hints(("Goal" :in-theory (enable (:i nth))
                                :induct (nth idx x)
                                :expand ((nth idx x)))))))
    (stobj-let ((elab-modinst$c (elab-mod$c->modinsttablei idx elab-mod$c)))
               (res)
               (mbe :logic (name-fix (elab-modinst$c->instname elab-modinst$c))
                    :exec (elab-modinst$c->instname elab-modinst$c))
               res)
    ///
    (defthm elab-mod$c->instname-in-terms-of-abstraction
      (implies (< (nfix idx) (nfix (nth *elab-mod$c->ninsts* elab-mod$c)))
               (equal (elab-mod$c->instname idx elab-mod$c)
                      (name-fix
                       (nth *elab-modinst$c->instname*
                            (nth idx (elab-mod$c-inst-abstraction elab-mod$c))))))
      :hints(("Goal" :in-theory (enable elab-mod$c-inst-abstraction)))))

  (define elab-mod$a->inst-modidx ((idx natp) (elab-mod$a elab-mod$ap))
    :prepwork ((local (in-theory (enable elab-mod$a-ninsts))))
    :guard-hints (("goal" :use ((:instance elab-modinst$cp-of-nth-when-elab-modinst-list-p
                                 (x (g :insts (elab-mod$a-fix elab-mod$a)))
                                 (acl2::n idx)))
                   :in-theory (disable elab-modinst$cp-of-nth-when-elab-modinst-list-p)))
    :guard (< idx (elab-mod$a-ninsts elab-mod$a))
    (nfix (nth *elab-modinst$c->modidx*
               (nth idx (g :insts (elab-mod$a-fix elab-mod$a)))))
    ///
    (deffixequiv elab-mod$a->inst-modidx))

  (define elab-mod$c->inst-modidx ((idx natp) elab-mod$c)
    :guard (and (elab-mod$c-modinsts-ok elab-mod$c)
                (< idx (elab-mod$c->ninsts elab-mod$c)))
    :prepwork ((local (defthm natp-of-modidx-of-elab-modinst
                        (implies (and (elab-mod$c->modinsttablep x)
                                      (< (nfix idx) (len x)))
                                 (natp (nth *elab-modinst$c->modidx*
                                            (nth idx x))))
                        :hints(("Goal" :in-theory (enable (:i nth))
                                :induct (nth idx x)
                                :expand ((nth idx x)))))))
    (stobj-let ((elab-modinst$c (elab-mod$c->modinsttablei idx elab-mod$c)))
               (res)
               (mbe :logic (nfix (elab-modinst$c->modidx elab-modinst$c))
                    :exec (elab-modinst$c->modidx elab-modinst$c))
               res)
    ///
    (defthm elab-mod$c->inst-modidx-in-terms-of-abstraction
      (implies (< (nfix idx) (nfix (nth *elab-mod$c->ninsts* elab-mod$c)))
               (equal (elab-mod$c->inst-modidx idx elab-mod$c)
                      (nfix (nth *elab-modinst$c->modidx*
                                 (nth idx (elab-mod$c-inst-abstraction elab-mod$c))))))
      :hints(("Goal" :in-theory (enable elab-mod$c-inst-abstraction)))))

  (define elab-mod$a->inst-wireoffset ((idx natp) (elab-mod$a elab-mod$ap))
    :prepwork ((local (in-theory (enable elab-mod$a-ninsts))))
    :guard-hints (("goal" :use ((:instance elab-modinst$cp-of-nth-when-elab-modinst-list-p
                                 (x (g :insts (elab-mod$a-fix elab-mod$a)))
                                 (acl2::n idx)))
                   :in-theory (disable elab-modinst$cp-of-nth-when-elab-modinst-list-p)))
    :guard (< idx (elab-mod$a-ninsts elab-mod$a))
    (nfix (nth *elab-modinst$c->wire-offset*
               (nth idx (g :insts (elab-mod$a-fix elab-mod$a)))))
    ///
    (deffixequiv elab-mod$a->inst-wireoffset))

  (define elab-mod$c->inst-wireoffset ((idx natp) elab-mod$c)
    :guard (and (elab-mod$c-modinsts-ok elab-mod$c)
                (< idx (elab-mod$c->ninsts elab-mod$c)))
    :prepwork ((local (defthm natp-of-wire-offset-of-elab-modinst
                        (implies (and (elab-mod$c->modinsttablep x)
                                      (< (nfix idx) (len x)))
                                 (natp (nth *elab-modinst$c->wire-offset*
                                            (nth idx x))))
                        :hints(("Goal" :in-theory (enable (:i nth))
                                :induct (nth idx x)
                                :expand ((nth idx x)))))))
    (stobj-let ((elab-modinst$c (elab-mod$c->modinsttablei idx elab-mod$c)))
               (res)
               (mbe :logic (nfix (elab-modinst$c->wire-offset elab-modinst$c))
                    :exec (elab-modinst$c->wire-offset elab-modinst$c))
               res)
    ///
    (defthm elab-mod$c->inst-wireoffset-in-terms-of-abstraction
      (implies (< (nfix idx) (nfix (nth *elab-mod$c->ninsts* elab-mod$c)))
               (equal (elab-mod$c->inst-wireoffset idx elab-mod$c)
                      (nfix (nth *elab-modinst$c->wire-offset*
                                 (nth idx (elab-mod$c-inst-abstraction elab-mod$c))))))
      :hints(("Goal" :in-theory (enable elab-mod$c-inst-abstraction)))))

  (define elab-mod$a->inst-instoffset ((idx natp) (elab-mod$a elab-mod$ap))
    :prepwork ((local (in-theory (enable elab-mod$a-ninsts))))
    :guard-hints (("goal" :use ((:instance elab-modinst$cp-of-nth-when-elab-modinst-list-p
                                 (x (g :insts (elab-mod$a-fix elab-mod$a)))
                                 (acl2::n idx)))
                   :in-theory (disable elab-modinst$cp-of-nth-when-elab-modinst-list-p)))
    :guard (< idx (elab-mod$a-ninsts elab-mod$a))
    (nfix (nth *elab-modinst$c->inst-offset*
               (nth idx (g :insts (elab-mod$a-fix elab-mod$a)))))
    ///
    (deffixequiv elab-mod$a->inst-instoffset))

  (define elab-mod$c->inst-instoffset ((idx natp) elab-mod$c)
    :guard (and (elab-mod$c-modinsts-ok elab-mod$c)
                (< idx (elab-mod$c->ninsts elab-mod$c)))
    :prepwork ((local (defthm natp-of-inst-offset-of-elab-modinst
                        (implies (and (elab-mod$c->modinsttablep x)
                                      (< (nfix idx) (len x)))
                                 (natp (nth *elab-modinst$c->inst-offset*
                                            (nth idx x))))
                        :hints(("Goal" :in-theory (enable (:i nth))
                                :induct (nth idx x)
                                :expand ((nth idx x)))))))
    (stobj-let ((elab-modinst$c (elab-mod$c->modinsttablei idx elab-mod$c)))
               (res)
               (mbe :logic (nfix (elab-modinst$c->inst-offset elab-modinst$c))
                    :exec (elab-modinst$c->inst-offset elab-modinst$c))
               res)
    ///
    (defthm elab-mod$c->inst-instoffset-in-terms-of-abstraction
      (implies (< (nfix idx) (nfix (nth *elab-mod$c->ninsts* elab-mod$c)))
               (equal (elab-mod$c->inst-instoffset idx elab-mod$c)
                      (nfix (nth *elab-modinst$c->inst-offset*
                                 (nth idx (elab-mod$c-inst-abstraction elab-mod$c))))))
      :hints(("Goal" :in-theory (enable elab-mod$c-inst-abstraction)))))

  (define elab-mod$a-instname->idx ((name name-p) (elab-mod$a elab-mod$ap))
    (index-of (name-fix name)
              (elab-modinst-list-names
               (g :insts (elab-mod$a-fix elab-mod$a))))
    ///
    (deffixequiv elab-mod$a-instname->idx))

  (defthm elab-modinst-list-names-of-append
    (equal (elab-modinst-list-names (append a b))
           (append (elab-modinst-list-names a) (elab-modinst-list-names b)))
    :hints(("Goal" :in-theory (enable elab-modinst-list-names append)
            :induct (elab-modinst-list-names a)
            :expand ((elab-modinst-list-names a)))))

  (define elab-mod$a-add-inst (elab-modinst$c (elab-mod$a elab-mod$ap))
    :returns (elab-mod$a2 elab-mod$ap
                          :hints(("Goal" :in-theory (enable elab-modinst-list-names)
                                  :expand ((:free (a b)
                                            (elab-modinst-list-names (cons a b)))))))
    (let* ((elab-modinst (non-exec (elab-modinst$c-fix elab-modinst$c)))
           (iname (non-exec (elab-modinst$c->instname elab-modinst)))
           (elab-mod$a (elab-mod$a-fix elab-mod$a))
           (insts (g :insts elab-mod$a)))
      (s :insts
         (if (member-equal iname (elab-modinst-list-names insts))
             insts
           (append-without-guard insts (list (non-exec elab-modinst))))
         elab-mod$a))
    ///
    (deffixequiv elab-mod$a-add-inst))

  (define elab-mod$a->name ((elab-mod$a elab-mod$ap))
    (modname-fix (g :name elab-mod$a))
    ///
    (deffixequiv elab-mod$a->name))

  (define elab-mod$a->totalwires ((elab-mod$a elab-mod$ap))
    (nfix (g :totalwires elab-mod$a))
    ///
    (deffixequiv elab-mod$a->totalwires))

  (define elab-mod$a->totalinsts ((elab-mod$a elab-mod$ap))
    (nfix (g :totalinsts elab-mod$a))
    ///
    (deffixequiv elab-mod$a->totalinsts))

  (define elab-mod$a->orig-mod ((elab-mod$a elab-mod$ap))
    (ec-call (module-fix$inline (g :orig-mod elab-mod$a)))
    ///
    (deffixequiv elab-mod$a->orig-mod))

  (define update-elab-mod$a->name ((name modname-p) (elab-mod$a elab-mod$ap))
    :returns (elab-mod$a2 elab-mod$ap)
    (s :name (modname-fix name) (elab-mod$a-fix elab-mod$a))
    ///
    (fty::deffixequiv update-elab-mod$a->name))

  (define update-elab-mod$a->totalwires ((n natp) (elab-mod$a elab-mod$ap))
    :returns (elab-mod$a2 elab-mod$ap)
    (s :totalwires (nfix n) (elab-mod$a-fix elab-mod$a))
    ///
    (fty::deffixequiv update-elab-mod$a->totalwires))

  (define update-elab-mod$a->totalinsts ((n natp) (elab-mod$a elab-mod$ap))
    :returns (elab-mod$a2 elab-mod$ap)
    (s :totalinsts (nfix n) (elab-mod$a-fix elab-mod$a))
    ///
    (fty::deffixequiv update-elab-mod$a->totalinsts))

  (define update-elab-mod$a->orig-mod ((m module-p) (elab-mod$a elab-mod$ap))
    :returns (elab-mod$a2 elab-mod$ap)
    (s :orig-mod (module-fix m) (elab-mod$a-fix elab-mod$a))
    ///
    (deffixequiv update-elab-mod$a->orig-mod))

  (define create-elab-mod$a ()
    :returns (elab-mod$a elab-mod$ap)
    (b* ((m (s :name "default-modname" nil))
         (m (s :totalwires 0 m))
         (m (s :totalinsts 0 m))
         (m (s :orig-mod (make-module) m)))
      m)))

(defsection elab-mod-absstobj
  (local (defun-nx elab-mod-corr (elab-mod$c elab-mod)
           (and (elab-mod$cp elab-mod$c)
                (elab-mod$c-wires-ok elab-mod$c)
                (elab-mod$c-modinsts-ok elab-mod$c)
                (equal (g :wires elab-mod)
                       (elab-mod$c-wire-abstraction elab-mod$c))
                (equal (g :insts elab-mod)
                       (elab-mod$c-inst-abstraction elab-mod$c))
                (equal (g :name elab-mod)
                       (elab-mod$c->name elab-mod$c))
                (equal (g :totalwires elab-mod)
                       (elab-mod$c->totalwires elab-mod$c))
                (equal (g :totalinsts elab-mod)
                       (elab-mod$c->totalinsts elab-mod$c))
                (equal (g :orig-mod elab-mod)
                       (elab-mod$c->orig-mod elab-mod$c)))))

  (local (defthm name-p-of-instname-when-elab-modinst$cp
           (implies (elab-modinst$cp x)
                    (name-p (nth *elab-modinst$c->instname* x)))))

  (local (in-theory (disable (elab-mod-corr)
                             (elab-mod$c-wires-ok)
                             (elab-mod$c-modinsts-ok)
                             (elab-mod$c-inst-abstraction)
                             acl2::nth-when-too-large-cheap
                             len not member
                             acl2::take-of-len-free
                             acl2::take
                             acl2::nth-when-atom
                             elab-modinst$cp)))




  (local (defthm elab-mod$c-wire-indices-ok-frame
           (implies (and (not (equal n *elab-mod$c->nwires*))
                         (not (equal n *elab-mod$c->wiretablei*))
                         (not (equal n *elab-mod$c->wirename-idxes-get*)))
                    (equal (elab-mod$c-wire-indices-ok
                            (update-nth n v x))
                           (elab-mod$c-wire-indices-ok x)))
           :hints (("goal" :cases ((elab-mod$c-wire-indices-ok x)))
                   (and stable-under-simplificationp
                        (if (eq (caar clause) 'not)
                            `(:expand (,(car (last clause)))
                              :use ((:instance elab-mod$c-wire-indices-ok-necc
                                     (elab-mod$c ,(cadr (cadr (car clause))))
                                     (idx (elab-mod$c-wire-indices-ok-witness
                                           ,(cadr (car (last clause)))))))
                              :in-theory (disable elab-mod$c-wire-indices-ok-necc))
                          `(:expand (,(car clause))
                            :use ((:instance elab-mod$c-wire-indices-ok-necc
                                   (elab-mod$c ,(cadr (cadr (car (last clause)))))
                                   (idx (elab-mod$c-wire-indices-ok-witness
                                         ,(cadr (car clause))))))
                            :in-theory (disable elab-mod$c-wire-indices-ok-necc)))))))

  (local (defthm elab-mod$c-wire-names-ok-frame
           (implies (and (not (equal n *elab-mod$c->nwires*))
                         (not (equal n *elab-mod$c->wiretablei*))
                         (not (equal n *elab-mod$c->wirename-idxes-get*)))
                    (equal (elab-mod$c-wire-names-ok
                            (update-nth n v x))
                           (elab-mod$c-wire-names-ok x)))
           :hints (("goal" :cases ((elab-mod$c-wire-names-ok x)))
                   (and stable-under-simplificationp
                        (if (eq (caar clause) 'not)
                            `(:expand (,(car (last clause)))
                              :use ((:instance elab-mod$c-wire-names-ok-necc
                                     (elab-mod$c ,(cadr (cadr (car clause))))
                                     (name (elab-mod$c-wire-names-ok-witness
                                            ,(cadr (car (last clause)))))))
                              :in-theory (disable elab-mod$c-wire-names-ok-necc))
                          `(:expand (,(car clause))
                            :use ((:instance elab-mod$c-wire-names-ok-necc
                                   (elab-mod$c ,(cadr (cadr (car (last clause)))))
                                   (name (elab-mod$c-wire-names-ok-witness
                                          ,(cadr (car clause))))))
                            :in-theory (disable elab-mod$c-wire-names-ok-necc)))))))

  (local (defthm elab-mod$c-inst-indices-ok-frame
           (implies (and (not (equal n *elab-mod$c->ninsts*))
                         (not (equal n *elab-mod$c->modinsttablei*))
                         (not (equal n *elab-mod$c->modinstname-idxes-get*)))
                    (equal (elab-mod$c-inst-indices-ok
                            (update-nth n v x))
                           (elab-mod$c-inst-indices-ok x)))
           :hints (("goal" :cases ((elab-mod$c-inst-indices-ok x)))
                   (and stable-under-simplificationp
                        (if (eq (caar clause) 'not)
                            `(:expand (,(car (last clause)))
                              :use ((:instance elab-mod$c-inst-indices-ok-necc
                                     (elab-mod$c ,(cadr (cadr (car clause))))
                                     (idx (elab-mod$c-inst-indices-ok-witness
                                           ,(cadr (car (last clause)))))))
                              :in-theory (disable elab-mod$c-inst-indices-ok-necc))
                          `(:expand (,(car clause))
                            :use ((:instance elab-mod$c-inst-indices-ok-necc
                                   (elab-mod$c ,(cadr (cadr (car (last clause)))))
                                   (idx (elab-mod$c-inst-indices-ok-witness
                                         ,(cadr (car clause))))))
                            :in-theory (disable elab-mod$c-inst-indices-ok-necc)))))))

  (local (defthm elab-mod$c-inst-names-ok-frame
           (implies (and (not (equal n *elab-mod$c->ninsts*))
                         (not (equal n *elab-mod$c->modinsttablei*))
                         (not (equal n *elab-mod$c->modinstname-idxes-get*)))
                    (equal (elab-mod$c-inst-names-ok
                            (update-nth n v x))
                           (elab-mod$c-inst-names-ok x)))
           :hints (("goal" :cases ((elab-mod$c-inst-names-ok x)))
                   (and stable-under-simplificationp
                        (if (eq (caar clause) 'not)
                            `(:expand (,(car (last clause)))
                              :use ((:instance elab-mod$c-inst-names-ok-necc
                                     (elab-mod$c ,(cadr (cadr (car clause))))
                                     (name (elab-mod$c-inst-names-ok-witness
                                            ,(cadr (car (last clause)))))))
                              :in-theory (disable elab-mod$c-inst-names-ok-necc))
                          `(:expand (,(car clause))
                            :use ((:instance elab-mod$c-inst-names-ok-necc
                                   (elab-mod$c ,(cadr (cadr (car (last clause)))))
                                   (name (elab-mod$c-inst-names-ok-witness
                                          ,(cadr (car clause))))))
                            :in-theory (disable elab-mod$c-inst-names-ok-necc)))))))




  (local (defthm elab-mod$c->wiretablep-is-wirelist-p
           (equal (elab-mod$c->wiretablep x)
                  (wirelist-p x))))

  (local (defthm index-of-take
           (implies (<= (nfix n) (len x))
                    (equal (index-of k (take n x))
                           (and (index-of k x)
                                (< (index-of k x) (nfix n))
                                (index-of k x))))
           :hints(("Goal" :in-theory (enable index-of len take)))))

  (local (defthm len-when-equal-take
           (implies (equal x (take n y))
                    (equal (len x) (nfix n)))))

  (local (defthm nth-when-equal-take
           (implies (equal y (take n x))
                    (equal (nth m y)
                           (and (< (nfix m) (nfix n))
                                (nth m x))))))
  (local (defthm nth-of-wirelist
           (implies (and (wirelist-p x)
                         (< (nfix n) (len x)))
                    (wire-p (nth n x)))
           :hints(("Goal" :in-theory (enable wirelist-p nth len)
                   :induct (nth n x)))))

  ;; (local (defthm nth-in-string-list
  ;;          (implies (and (namelist-p x)
  ;;                        (< (nfix n) (len x)))
  ;;                   (stringp (nth n x)))
  ;;          :hints(("Goal" :in-theory (enable nth len)
  ;;                  :induct (nth n x)
  ;;                  :expand ((nth n x))))))

  ;; (local (defthm namelist-p-of-update-nth
  ;;          (implies (and (namelist-p x)
  ;;                        (stringp v)
  ;;                        (<= (nfix n) (len x)))
  ;;                   (namelist-p (update-nth n v x)))
  ;;          :hints(("Goal" :in-theory (enable update-nth len)))))

  ;; (local (defthm namelist-p-of-resize-list
  ;;          (implies (and (namelist-p x)
  ;;                        (stringp default))
  ;;                   (namelist-p (resize-list x n default)))
  ;;          :hints(("Goal" :in-theory (enable acl2::replicate)))))

  (local (defthm member-take
           (implies (<= (nfix n) (len x))
                    (iff (member k (take n x))
                         (and (member k x)
                              (< (index-of k x)
                                 (nfix n)))))
           :hints(("Goal" :in-theory (enable index-of len take)))))


  (defthm remove-duplicates-equal-when-no-duplicates-under-list-equiv
    (implies (no-duplicatesp x)
             (equal (remove-duplicates-equal x)
                    (list-fix x)))
    :hints(("Goal" :in-theory (enable remove-duplicates-equal
                                      no-duplicatesp))))

  (defthm index-of-of-list-fix
    (equal (index-of k (list-fix x))
           (index-of k x))
    :hints(("Goal" :in-theory (enable index-of))))

  (defcong acl2::list-equiv equal (index-of k x) 2
    :hints(("Goal" :use ((:instance index-of-of-list-fix)
                         (:instance index-of-of-list-fix
                          (x x-equiv)))
            :in-theory (disable index-of-of-list-fix))))

  (local
   (defthm elab-mod$cp-as-hyp
     (implies (acl2::rewriting-negative-literal
               `(elab-mod$cp ,elab-mod$c))
              (equal (elab-mod$cp elab-mod$c)
                     (AND (TRUE-LISTP ELAB-MOD$C)
                          (= (LENGTH ELAB-MOD$C) 10)
                          (ELAB-MOD$C->NAMEP (NTH 0 ELAB-MOD$C))
                          (ELAB-MOD$C->NWIRESP (NTH 1 ELAB-MOD$C))
                          (ELAB-MOD$C->WIRETABLEP (NTH 2 ELAB-MOD$C))
                          (ELAB-MOD$C->WIRENAME-IDXESP (NTH 3 ELAB-MOD$C))
                          (ELAB-MOD$C->NINSTSP (NTH 4 ELAB-MOD$C))
                          (ELAB-MOD$C->MODINSTTABLEP (NTH 5 ELAB-MOD$C))
                          (ELAB-MOD$C->MODINSTNAME-IDXESP (NTH 6 ELAB-MOD$C))
                          (ELAB-MOD$C->TOTALWIRESP (NTH 7 ELAB-MOD$C))
                          (ELAB-MOD$C->TOTALINSTSP (NTH 8 ELAB-MOD$C))
                          (ELAB-MOD$C->ORIG-MODP (NTH 9 ELAB-MOD$C))
                          T)))))

  (local (in-theory (disable elab-mod$cp)))

  (local (set-default-hints
          '((and stable-under-simplificationp
                 '(:in-theory (enable elab-mod$a->name
                                      elab-mod$a->totalwires
                                      elab-mod$a->totalinsts
                                      elab-mod$a->orig-mod

                                      update-elab-mod$a->name
                                      update-elab-mod$a->totalwires
                                      update-elab-mod$a->totalinsts
                                      update-elab-mod$a->orig-mod

                                      elab-mod$a-nwires
                                      elab-mod$a-wiretablei
                                      elab-mod$a-wirename->idx
                                      elab-mod$a-add-wire

                                      elab-mod$a-ninsts
                                      elab-mod$a->instname
                                      elab-mod$a->inst-modidx
                                      elab-mod$a->inst-wireoffset
                                      elab-mod$a->inst-instoffset
                                      elab-mod$a-instname->idx
                                      elab-mod$a-add-inst)))
            (and stable-under-simplificationp
                 '(:in-theory (enable elab-mod$c-wire-abstraction
                                      elab-mod$c-inst-abstraction)
                   :do-not-induct t))
            (and stable-under-simplificationp
                 '(:in-theory (enable elab-mod$cp)))
            (and stable-under-simplificationp
                 '(:in-theory (enable elab-mod$c-wires-ok
                                      elab-mod$c-modinsts-ok)))
            (and stable-under-simplificationp
                 '(:in-theory (enable elab-mod$c-add-wire
                                      elab-mod$c-add-inst
                                      elab-mod$c-wires-ok
                                      elab-mod$c-modinsts-ok)))
            (and stable-under-simplificationp
                 '(:in-theory (enable elab-mod$c-modinsts-ok-implies-lookup-name
                                      elab-mod$c-wires-ok-implies-lookup-name
                                      elab-mod$c-wires-ok
                                      elab-mod$c-modinsts-ok)))
            )))

  (acl2::defabsstobj-events elab-mod
    :concrete elab-mod$c
    :creator (create-elab-mod :logic create-elab-mod$a :exec create-elab-mod$c)
    :recognizer (elab-modp :logic elab-mod$ap :exec elab-mod$cp)
    :corr-fn elab-mod-corr
    :exports
    ((elab-mod->name       :logic elab-mod$a->name       :exec elab-mod$c->name)
     (elab-mod->totalwires :logic elab-mod$a->totalwires :exec elab-mod$c->totalwires)
     (elab-mod->totalinsts :logic elab-mod$a->totalinsts :exec elab-mod$c->totalinsts)
     (elab-mod->orig-mod   :logic elab-mod$a->orig-mod   :exec elab-mod$c->orig-mod)

     (update-elab-mod->name       :logic update-elab-mod$a->name       :exec update-elab-mod$c->name)
     (update-elab-mod->totalwires :logic update-elab-mod$a->totalwires :exec update-elab-mod$c->totalwires)
     (update-elab-mod->totalinsts :logic update-elab-mod$a->totalinsts :exec update-elab-mod$c->totalinsts)
     (update-elab-mod->orig-mod   :logic update-elab-mod$a->orig-mod   :exec update-elab-mod$c->orig-mod)

     (elab-mod-nwires :logic elab-mod$a-nwires :exec elab-mod$c->nwires)
     (elab-mod-wiretablei :logic elab-mod$a-wiretablei
                          :exec elab-mod$c->wiretablei)
     (elab-mod-wirename->idx :logic elab-mod$a-wirename->idx
                             :exec elab-mod$c->wirename-idxes-get)
     (elab-mod-add-wire :logic elab-mod$a-add-wire
                        :exec elab-mod$c-add-wire
                        :protect t)

     (elab-mod-ninsts :logic elab-mod$a-ninsts :exec elab-mod$c->ninsts)
     (elab-mod->instname :logic elab-mod$a->instname :exec elab-mod$c->instname)
     (elab-mod->inst-modidx :logic elab-mod$a->inst-modidx :exec elab-mod$c->inst-modidx)
     (elab-mod->inst-wireoffset :logic elab-mod$a->inst-wireoffset :exec elab-mod$c->inst-wireoffset)
     (elab-mod->inst-instoffset :logic elab-mod$a->inst-instoffset :exec elab-mod$c->inst-instoffset)

     (elab-mod-instname->idx :logic elab-mod$a-instname->idx
                             :exec elab-mod$c->modinstname-idxes-get)
     (elab-mod-add-inst :logic elab-mod$a-add-inst
                        :exec elab-mod$c-add-inst
                        :protect t)))

  (in-theory (enable elab-mod$a->name
                     elab-mod$a->totalwires
                     elab-mod$a->totalinsts
                     elab-mod$a->orig-mod
                     update-elab-mod$a->name
                     update-elab-mod$a->totalwires
                     update-elab-mod$a->totalinsts
                     update-elab-mod$a->orig-mod))

  (acl2::defstobj-clone elab-mod2 elab-mod :suffix "2")
  (acl2::defstobj-clone new-elab-mod elab-mod :suffix "NEW")

  (acl2::def-stobj-swap elab-mod elab-mod2))


(defsection elab-modlist
  (deflist elab-modlist :elt-type elab-mod :true-listp t)

  (defthm nth-of-elab-modlist-fix-under-elab-mod$a-equiv
    (elab-mod$a-equiv (nth n (elab-modlist-fix x))
                      (nth n x))
    :hints(("Goal" :in-theory (enable elab-modlist-fix nth))))

  (defthm nth-when-elab-modlist-p
    (implies (and (elab-modlist-p x)
                  (< (nfix n) (len x)))
             (elab-mod$ap (nth n x)))
    :hints(("Goal" :in-theory (enable elab-modlist-p nth))))

  (defthm len-of-elab-modlist-fix
    (equal (len (elab-modlist-fix x))
           (len x))
    :hints(("Goal" :in-theory (enable elab-modlist-fix))))

  (define elab-mods->names ((elab-mods elab-modlist-p))
    :returns (names modnamelist-p)
    :guard-hints (("goal" :in-theory (enable elab-modlist-p
                                             elab-mod$ap)))
    (if (atom elab-mods)
        nil
      (cons (modname-fix (g :name (car elab-mods)))
            (elab-mods->names (cdr elab-mods))))
    ///
    (deffixequiv elab-mods->names
      :hints(("Goal" :in-theory (enable elab-modlist-fix
                                        elab-mod$a-fix))))

    (defthm elab-mods->names-of-take
      (implies (<= (nfix n) (len elab-mods))
               (equal (elab-mods->names (take n elab-mods))
                      (take n (elab-mods->names elab-mods))))
      :hints (("Goal" :in-theory (enable take))))

    (defthm len-of-elab-mods->names
      (equal (len (elab-mods->names x))
             (len x)))

    (defthm nth-of-elab-mods->names
      (implies (< (nfix n) (len x))
               (equal (nth n (elab-mods->names x))
                      (modname-fix (g :name (nth n x)))))
      :hints(("Goal" :in-theory (enable nth)))))

  (define elab-modlist-norm ((x elab-modlist-p))
    :verify-guards nil
    (if (atom x)
        nil
      (let ((rest (elab-modlist-norm (cdr x))))
        (if (and (not rest)
                 (elab-mod$a-equiv (car x) nil))
            nil
          (cons (elab-mod$a-fix (car x)) rest))))
    ///
    (deffixequiv elab-modlist-norm)

    (defthm elab-modlist-norm-idempotent
      (equal (elab-modlist-norm (elab-modlist-norm x))
             (elab-modlist-norm x)))

    (define elab-modlist-normp (x)
      :verify-guards nil
      (equal (elab-modlist-norm x) x)
      ///
      (deffixtype elab-modlist-norm :fix elab-modlist-norm :pred elab-modlist-normp
        :equiv elab-modlist-norm-equiv :define t :forward t :executablep nil))

    (defthm elab-modlist-fix-of-elab-modlist-norm
      (equal (elab-modlist-fix (elab-modlist-norm x))
             (elab-modlist-norm x)))

    (defrefinement elab-modlist-equiv elab-modlist-norm-equiv)

    (fty::deffixcong elab-modlist-norm-equiv elab-mod$a-equiv (nth n x) x
      :hints(("Goal" :in-theory (enable nth)
              :induct (nth n x))))

    (fty::deffixcong elab-modlist-norm-equiv elab-modlist-norm-equiv
      (update-nth n v X) x
      :hints(("Goal" :in-theory (e/d (update-nth)
                                     (acl2::update-nth-when-atom)))))
    (fty::deffixcong elab-mod$a-equiv elab-modlist-norm-equiv
      (update-nth n v X) v
      :hints(("Goal" :in-theory (e/d (update-nth)
                                     (acl2::update-nth-when-atom)))))))

(defsection elab-mod-congruences
  (fty::deffixcong elab-modlist-equiv elab-modlist-equiv (resize-list lst n d) lst)
  (fty::deffixcong elab-mod$a-equiv elab-modlist-equiv (replicate n d) d
    :hints(("Goal" :in-theory (enable replicate))))
  (fty::deffixcong elab-mod$a-equiv elab-modlist-equiv (resize-list lst n d) d)
  (fty::deffixcong elab-modlist-equiv elab-modlist-equiv (take n x) x
    :hints (("Goal" :in-theory (enable take))
            '(:expand (take n (elab-modlist-fix x)))))
  (fty::deffixcong elab-modlist-equiv elab-modlist-equiv (append x y) x)
  (fty::deffixcong elab-modlist-equiv elab-modlist-equiv (append x y) y)
  (fty::deffixcong elab-modlist-equiv elab-modlist-equiv (update-nth n v x) x
    :hints(("Goal" :in-theory (enable update-nth))))
  (fty::deffixcong elab-mod$a-equiv elab-modlist-equiv (update-nth n v x) v
    :hints(("Goal" :in-theory (enable update-nth))))
  (fty::deffixcong elab-mod$a-equiv modname-equiv (g :name x) x))

(defsection moddb-stobj
  (defstobj moddb
    ;; module names<->indices must be bijective
    (moddb->nmods1 :type (integer 0 *) :initially 0)
    (moddb->mods :type (array elab-mod (0)) :resizable t)
    (moddb->modname-idxes :type (hash-table equal)))

  (defconst *moddb->nmods* *moddb->nmods1*)

  (define moddb->nmods (moddb)
    :enabled t
    :inline t
    (mbe :logic (non-exec (nfix (nth *moddb->nmods* moddb)))
         :exec (moddb->nmods1 moddb)))

  (defthm moddb->modsp-is-elab-modlist-p
    (equal (moddb->modsp x)
           (elab-modlist-p x)))



  (define moddb-fix (moddb)
    :prepwork ((local (in-theory (enable nth)))
               (local (local (defthm equal-of-cons
                               (equal (equal (cons a b) c)
                                      (and (consp c)
                                           (equal (car c) a)
                                           (equal (cdr c) b))))))
               (local (defthm equal-of-len
                        (implies (syntaxp (quotep y))
                                 (equal (equal (len x) y)
                                        (if (zp y)
                                            (and (equal y 0)
                                                 (atom x))
                                          (and (consp x)
                                               (equal (len (cdr x)) (1- y)))))))))
    :hooks nil
    (mbe :logic (non-exec (list (nfix (nth 0 moddb))
                                (elab-modlist-fix (nth 1 moddb))
                                (nth 2 moddb)))
         :exec moddb)
    ///
    (defthm moddb-fix-when-moddbp
      (implies (moddbp moddb)
               (equal (moddb-fix moddb) moddb)))

    (deffixtype moddb :pred moddbp :fix moddb-fix :equiv moddb-equiv :define t :executablep nil)

    (defthm nth-of-moddb-fix
      (and (equal (nth 0 (moddb-fix moddb))
                  (nfix (nth 0 moddb)))
           (equal (nth 1 (moddb-fix moddb))
                  (elab-modlist-fix (nth 1 moddb)))
           (equal (nth 2 (moddb-fix moddb))
                  (nth 2 moddb))))

    (defcong moddb-equiv moddb-equiv (update-nth n v x) 3
      :hints(("Goal" :in-theory (enable moddb-fix))))

    (fty::deffixcong elab-modlist-equiv moddb-equiv (update-nth *moddb->modsi* v moddb) v))

  (define update-moddb->nmods ((n natp) moddb)
    :enabled t
    :inline t
    (mbe :logic (non-exec (update-nth *moddb->nmods* (nfix n) (moddb-fix moddb)))
         :exec (update-moddb->nmods1 n moddb))))

(define moddb-norm (moddb)
  :non-executable t
  :verify-guards nil
  :returns (moddb1 moddbp)
  (b* ((nmods (nfix (nth *moddb->nmods* moddb)))
       (mods (elab-modlist-fix (take (nth *moddb->nmods* moddb)
                                     (nth *moddb->modsi* moddb))))
       (names (elab-mods->names mods)))
    (list nmods mods (pairlis$ names (acl2::numlist 0 1 nmods))))

  ///

  (deffixequiv moddb-norm)

  (defthm hons-assoc-equal-pairlis
    (equal (hons-assoc-equal k (pairlis$ keys vals))
           (and (member k keys)
                (cons k (nth (index-of k keys) vals))))
    :hints(("Goal" :in-theory (enable index-of))))

  (local (defun ind (n start by count)
           (if (zp count)
               (list n start by)
             (ind (1- n) (+ start by) by (1- count)))))


  (defthm nth-of-numlist
    (implies (acl2-numberp start)
             (equal (nth n (acl2::numlist start by count))
                    (and (< (nfix n) (nfix count))
                         (+ start (* (nfix n) by)))))
    :hints(("Goal" :in-theory (enable nth)
            :induct (ind n start by count))))

  (local (defun ind2 (n m mods)
           (if (zp m)
               (list n mods)
             (ind2 (1- n) (1- m) (cdr mods)))))

  ;; (defthm member-name-nth-of-take-mod-names
  ;;   (implies (and (< (nfix n) (nfix m))
  ;;                 (<= (nfix m) (len mods)))
  ;;            (member (modname-fix (g :name (nth n mods)))
  ;;                    (take m (elab-mods->names mods))))
  ;;   :hints(("Goal" :in-theory (enable elab-mods->names nth)
  ;;           :induct (ind2 n m mods))
  ;;          (and stable-under-simplificationp
  ;;               '(:in-theory (enable nfix)))))

  ;; (defthm member-name-nth-of-mod-names
  ;;   (implies (< (nfix n) (len mods))
  ;;            (member (modname-fix (g :name (nth n mods)))
  ;;                    (elab-mods->names mods)))
  ;;   :hints(("Goal" :in-theory (enable nth elab-mods->names))))



  (defthm nmods-of-moddb-norm
    (equal (nth *moddb->nmods* (moddb-norm moddb))
           (nfix (nth *moddb->nmods* moddb)))
    :hints(("Goal" :in-theory (enable moddb-norm))))

  (defthm modidx-of-moddb-norm
           (implies (< (nfix modidx) (nfix (nth *moddb->nmods* moddb)))
                    (equal (nth modidx (nth *moddb->modsi* (moddb-norm moddb)))
                           (elab-mod$a-fix (nth modidx (nth *moddb->modsi* moddb)))))
           :hints(("Goal" :in-theory (enable moddb-norm))))

  (defthm moddb-norm-idempotent
    (equal (moddb-norm (moddb-norm moddb))
           (moddb-norm moddb)))

  (define moddb-norm-p (moddb)
    :non-executable t
    :verify-guards nil
    :hooks nil
    (equal (moddb-norm moddb) moddb)
    ///
    (deffixtype moddb-norm :pred moddb-norm-p
      :fix moddb-norm :equiv moddb-norm-equiv
      :define t :forward t :executablep nil)

    (fty::deffixcong moddb-norm-equiv nat-equiv (nth *moddb->nmods* moddb) moddb)

    (fty::deffixcong elab-modlist-norm-equiv elab-modlist-equiv
      (take n mods) mods
      :hints(("Goal" :in-theory (e/d (elab-modlist-norm
                                      take
                                      my-open-take)
                                     (acl2::take-when-atom
; Matt K. mod 5/2016 (type-set bit for {1}):
                                      acl2::<-0-+-negative-1)))))

    (fty::deffixcong elab-modlist-norm-equiv moddb-norm-equiv
      (update-nth *moddb->modsi* mods moddb) mods)

    (defthm moddb-norm-equiv-nth-module-congruence
      (implies (and (< (nfix n) (nfix (nth *moddb->nmods* moddb)))
                    (moddb-norm-equiv moddb moddb1))
               (equal (elab-mod$a-equiv (nth n (nth *moddb->modsi* moddb))
                                        (nth n (nth *moddb->modsi* moddb1)))
                      t))
      :hints (("goal" :use ((:instance modidx-of-moddb-norm
                             (modidx n))
                            (:instance modidx-of-moddb-norm
                             (modidx n) (moddb moddb1)))
               :in-theory (disable modidx-of-moddb-norm moddb-norm))))

    (defthm moddb-fix-under-moddb-norm-equiv
      (moddb-norm-equiv (moddb-fix x)
                        x))))

(local (in-theory (disable
                   (:rewrite nth-of-elab-modlist-fix))))

;; We can't make moddb into an abstract stobj if we still want to let-bind
;; modules within it.  But we can define a strong interface that still
;; abstracts away the nastiness.


(defsection moddb-basics-ok
  (define moddb-find-bad-index ((idx natp) (moddb moddbp))
    :guard (and (<= (moddb->nmods moddb) (moddb->mods-length moddb))
                (<= idx (moddb->nmods moddb)))
    :prepwork ((local (defthmd equal-of-cons
                        (equal (equal (cons a b) c)
                               (and (consp c)
                                    (equal (car c) a)
                                    (equal (cdr c) b)))))
               (local (in-theory (disable
                                  acl2::nth-when-too-large-cheap
                                  hons-assoc-equal))))
    :guard-hints (("goal" :in-theory (enable equal-of-cons)))
    :returns (idx (iff (natp idx) idx))
    (if (zp idx)
        nil
      (b* ((idx (1- idx))
           ((unless (mbt (< idx (lnfix (moddb->nmods moddb)))))
            (moddb-find-bad-index idx moddb))
           (name (stobj-let ((elab-mod (moddb->modsi idx moddb)))
                            (name)
                            (elab-mod->name elab-mod)
                            name))
           (name-idx (moddb->modname-idxes-get name moddb)))
        (if (mbe :logic
                 (non-exec
                  (equal (cons name idx)
                         (hons-assoc-equal name
                                           (nth *moddb->modname-idxes-get* moddb))))
                 :exec (equal name-idx idx))
            (moddb-find-bad-index idx moddb)
          idx)))
    ///
    (deffixequiv moddb-find-bad-index
      :hints(("Goal" :in-theory (disable elab-mod$a->name))))


    ;; (defthm moddb-find-bad-index-bound
    ;;   (implies (moddb-find-bad-index idx moddb)
    ;;            (< (moddb-find-bad-index idx moddb) (nfix idx)))
    ;;   :rule-classes :linear)

    ;; (defthm moddb-find-bad-index-bound-nmods
    ;;   (implies (moddb-find-bad-index idx moddb)
    ;;            (< (moddb-find-bad-index idx moddb)
    ;;               (nfix (nth *moddb->nmods* moddb))))
    ;;   :rule-classes :linear)

    ;; (defthm moddb-find-bad-index-bound-mods-length
    ;;   (implies (moddb-find-bad-index idx moddb)
    ;;            (< (moddb-find-bad-index idx moddb)
    ;;               (len (nth *moddb->modsi* moddb))))
    ;;   :rule-classes :linear)

    ;; (defthm moddb-find-bad-index-bound-weak
    ;;   (<= (moddb-find-bad-index idx moddb) (nfix idx))
    ;;   :rule-classes :linear)

    (defthm moddb-find-bad-index-is-bad
      (implies (moddb-find-bad-index n moddb)
               (let* ((idx (moddb-find-bad-index n moddb))
                      (names->idxes (nth *moddb->modname-idxes-get* moddb))
                      (idxes->mods (nth *moddb->modsi* moddb))
                      (mod (nth idx idxes->mods))
                      (name (modname-fix (g :name mod))))
                 (and (< (nfix idx) (nfix n))
; (< (nfix idx) (len (nth *moddb->modsi* moddb)))
                      (< (nfix idx) (nfix (nth *moddb->nmods* moddb)))
                      (not (equal (hons-assoc-equal name names->idxes)
                                  (cons name (nfix idx)))))))
      :hints (("goal" :induct (moddb-find-bad-index n moddb)
               :in-theory (e/d (equal-of-cons)
                               ((:d moddb-find-bad-index)))
               :expand ((moddb-find-bad-index n moddb)
                        (moddb-find-bad-index 0 moddb)))))

    (defthm moddb-find-bad-index-finds-bad
      (implies (and (< (nfix idx) (nfix n))
; (< (nfix idx) (len (nth *moddb->modsi* moddb)))
                    (< (nfix idx) (nfix (nth *moddb->nmods* moddb)))
                    (let* ((names->idxes (nth *moddb->modname-idxes-get* moddb))
                           (idxes->mods (nth *moddb->modsi* moddb))
                           (mod (nth idx idxes->mods))
                           (name (modname-fix (g :name mod))))
                      (not (equal (hons-assoc-equal name names->idxes)
                                  (cons name (nfix idx))))))
               (and (moddb-find-bad-index n moddb)
                    (let* ((idx (moddb-find-bad-index n moddb))
                           (names->idxes (nth *moddb->modname-idxes-get* moddb))
                           (idxes->mods (nth *moddb->modsi* moddb))
                           (mod (nth idx idxes->mods))
                           (name (modname-fix (g :name mod))))
                      (not (equal (hons-assoc-equal name names->idxes)
                                  (cons name (nfix idx)))))))
      :hints (("goal" :induct (moddb-find-bad-index n moddb)
               :in-theory (disable (:d moddb-find-bad-index))
               :expand ((moddb-find-bad-index n moddb))))))

  (define moddb-indices-ok (moddb)
    :guard (<= (moddb->nmods moddb) (moddb->mods-length moddb))
    :prepwork ((local (in-theory (disable acl2::nth-when-too-large-cheap
                                          acl2::hons-remove-assoc))))
    (not (moddb-find-bad-index (moddb->nmods moddb) moddb))
    ///
    (deffixequiv moddb-indices-ok)

    (defthm moddb-indices-ok-implies
      (implies (and (moddb-indices-ok moddb)
                    (< (nfix idx) (nfix (nth *moddb->nmods* moddb))))
               (let* ((names->idxes (nth *moddb->modname-idxes-get* moddb))
                      (idxes->mods (nth *moddb->modsi* moddb))
                      (mod (nth idx idxes->mods))
                      (name (modname-fix (g :name mod))))
                 (equal (hons-assoc-equal name names->idxes)
                        (cons name (nfix idx)))))
      :hints (("goal" :use ((:instance moddb-find-bad-index-finds-bad
                             (n (nth *moddb->nmods* moddb))))
               :in-theory (disable moddb-find-bad-index-finds-bad))))

    (local (defthm nth-of-nil
             (equal (nth nil x)
                    (nth 0 x))
             :hints(("Goal" :in-theory (enable nth)))))

    (local (defthm len-equal-0
             (equal (equal (len x) 0)
                    (not (consp x)))))

    (defund-nx moddb-indices-badguy (moddb)
      (moddb-find-bad-index (moddb->nmods moddb) moddb))

    (defthmd moddb-indices-not-ok
      (implies (acl2::rewriting-positive-literal
                `(moddb-indices-ok ,moddb))
               (equal (moddb-indices-ok moddb)
                      (let* ((idx (moddb-indices-badguy moddb))
                             (names->idxes (nth *moddb->modname-idxes-get* moddb))
                             (idxes->mods (nth *moddb->modsi* moddb))
                             (mod (nth idx idxes->mods))
                             (name (modname-fix (g :name mod))))
                        (or (>= (nfix idx) (nfix (nth *moddb->nmods* moddb)))
                            (equal (hons-assoc-equal name names->idxes)
                                   (cons name (nfix idx)))))))
      :hints (("goal" :use ((:instance moddb-find-bad-index-finds-bad
                             (n (nth *moddb->nmods* moddb))
                             (idx 0))
                            (:instance moddb-find-bad-index-is-bad
                             (n (nth *moddb->nmods* moddb))))
               :in-theory (e/d (moddb-indices-badguy)
                               (moddb-find-bad-index-finds-bad
                                moddb-find-bad-index-is-bad))))
      :otf-flg t)

    (local (in-theory (disable moddb-indices-ok)))

    (local
     (defthm moddb-index-ok-of-remove-name-with-greater-index
       (implies (and (posp (nth *moddb->nmods* moddb))
                     (<= (+ -1 (nth *moddb->nmods* moddb))
                         (nfix (cdr (hons-assoc-equal name (nth *moddb->modname-idxes-get* moddb)))))
                     (moddb-indices-ok moddb))
                (moddb-indices-ok
                 (update-nth *moddb->nmods*
                             (+ -1 (nth *moddb->nmods* moddb))
                             (update-nth
                              *moddb->modname-idxes-get*
                              (acl2::hons-remove-assoc name (nth *moddb->modname-idxes-get* moddb))
                              moddb))))
       :hints (("goal" :in-theory (e/d (moddb-indices-not-ok)
                                       (moddb-indices-ok-implies)))
               (and stable-under-simplificationp
                    '(:use ((:instance moddb-indices-ok-implies
                             (idx (moddb-indices-badguy
                                   (update-nth *moddb->nmods*
                                               (+ -1 (nfix (nth *moddb->nmods* moddb)))
                                               (update-nth
                                                *moddb->modname-idxes-get*
                                                (acl2::hons-remove-assoc name (nth *moddb->modname-idxes-get* moddb))
                                                moddb)))))))))))

    (local
     (defun-nx ind (moddb)
       (declare (xargs :measure (nfix (moddb->nmods moddb))))
       (if (zp (moddb->nmods moddb))
           nil
         (let* ((idx (+ -1 (lnfix (moddb->nmods moddb))))
                (name (stobj-let ((elab-mod (moddb->modsi idx moddb)))
                                 (name)
                                 (elab-mod->name elab-mod)
                                 name))
                (name-idx (moddb->modname-idxes-get name moddb)))
           (if (equal name-idx idx)
               (b* ((moddb (moddb->modname-idxes-rem name moddb))
                    (moddb (update-moddb->nmods idx moddb)))
                 (ind moddb))
             idx)))))

    (local (defthm hons-assoc-equal-when-no-keys
             (implies (equal 0 (acl2::count-keys a))
                      (not (hons-assoc-equal k a)))))

    (defthm moddb-indices-ok-implies-name-indices-in-bounds
      (implies (and (moddb-indices-ok moddb)
; (<= (nfix (nth *moddb->nmods* moddb)) (len (nth *moddb->modsi* moddb)))
                    (equal (nfix (nth *moddb->nmods* moddb)) (acl2::count-keys (nth *moddb->modname-idxes-get* moddb))))
               (b* ((nametab (nth *moddb->modname-idxes-get* moddb))
                    (look (hons-assoc-equal name nametab)))
                 (implies look
                          (< (nfix (cdr look)) (nfix (nth *moddb->nmods* moddb))))))
      :hints (("goal" :induct (ind moddb)))
      :rule-classes :linear)


    (defthm moddb-indices-ok-implies-names-ok
      (implies (and (moddb-indices-ok moddb)
; (<= (nfix (nth *moddb->nmods* moddb)) (len (nth *moddb->modsi* moddb)))
                    (equal (nfix (nth *moddb->nmods* moddb)) (acl2::count-keys (nth *moddb->modname-idxes-get* moddb))))
               (b* ((nametab (nth *moddb->modname-idxes-get* moddb))
                    (look (hons-assoc-equal name nametab))
                    (name-idx-name
                     (modname-fix (g :name (nth (cdr look) (nth *moddb->modsi* moddb))))))
                 (implies look
                          (equal name-idx-name name))))
      :hints (("goal" :induct (ind moddb))))

    (defthm moddb-indices-ok-implies-no-duplicates-of-elab-mods->names
      (implies (and (moddb-indices-ok moddb)
                    (<= (nfix (nth *moddb->nmods* moddb)) (len (nth *moddb->modsi* moddb)))
                    (equal (nfix (nth *moddb->nmods* moddb)) (acl2::count-keys (nth *moddb->modname-idxes-get* moddb))))
               (no-duplicatesp (take (nth *moddb->nmods* moddb)
                                     (elab-mods->names (nth *moddb->modsi* moddb)))))
      :hints (("goal" :use ((:instance acl2::no-duplicatesp-by-indices-of-dup-witness
                             (x (take (nth *moddb->nmods* moddb)
                                      (elab-mods->names (nth *moddb->modsi* moddb)))))
                            (:instance moddb-indices-ok-implies
                             (idx (acl2::dup-index-1 (take (nth *moddb->nmods* moddb)
                                                     (elab-mods->names (nth *moddb->modsi* moddb))))))
                            (:instance moddb-indices-ok-implies
                             (idx (acl2::dup-index-2 (take (nth *moddb->nmods* moddb)
                                                     (elab-mods->names (nth *moddb->modsi* moddb)))))))
               :do-not-induct t
               :in-theory (e/d ()
                               ((elab-mods->names)
                                moddb-find-bad-index
                                acl2::take
                                acl2::take-of-len-free
                                moddb-indices-ok-implies))))
      :otf-flg t)

    (local (defthm acl2-numberp-index-of
             (iff (acl2-numberp (index-of k x))
                  (index-of k x))
             :hints(("Goal" :in-theory (enable index-of)))))

    (local (defun ind2 (n nmods mods)
             (if (zp n)
                 (list nmods mods)
               (ind2 (1- n) (1- nmods) (cdr mods)))))


    (local (defthm member-name-of-take
             (let ((name (modname-fix (g :name (nth n mods)))))
               (implies (< (nfix n) (nfix nmods))
                        (member name (elab-mods->names (take nmods mods)))))
             :hints(("Goal" :in-theory (e/d (elab-mods->names my-open-take nth take)
                                            (acl2::take-when-atom))))))

    (local (defthm name-nth-index-name-take
             (let ((name (modname-fix (g :name (nth n mods)))))
               (implies (< (nfix n) (nfix nmods))
                        (equal (modname-fix
                                (g :name (nth (index-of name (elab-mods->names (take nmods mods)))
                                              mods)))
                               name)))
             :hints(("Goal" :in-theory (e/d (index-of nth elab-mods->names
                                                      my-open-take)
                                            (acl2::integerp-of-index-of
                                             ;; ACL2::INDEX-OF-IFF-MEMBER
                                             acl2::take-when-atom
                                             acl2::take))
                     :induct (ind2 n nmods mods)))))

    (local (defthmd equal-of-cons
             (equal (equal (cons a b) c)
                    (and (consp c)
                         (equal (car c) a)
                         (equal (cdr c) b)))))

    (local (defthm cons-under-iff
             (iff (cons a b) t)))

    (local (defthm member-name-of-names-of-take
             (implies (< (nfix n) (nfix nmods))
                      (member (modname-fix (g :name (nth n mods)))
                              (elab-mods->names (take nmods mods))))
             :hints(("Goal" :in-theory (enable nth elab-mods->names)))))

    (defthm moddb-indices-ok-of-norm
      (implies (and (moddb-indices-ok moddb)
                    (equal (nfix (nth *moddb->nmods* moddb)) (acl2::count-keys (nth *moddb->modname-idxes-get* moddb))))
               (moddb-indices-ok (moddb-norm moddb)))
      :hints(("Goal" :in-theory (enable moddb-norm moddb-indices-not-ok))
             (and stable-under-simplificationp
                  '(:use ((:instance moddb-indices-ok-implies
                           (idx (moddb-indices-badguy (moddb-norm moddb))))
                          (:instance moddb-indices-ok-implies
                           (idx (index-of
                                 (modname-fix (g :name (nth (moddb-indices-badguy (moddb-norm moddb)) (nth *moddb->modsi* moddb))))
                                 (elab-mods->names
                                  (take (nth *moddb->nmods* moddb)
                                        (nth *moddb->modsi* moddb)))))))
                    :in-theory (e/d (moddb-norm)
                                    (moddb-indices-ok-implies)))))
      :otf-flg t))

  (define moddb-basics-ok (moddb)
    (and (<= (lnfix (moddb->nmods moddb)) (moddb->mods-length moddb))
         (eql (lnfix (moddb->nmods moddb))
              (moddb->modname-idxes-count moddb))
         (moddb-indices-ok moddb))
    ///

    (deffixequiv moddb-basics-ok)

    (defthm moddb-basics-linear
      (implies (moddb-basics-ok moddb)
               (<= (nfix (nth *moddb->nmods* moddb))
                   (len (nth *moddb->modsi* moddb))))
      :rule-classes :linear)

    (defthm moddb-basics-count
      (implies (moddb-basics-ok moddb)
               (eql (acl2::count-keys (nth *moddb->modname-idxes-get* moddb))
                    (lnfix (moddb->nmods moddb)))))


    (defthm moddb-indices-ok-when-moddb-basics-ok
      (implies (moddb-basics-ok moddb)
               (moddb-indices-ok moddb)))

    (local (defthm count-keys-of-pairlis-when-no-duplicates
             (implies (no-duplicatesp keys)
                      (equal (acl2::count-keys (pairlis$ keys vals))
                             (len keys)))))

    (defthm moddb-basics-ok-of-norm
      (implies (moddb-basics-ok moddb)
               (moddb-basics-ok (moddb-norm moddb)))
      :hints ((and stable-under-simplificationp
                   '(:in-theory (enable moddb-norm)))))

    (local (in-theory (disable moddb-basics-ok)))

    (local (Defthm acl2-numberp-index-of
             (iff (acl2-numberp (index-of n x))
                  (index-of n x))
             :hints (("goal" :in-theory (enable index-of)))))

    (local (defthm nth-nil
             (equal (nth nil x)
                    (nth 0 x))
             :hints(("Goal" :in-theory (enable nth)))))

    (local (Defthm cons-under-iff
             (iff (cons a b) t)))

    (defthm lookup-name-in-moddb-norm
      (implies (moddb-basics-ok moddb)
               (equal (hons-assoc-equal name (nth *moddb->modname-idxes-get*
                                                  (moddb-norm moddb)))
                      (hons-assoc-equal name (nth *moddb->modname-idxes-get* moddb))))
      :hints(("Goal" :in-theory (e/d ()
                                     (moddb-indices-ok-implies-names-ok
                                      moddb-indices-ok-implies))
              :use ((:instance moddb-indices-ok-implies-names-ok
                     (moddb (moddb-norm moddb)))
                    (:instance moddb-indices-ok-implies-names-ok)
                    (:instance moddb-indices-ok-implies
                     (idx (cdr (hons-assoc-equal
                                name (nth *moddb->modname-idxes-get* moddb))))
                     (moddb (moddb-norm moddb)))
                    (:instance moddb-indices-ok-implies
                     (idx (cdr (hons-assoc-equal
                                name (nth *moddb->modname-idxes-get* (moddb-norm moddb)))))
                     (moddb moddb)))
              :do-not-induct t)
             (and stable-under-simplificationp
                  '(:in-theory (e/d (moddb-norm) (moddb-indices-ok-implies-names-ok
                                                  moddb-indices-ok-implies)))))
      :otf-flg t)))

;; (define moddb-instidx-wireoffset ((instidx natp)
;;                                   (modidx natp)
;;                                   moddb)
;;   :guard (and (< modidx (moddb->mods-length moddb))
;;               (stobj-let ((elab-mod (moddb->modsi modidx moddb)))
;;                          (ok)
;;                          (and (< instidx (elab-mod-ninsts elab-mod))
;;                               (or (zp instidx)
;;                                   (let ((instmod (elab-mod->inst-modidx (1- instidx) elab-mod)))
;;                                     (< instmod modidx))))
;;                          ok))
;;   (b* (((when (>= (lnfix modidx) (moddb->mods-length moddb))) 0)
;;        ((
;;                   (>= (lnfix instidx) (elab-mod-ninsts elab-mod))

(defsection moddb-mod-order-ok
  (define moddb-modinst-order-ok ((instidx natp)
                                  (modidx natp)
                                  moddb)
    :guard (and (< modidx (moddb->nmods moddb))
                (<= (moddb->nmods moddb) (moddb->mods-length moddb))
                (stobj-let ((elab-mod (moddb->modsi modidx moddb)))
                           (ok)
                           (< instidx (elab-mod-ninsts elab-mod))
                           ok))
    (b* (((unless (mbt (and (< (lnfix modidx) (lnfix (moddb->nmods moddb)))
; (< (lnfix modidx) (moddb->mods-length moddb))
                            (stobj-let ((elab-mod (moddb->modsi modidx moddb)))
                                       (ok)
                                       (< (lnfix instidx) (elab-mod-ninsts elab-mod))
                                       ok))))
          t)
         ((stobj-get instname submodidx)
          ((elab-mod (moddb->modsi modidx moddb)))
          (mv (elab-mod->instname instidx elab-mod)
              (elab-mod->inst-modidx instidx elab-mod)))
         ((unless (< submodidx (lnfix modidx)))
          (cw "Mod index out of order: ~s0~%" instname)))
      t)
    ///

    (deffixequiv moddb-modinst-order-ok)

    (defthm moddb-modinst-order-ok-implies-modidx-less
      (implies (and (moddb-modinst-order-ok instidx modidx moddb)
; (< (nfix modidx) (len (nth *moddb->modsi* moddb)))
                    (< (nfix modidx) (nfix (nth *moddb->nmods* moddb)))
                    (< (nfix instidx) (elab-mod$a-ninsts (nth modidx (nth *moddb->modsi* moddb)))))
               (< (ELAB-MOD$A->INST-MODIDX INSTIDX
                                           (NTH MODIDX (NTH *MODDB->MODSI* MODDB)))
                  (NFIX MODIDX)))
      :rule-classes (:rewrite :linear))

    (fty::deffixcong moddb-norm-equiv equal (moddb-modinst-order-ok idx modidx moddb) moddb))

  (define moddb-find-bad-modinst-order ((n natp) (modidx natp) moddb)
    :returns (idx (iff (natp idx) idx))
    :guard (and (< modidx (moddb->nmods moddb))
                (<= (moddb->nmods moddb) (moddb->mods-length moddb))
                (stobj-let ((elab-mod (moddb->modsi modidx moddb)))
                           (ok)
                           (<= n (elab-mod-ninsts elab-mod))
                           ok))
    (if (zp n)
        nil
      (if (moddb-modinst-order-ok (1- n) modidx moddb)
          (moddb-find-bad-modinst-order (1- n) modidx moddb)
        (1- n)))
    ///
    (deffixequiv moddb-find-bad-modinst-order)

    (defthm moddb-find-bad-modinst-order-bound-weak
      (<= (moddb-find-bad-modinst-order n modidx moddb) (nfix n))
      :rule-classes :linear)
    (defthm moddb-find-bad-modinst-order-bound
      (implies (moddb-find-bad-modinst-order n modidx moddb)
               (< (moddb-find-bad-modinst-order n modidx moddb) (nfix n)))
      :rule-classes :linear)

    (defthm moddb-find-bad-modinst-order-is-bad
      (implies (moddb-find-bad-modinst-order n modidx moddb)
               (not (moddb-modinst-order-ok
                     (moddb-find-bad-modinst-order n modidx moddb)
                     modidx moddb))))

    (defthm moddb-find-bad-modinst-order-finds-bad
      (implies (and (not (moddb-modinst-order-ok idx modidx moddb))
                    (< (nfix idx) (nfix n)))
               (and (moddb-find-bad-modinst-order n modidx moddb)
                    (not (moddb-modinst-order-ok
                          (moddb-find-bad-modinst-order n modidx moddb)
                          modidx moddb))))))

  (define moddb-mod-order-ok ((modidx natp) moddb)
    :guard (and (< modidx (moddb->nmods moddb))
                (<= (moddb->nmods moddb) (moddb->mods-length moddb)))
    (b* (((unless (mbt (< (lnfix modidx) (lnfix (moddb->nmods moddb))))) t)
         ((stobj-get ninsts)
          ((elab-mod (moddb->modsi modidx moddb)))
          (elab-mod-ninsts elab-mod)))
      (not (moddb-find-bad-modinst-order ninsts modidx moddb)))
    ///
    (deffixequiv moddb-mod-order-ok)

    (defthm moddb-mod-order-ok-implies
      (implies (and (moddb-mod-order-ok modidx moddb)
                    ;; (< (nfix modidx) (len (nth *moddb->modsi* moddb) ))
                    (< (nfix modidx) (nfix (nth *moddb->nmods* moddb)))
                    (< (nfix idx) (elab-mod$a-ninsts
                                   (nth modidx (nth *moddb->modsi* moddb)))))
               (moddb-modinst-order-ok idx modidx moddb))
      :hints (("goal" :use ((:instance moddb-find-bad-modinst-order-finds-bad
                             (n (elab-mod-ninsts (moddb->modsi modidx moddb)))))
               :in-theory (disable moddb-find-bad-modinst-order-finds-bad))))

    (define moddb-modinst-order-badguy ((modidx natp) moddb)
      :non-executable t
      :verify-guards nil
      (let ((moddb (moddb-fix moddb)))
        (moddb-find-bad-modinst-order (elab-mod-ninsts (moddb->modsi modidx moddb)) modidx moddb))
      ///
      (deffixequiv moddb-modinst-order-badguy)

      (defthmd moddb-mod-order-not-ok
        (implies (acl2::rewriting-positive-literal
                  `(moddb-mod-order-ok ,modidx ,moddb))
                 (equal (moddb-mod-order-ok modidx moddb)
                        (let ((idx (moddb-modinst-order-badguy modidx moddb)))
                          (or (>= (nfix idx) (elab-mod$a-ninsts
                                              (nth modidx (nth *moddb->modsi* moddb))))
                              (>= (nfix modidx) (nfix (nth *moddb->nmods* moddb)))
                              (moddb-modinst-order-ok idx modidx moddb)))))
        :hints (("goal" :use ((:instance moddb-find-bad-modinst-order-finds-bad
                               (n (elab-mod-ninsts (moddb->modsi modidx moddb)))
                               (idx 0)))
                 :in-theory (disable moddb-find-bad-modinst-order-finds-bad))
                (and stable-under-simplificationp
                     '(:expand ((moddb-modinst-order-ok 0 modidx moddb)
                                (moddb-find-bad-modinst-order 0 modidx moddb)))))))


    (fty::deffixcong moddb-norm-equiv equal (moddb-mod-order-ok modidx moddb) moddb
      :hints(("Goal" :in-theory (e/d ()
                                     (moddb-mod-order-ok))
              :cases ((moddb-mod-order-ok modidx moddb)))
             (and stable-under-simplificationp
                  '(:in-theory (e/d (moddb-mod-order-not-ok)
                                    (moddb-mod-order-ok))))
             (and stable-under-simplificationp
                  '(:use ((:instance moddb-mod-order-ok-implies
                           (idx (moddb-modinst-order-badguy modidx moddb))
                           (moddb (moddb-norm moddb))))
                    :in-theory (disable moddb-mod-order-ok
                                        moddb-mod-order-ok-implies)))))))


(define elab-mod-wireoffset ((instidx natp) elab-mod)
  :guard (<= instidx (elab-mod-ninsts elab-mod))
  (if (>= (lnfix instidx) (elab-mod-ninsts elab-mod))
      (elab-mod->totalwires elab-mod)
    (elab-mod->inst-wireoffset instidx elab-mod))
  ///
  (defthmd elab-mod-inst-wireoffset-norm
    (implies (< (nfix instidx) (elab-mod$a-ninsts elab-mod))
             (equal (elab-mod$a->inst-wireoffset instidx elab-mod)
                    (elab-mod-wireoffset instidx elab-mod))))

  (defthmd elab-mod-totalwires-norm
    (nat-equiv (g :totalwires elab-mod)
               (elab-mod-wireoffset (elab-mod-ninsts elab-mod) elab-mod)))

  (deffixequiv elab-mod-wireoffset))

(define elab-mod-instoffset ((instidx natp) elab-mod)
  :guard (<= instidx (elab-mod-ninsts elab-mod))
  (if (>= (lnfix instidx) (elab-mod-ninsts elab-mod))
      (elab-mod->totalinsts elab-mod)
    (elab-mod->inst-instoffset instidx elab-mod))
  ///
  (defthmd elab-mod-inst-instoffset-norm
    (implies (< (nfix instidx) (elab-mod$a-ninsts elab-mod))
             (equal (elab-mod$a->inst-instoffset instidx elab-mod)
                    (elab-mod-instoffset instidx elab-mod))))

  (defthmd elab-mod-totalinsts-norm
    (equal (elab-mod$a->totalinsts elab-mod)
           (elab-mod-instoffset (elab-mod-ninsts elab-mod) elab-mod))))

(defsection moddb-mod-inst-wire/instoffset
  (define moddb-mod-inst-wireoffset ((instidx natp)
                                     (modidx natp)
                                     moddb)
    :guard (and (< modidx (moddb->nmods moddb))
                (<= (moddb->nmods moddb) (moddb->mods-length moddb))
                (moddb-mod-order-ok modidx moddb)
                (stobj-let ((elab-mod (moddb->modsi modidx moddb)))
                           (ok)
                           (<= instidx (elab-mod-ninsts elab-mod))
                           ok))
    :returns (offset natp :rule-classes :type-prescription)
    (b* (((unless (mbt (< (lnfix modidx) (lnfix (moddb->nmods moddb))))) 0)
         (instidx (mbe :logic (min (nfix instidx)
                                   (stobj-let ((elab-mod (moddb->modsi modidx moddb)))
                                              (ninsts)
                                              (elab-mod-ninsts elab-mod)
                                              ninsts))
                       :exec instidx))
         ((when (zp instidx))
          (b* (((stobj-get nwires)
                ((elab-mod (moddb->modsi modidx moddb)))
                (elab-mod-nwires elab-mod)))
            nwires))
         (prev-instidx (1- instidx))
         ((stobj-get prevoffset instmod)
          ((elab-mod (moddb->modsi modidx moddb)))
          (mv (elab-mod->inst-wireoffset prev-instidx elab-mod)
              (elab-mod->inst-modidx prev-instidx elab-mod)))
         ((unless (mbt (< instmod (lnfix modidx)))) prevoffset)
         ((stobj-get inst-totalwires)
          ((elab-mod (moddb->modsi instmod moddb)))
          (elab-mod->totalwires elab-mod)))
      (+ prevoffset inst-totalwires))
    ///
    (deffixequiv moddb-mod-inst-wireoffset
      :hints(("Goal" :in-theory (disable elab-mod$a->totalinsts
                                         elab-mod$a->totalwires))))

    (fty::deffixcong moddb-norm-equiv equal (moddb-mod-inst-wireoffset idx modidx moddb) moddb))

  (define moddb-mod-inst-instoffset ((instidx natp)
                                     (modidx natp)
                                     moddb)
    :guard (and (< modidx (moddb->nmods moddb))
                (<= (moddb->nmods moddb) (moddb->mods-length moddb))
                (moddb-mod-order-ok modidx moddb)
                (stobj-let ((elab-mod (moddb->modsi modidx moddb)))
                           (ok)
                           (<= instidx (elab-mod-ninsts elab-mod))
                           ok))
    :returns (offset natp :rule-classes :type-prescription)
    (b* (((unless (mbt (< (lnfix modidx) (lnfix (moddb->nmods moddb))))) 0)
         (instidx (mbe :logic (min (nfix instidx)
                                   (stobj-let ((elab-mod (moddb->modsi modidx moddb)))
                                              (ninsts)
                                              (elab-mod-ninsts elab-mod)
                                              ninsts))
                       :exec instidx))
         ((when (zp instidx)) 0)
         (prev-instidx (1- instidx))
         ((stobj-get prevoffset instmod)
          ((elab-mod (moddb->modsi modidx moddb)))
          (mv (elab-mod->inst-instoffset prev-instidx elab-mod)
              (elab-mod->inst-modidx prev-instidx elab-mod)))
         ((unless (mbt (< instmod (lnfix modidx)))) (+ 1 prevoffset))
         ((stobj-get inst-totalinsts)
          ((elab-mod (moddb->modsi instmod moddb)))
          (elab-mod->totalinsts elab-mod)))
      (+ 1 prevoffset inst-totalinsts))
    ///
    (deffixequiv moddb-mod-inst-instoffset
      :hints(("Goal" :in-theory (disable elab-mod$a->totalinsts
                                         elab-mod$a->totalinsts))))

    (fty::deffixcong moddb-norm-equiv equal (moddb-mod-inst-instoffset idx modidx moddb) moddb)))



(defsection moddb-mod-insts-ok
  (define moddb-modinst-ok ((instidx natp)
                            (modidx natp)
                            moddb)
    :guard (and (< modidx (moddb->nmods moddb))
                (<= (moddb->nmods moddb) (moddb->mods-length moddb))
                (moddb-mod-order-ok modidx moddb)
                (stobj-let ((elab-mod (moddb->modsi modidx moddb)))
                           (ok)
                           (< instidx (elab-mod-ninsts elab-mod))
                           ok))
    (b* (((unless (mbt (and (< (lnfix modidx) (lnfix (moddb->nmods moddb)))
; (< (lnfix modidx) (moddb->mods-length moddb))
                            (stobj-let ((elab-mod (moddb->modsi modidx moddb)))
                                       (ok)
                                       (< (lnfix instidx) (elab-mod-ninsts elab-mod))
                                       ok))))
          t)
         ((stobj-get instname wireoffset instoffset)
          ((elab-mod (moddb->modsi modidx moddb)))
          (mv (elab-mod->instname instidx elab-mod)
              (elab-mod->inst-wireoffset instidx elab-mod)
              (elab-mod->inst-instoffset instidx elab-mod)))
         (wireoffset-spec (moddb-mod-inst-wireoffset instidx modidx moddb))
         (instoffset-spec (moddb-mod-inst-instoffset instidx modidx moddb))
         ((unless (eql wireoffset wireoffset-spec))
          (cw "Bad wire offset in ~s0: ~x1, should be ~x2~%" instname wireoffset wireoffset-spec))
         ((unless (eql instoffset instoffset-spec))
          (cw "Bad inst offset in ~s0: ~x1, should be ~x2~%" instname instoffset instoffset-spec)))
      t)
    ///
    (deffixequiv moddb-modinst-ok
      :hints(("Goal" :in-theory (disable elab-mod$a->totalinsts
                                         elab-mod$a->totalwires))))

    (defthm moddb-modinst-ok-implies-instoffset
      (implies (and (moddb-modinst-ok instidx modidx moddb)
                    (< (nfix modidx) (nfix (nth *moddb->nmods* moddb)))
                    (< (nfix instidx) (elab-mod$a-ninsts (nth modidx (nth *moddb->modsi* moddb)))))
               (EQUAL
                (ELAB-MOD$A->INST-INSTOFFSET instidx
                                             (NTH MODIDX (NTH *MODDB->MODSI* MODDB)))
                (moddb-mod-inst-instoffset instidx modidx moddb))))

    (defthm moddb-modinst-ok-implies-wireoffset
      (implies (and (moddb-modinst-ok instidx modidx moddb)
                    (< (nfix modidx) (nfix (nth *moddb->nmods* moddb)))
                    (< (nfix instidx) (elab-mod$a-ninsts (nth modidx (nth *moddb->modsi* moddb)))))
               (EQUAL
                (ELAB-MOD$A->INST-wireOFFSET instidx
                                             (NTH MODIDX (NTH *MODDB->MODSI* MODDB)))
                (moddb-mod-inst-wireoffset instidx modidx moddb))))

    (fty::deffixcong moddb-norm-equiv equal (moddb-modinst-ok idx modidx moddb) moddb))

  (define moddb-find-bad-modinst ((n natp) (modidx natp) moddb)
    :returns (idx (iff (natp idx) idx))
    :guard (and (< modidx (moddb->nmods moddb))
                (<= (moddb->nmods moddb) (moddb->mods-length moddb))
                (moddb-mod-order-ok modidx moddb)
                (stobj-let ((elab-mod (moddb->modsi modidx moddb)))
                           (ok)
                           (<= n (elab-mod-ninsts elab-mod))
                           ok))
    (if (zp n)
        nil
      (if (moddb-modinst-ok (1- n) modidx moddb)
          (moddb-find-bad-modinst (1- n) modidx moddb)
        (1- n)))
    ///
    (deffixequiv moddb-find-bad-modinst)

    (defthm moddb-find-bad-modinst-bound-weak
      (<= (moddb-find-bad-modinst n modidx moddb) (nfix n))
      :rule-classes :linear)
    (defthm moddb-find-bad-modinst-bound
      (implies (moddb-find-bad-modinst n modidx moddb)
               (< (moddb-find-bad-modinst n modidx moddb) (nfix n)))
      :rule-classes :linear)

    (defthm moddb-find-bad-modinst-is-bad
      (implies (moddb-find-bad-modinst n modidx moddb)
               (not (moddb-modinst-ok
                     (moddb-find-bad-modinst n modidx moddb)
                     modidx moddb))))

    (defthm moddb-find-bad-modinst-finds-bad
      (implies (and (not (moddb-modinst-ok idx modidx moddb))
                    (< (nfix idx) (nfix n)))
               (and (moddb-find-bad-modinst n modidx moddb)
                    (not (moddb-modinst-ok
                          (moddb-find-bad-modinst n modidx moddb)
                          modidx moddb))))))

  (define moddb-mod-insts-ok ((modidx natp) moddb)
    :guard (and (< modidx (moddb->nmods moddb))
                (<= (moddb->nmods moddb) (moddb->mods-length moddb))
                (moddb-mod-order-ok modidx moddb))
    (b* (((unless (mbt (< (lnfix modidx) (lnfix (moddb->nmods moddb))))) t)
         ((stobj-get ninsts)
          ((elab-mod (moddb->modsi modidx moddb)))
          (elab-mod-ninsts elab-mod)))
      (not (moddb-find-bad-modinst ninsts modidx moddb)))
    ///
    (deffixequiv moddb-mod-insts-ok)

    (defthm moddb-mod-insts-ok-implies
      (implies (and (moddb-mod-insts-ok modidx moddb)
                    ;; (< (nfix modidx) (len (nth *moddb->modsi* moddb) ))
                    (< (nfix modidx) (nfix (nth *moddb->nmods* moddb)))
                    (< (nfix idx) (elab-mod$a-ninsts
                                   (nth modidx (nth *moddb->modsi* moddb)))))
               (moddb-modinst-ok idx modidx moddb))
      :hints (("goal" :use ((:instance moddb-find-bad-modinst-finds-bad
                             (n (elab-mod-ninsts (moddb->modsi modidx moddb)))))
               :in-theory (disable moddb-find-bad-modinst-finds-bad))))

    (define moddb-modinst-badguy ((modidx natp) moddb)
      :non-executable t
      :verify-guards nil
      (let ((moddb (moddb-fix moddb)))
        (moddb-find-bad-modinst (elab-mod-ninsts (moddb->modsi modidx moddb)) modidx moddb))
      ///
      (deffixequiv moddb-modinst-badguy)

      (defthmd moddb-mod-insts-not-ok
        (implies (acl2::rewriting-positive-literal
                  `(moddb-mod-insts-ok ,modidx ,moddb))
                 (equal (moddb-mod-insts-ok modidx moddb)
                        (let ((idx (moddb-modinst-badguy modidx moddb)))
                          (or (>= (nfix idx) (elab-mod$a-ninsts
                                              (nth modidx (nth *moddb->modsi* moddb))))
                              (>= (nfix modidx) (nfix (nth *moddb->nmods* moddb)))
                              (moddb-modinst-ok idx modidx moddb)))))
        :hints (("goal" :use ((:instance moddb-find-bad-modinst-finds-bad
                               (n (elab-mod-ninsts (moddb->modsi modidx moddb)))
                               (idx 0)))
                 :in-theory (disable moddb-find-bad-modinst-finds-bad))
                (and stable-under-simplificationp
                     '(:expand ((moddb-modinst-ok 0 modidx moddb)
                                (moddb-find-bad-modinst 0 modidx moddb)))))))


    (fty::deffixcong moddb-norm-equiv equal (moddb-mod-insts-ok modidx moddb) moddb
      :hints(("Goal" :in-theory (e/d ()
                                     (moddb-mod-insts-ok))
              :cases ((moddb-mod-insts-ok modidx moddb)))
             (and stable-under-simplificationp
                  '(:in-theory (e/d (moddb-mod-insts-not-ok)
                                    (moddb-mod-insts-ok))))
             (and stable-under-simplificationp
                  '(:use ((:instance moddb-mod-insts-ok-implies
                           (idx (moddb-modinst-badguy modidx moddb))
                           (moddb (moddb-norm moddb))))
                    :in-theory (disable moddb-mod-insts-ok
                                        moddb-mod-insts-ok-implies)))))))

(defsection moddb-mods-ok
  (define moddb-mod-ok ((modidx natp) moddb)
    :guard (and (< modidx (moddb->nmods moddb))
                (<= (moddb->nmods moddb) (moddb->mods-length moddb)))
    (b* (((unless (moddb-mod-order-ok modidx moddb)) nil)
         ((unless (moddb-mod-insts-ok modidx moddb)) nil)
         ((unless (mbt (< (lnfix modidx) (lnfix (moddb->nmods moddb))))) t)
         ((stobj-get totwires totinsts ninsts)
          ((elab-mod (moddb->modsi modidx moddb)))
          (mv (elab-mod->totalwires elab-mod)
              (elab-mod->totalinsts elab-mod)
              (elab-mod-ninsts elab-mod)))
         (totwires-spec (moddb-mod-inst-wireoffset ninsts modidx moddb))
         (totinsts-spec (moddb-mod-inst-instoffset ninsts modidx moddb)))
      (and (equal totwires-spec totwires)
           (equal totinsts-spec totinsts)))
    ///
    (defthm moddb-mod-ok-implies-order-ok
      (implies (moddb-mod-ok modidx moddb)
               (moddb-mod-order-ok modidx moddb)))

    (defthm moddb-mod-ok-implies-modinsts-ok
      (implies (moddb-mod-ok modidx moddb)
               (moddb-mod-insts-ok modidx moddb)))

    (defthm moddb-mod-ok-implies-totalwires
      (implies (and (moddb-mod-ok modidx moddb)
                    (< (lnfix modidx) (lnfix (moddb->nmods moddb))))
               (nat-equiv (g :totalwires (nth modidx (nth *moddb->modsi* moddb)))
                          (moddb-mod-inst-wireoffset
                           (elab-mod$a-ninsts (nth modidx (nth *moddb->modsi* moddb)))
                           modidx moddb))))

    (defthm moddb-mod-ok-implies-totalinsts
      (implies (and (moddb-mod-ok modidx moddb)
                    (< (lnfix modidx) (lnfix (moddb->nmods moddb))))
               (nat-equiv (g :totalinsts (nth modidx (nth *moddb->modsi* moddb)))
                          (moddb-mod-inst-instoffset
                           (elab-mod$a-ninsts (nth modidx (nth *moddb->modsi* moddb)))
                           modidx moddb))))

    (defthm moddb-mod-inst-wireoffset-greater-norm
      (implies (and (<= (elab-mod$a-ninsts (nth modidx (nth *moddb->modsi* moddb)))
                        (nfix instidx))
                    (equal newidx (elab-mod$a-ninsts (nth modidx (nth *moddb->modsi* moddb))))
                    (equal oldidx (nfix instidx))
                    (syntaxp (not (equal oldidx newidx))))
               (equal (moddb-mod-inst-wireoffset instidx modidx moddb)
                      (moddb-mod-inst-wireoffset newidx modidx moddb)))
      :hints ((and stable-under-simplificationp (equal (car id) '(0))
                   '(:induct (count-down instidx (elab-mod$a-ninsts
                                                  (nth modidx (nth *moddb->modsi* moddb))))
                     :expand ((moddb-mod-inst-wireoffset instidx modidx moddb)
                              (moddb-mod-inst-wireoffset newidx modidx moddb)
                              (moddb-mod-inst-wireoffset (+ -1 instidx) modidx moddb)
                              (moddb-mod-inst-wireoffset 0 modidx moddb))))))

    (defthm moddb-mod-inst-instoffset-greater-norm
      (implies (and (<= (elab-mod$a-ninsts (nth modidx (nth *moddb->modsi* moddb)))
                        (nfix instidx))
                    (equal newidx (nfix (elab-mod$a-ninsts (nth modidx (nth *moddb->modsi* moddb)))))
                    (equal oldidx (nfix instidx))
                    (syntaxp (not (equal oldidx newidx))))
               (equal (moddb-mod-inst-instoffset instidx modidx moddb)
                      (moddb-mod-inst-instoffset newidx modidx moddb)))
      :hints ((and stable-under-simplificationp (equal (car id) '(0))
                   '(:induct (count-down instidx (elab-mod$a-ninsts
                                                  (nth modidx (nth *moddb->modsi* moddb))))
                     :expand ((moddb-mod-inst-instoffset instidx modidx moddb)
                              (moddb-mod-inst-instoffset newidx modidx moddb)
                              (moddb-mod-inst-instoffset (+ -1 instidx) modidx moddb)
                              (moddb-mod-inst-instoffset 0 modidx moddb))))))

    (defthm moddb-mod-ok-implies-wire-offset
      (implies (and (moddb-mod-ok modidx moddb)
                    (< (lnfix modidx) (lnfix (moddb->nmods moddb))))
               (equal (elab-mod-wireoffset instidx (nth modidx (nth *moddb->modsi* moddb)))
                      (moddb-mod-inst-wireoffset instidx modidx moddb)))
      :hints(("Goal" :in-theory (e/d (elab-mod-wireoffset)
                                     (moddb-mod-ok)))))

    (defthm moddb-mod-ok-implies-inst-offset
      (implies (and (moddb-mod-ok modidx moddb)
                    (< (lnfix modidx) (lnfix (moddb->nmods moddb))))
               (equal (elab-mod-instoffset instidx (nth modidx (nth *moddb->modsi* moddb)))
                      (moddb-mod-inst-instoffset instidx modidx moddb)))
      :hints(("Goal" :in-theory (e/d (elab-mod-instoffset)
                                     (moddb-mod-ok)))))

    (deffixequiv moddb-mod-ok
      :hints(("Goal" :in-theory (disable elab-mod$a->totalinsts
                                         elab-mod$a->totalwires))))

    (fty::deffixcong moddb-norm-equiv equal (moddb-mod-ok modidx moddb) moddb))

  (define moddb-find-bad-mod ((n natp) moddb)
    :returns (idx (iff (natp idx) idx))
    :guard (and (<= n (moddb->nmods moddb))
                (<= (moddb->nmods moddb) (moddb->mods-length moddb)))
    (if (zp n)
        nil
      (if (moddb-mod-ok (1- n) moddb)
          (moddb-find-bad-mod (1- n) moddb)
        (1- n)))
    ///
    (deffixequiv moddb-find-bad-mod)

    (defthm moddb-find-bad-mod-bound-weak
      (<= (moddb-find-bad-mod n moddb) (nfix n))
      :rule-classes :linear)

    (defthm moddb-find-bad-mod-bound
      (implies (moddb-find-bad-mod n moddb)
               (< (moddb-find-bad-mod n moddb) (nfix n)))
      :rule-classes :linear)

    (defthm moddb-find-bad-mod-nmods-bound
      (implies (moddb-find-bad-mod n moddb)
               (< (moddb-find-bad-mod n moddb) (nfix (nth *moddb->nmods* moddb))))
      :hints (("goal" :induct t)
              (and stable-under-simplificationp
                   '(:in-theory (enable moddb-mod-ok
                                        moddb-mod-insts-not-ok
                                        moddb-mod-order-not-ok))))
      :rule-classes :linear)

    (defthm moddb-find-bad-mod-is-bad
      (implies (moddb-find-bad-mod n moddb)
               (not (moddb-mod-ok
                     (moddb-find-bad-mod n moddb) moddb))))

    (defthm moddb-find-bad-mod-finds-bad
      (implies (and (not (moddb-mod-ok idx moddb))
                    (< (nfix idx) (nfix n)))
               (and (moddb-find-bad-mod n moddb)
                    (not (moddb-mod-ok
                          (moddb-find-bad-mod n moddb) moddb))))))

  (define moddb-mods-ok (moddb)
    :guard (<= (moddb->nmods moddb) (moddb->mods-length moddb))
    (not (moddb-find-bad-mod (moddb->nmods moddb) moddb))
    ///
    (deffixequiv moddb-mods-ok)

    (defthm moddb-mods-ok-implies
      (implies (moddb-mods-ok moddb)
               (moddb-mod-ok idx moddb))
      :hints (("goal" :use ((:instance moddb-find-bad-mod-finds-bad
                             (n (moddb->nmods moddb))))
               :in-theory (disable moddb-find-bad-mod-finds-bad))
              (and stable-under-simplificationp
                   '(:in-theory (enable moddb-mod-ok
                                        moddb-mod-insts-not-ok
                                        moddb-mod-order-not-ok)))))

    (define moddb-mod-badguy (moddb)
      :non-executable t
      :verify-guards nil
      (let ((moddb (moddb-fix moddb)))
        (moddb-find-bad-mod (moddb->nmods moddb) moddb))
      ///
      (deffixequiv moddb-mod-badguy)

      (defthmd moddb-mods-not-ok
        (implies (acl2::rewriting-positive-literal
                  `(moddb-mods-ok ,moddb))
                 (equal (moddb-mods-ok moddb)
                        (let ((idx (moddb-mod-badguy moddb)))
                          (or (>= (nfix idx) (nfix (nth *moddb->nmods* moddb)))
                              (moddb-mod-ok idx moddb)))))
        :hints (("goal" :use ((:instance moddb-find-bad-mod-finds-bad
                               (n (moddb->nmods moddb))
                               (idx 0)))
                 :expand ((:free (x) (hide x)))
                 :in-theory (disable moddb-find-bad-mod-finds-bad))
                (and stable-under-simplificationp
                     '(:expand ((moddb-find-bad-mod (nth *moddb->nmods* moddb) moddb)))))))

    (fty::deffixcong moddb-norm-equiv equal (moddb-mods-ok moddb) moddb
      :hints (("goal" :in-theory (disable moddb-mods-ok)
               :cases ((moddb-mods-ok moddb)))
              (and stable-under-simplificationp
                   '(:in-theory (e/d (moddb-mods-not-ok)
                                     (moddb-mods-ok))))
              (and stable-under-simplificationp
                   '(:use ((:instance moddb-mods-ok-implies
                            (moddb (moddb-norm moddb))
                            (idx (moddb-mod-badguy moddb))))
                     :in-theory (disable moddb-mods-ok-implies
                                         moddb-mods-ok))))))

  (define moddb-ok ((moddb moddbp))
    :enabled t
    (and (moddb-basics-ok moddb)
         (moddb-mods-ok moddb))
    ///
    (deffixequiv moddb-ok)))

(define moddb-clear (moddb)
  :returns (moddb1 (and (moddb-mods-ok moddb1)
                        (moddb-basics-ok moddb1))
                   :hints(("Goal" :in-theory (enable moddb-mods-ok
                                                     moddb-basics-ok
                                                     moddb-find-bad-mod
                                                     moddb-indices-ok
                                                     moddb-find-bad-index))))
  (b* ((moddb (moddb->modname-idxes-clear moddb))
       (moddb (update-moddb->nmods 0 moddb)))
    (resize-moddb->mods 0 moddb))
  ///
  (defthm moddb-clear-normalize
    (implies (syntaxp (not (equal moddb ''nil)))
             (equal (moddb-clear moddb)
                    (moddb-clear nil)))
    :hints(("Goal" :in-theory (e/d (moddb-fix) ((moddb-fix)))))))

(define moddb-maybe-grow (moddb)
  (b* ((moddb (moddb-fix moddb))
       (idx (lnfix (moddb->nmods moddb))))
    (if (<= (moddb->mods-length moddb) idx)
        (resize-moddb->mods (max 16 (* 2 idx))
                            moddb)
      moddb))
  ///

  (deffixequiv moddb-maybe-grow)



  (defthm elab-mods->names-of-replicate
    (equal (elab-mods->names (replicate n x))
           (replicate n (modname-fix (g :name x))))
    :hints(("Goal" :in-theory (enable replicate elab-mods->names))))

  (defthm elab-mods->names-of-resize-list
    (equal (elab-mods->names (resize-list lst n d))
           (resize-list (elab-mods->names lst) n (modname-fix (g :name d))))
    :hints(("Goal" :in-theory (enable elab-mods->names))))

  (local (defun ind (n m lst)
           (if (zp n)
               (list m lst)
             (ind (1- n) (1- m) (cdr lst)))))

  (defthm take-of-resize-under-elab-modlist-equiv
    (implies (and (<= (nfix n) (nfix m))
                  (elab-mod$a-equiv d nil))
             (elab-modlist-equiv (take n (resize-list lst m d))
                                 (take n lst)))
    :hints (("goal" :induct (ind n m lst)
             :in-theory (enable acl2::take elab-mods->names))))


  (defthm moddb-maybe-grow-under-moddb-norm-equiv
    (moddb-norm-equiv (moddb-maybe-grow moddb)
                      moddb)
    :hints(("Goal" :in-theory (enable moddb-norm))))

  ;; is this needed?
  (fty::deffixcong moddb-norm-equiv moddb-norm-equiv (moddb-maybe-grow moddb) moddb)

  (defthm moddb-basics-ok-of-moddb-maybe-grow
    (implies (moddb-basics-ok moddb)
             (moddb-basics-ok (moddb-maybe-grow moddb)))
    :hints(("Goal" :in-theory (enable moddb-basics-ok
                                      moddb-indices-not-ok))))

  (defthm moddb-maybe-grow-frame
    (implies (not (equal (nfix n) *moddb->modsi*))
             (equal (nth n (moddb-maybe-grow moddb))
                    (nth n (moddb-fix moddb)))))

  (defthm len-mods-of-moddb-maybe-grow
    (< (nfix (nth *moddb->nmods* moddb))
       (len (nth *moddb->modsi* (moddb-maybe-grow moddb))))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable nfix))))
    :rule-classes :linear))

(define elab-mod-fix (elab-mod)
  :enabled t
  :inline t
  (mbe :logic (non-exec (elab-mod$a-fix elab-mod))
       :exec elab-mod))

(define moddb-modname-get-index ((name modname-p) moddb)
  :guard (moddb-basics-ok moddb)
  :returns (idx (iff (natp idx) idx)
                :hints(("Goal" :in-theory (enable moddb-norm)))
                :rule-classes (:rewrite
                               (:type-prescription
                                :corollary (maybe-natp (moddb-modname-get-index name moddb)))))
  (mbe :logic (non-exec
               (moddb->modname-idxes-get
                (modname-fix name) (moddb-norm moddb)))
       :exec (moddb->modname-idxes-get name moddb))
  ///
  (deffixequiv moddb-modname-get-index)

  (fty::deffixcong moddb-norm-equiv equal (moddb-modname-get-index name moddb) moddb)

  (defthm modbb-modname-get-index-type
    (or (natp (moddb-modname-get-index name moddb))
        (not (moddb-modname-get-index name moddb)))
    :rule-classes :type-prescription)

  (defthm moddb-modname-get-index-bound
    (implies (moddb-modname-get-index name moddb)
             (< (moddb-modname-get-index name moddb)
                (nfix (nth *moddb->nmods* moddb))))
    :hints(("Goal" :in-theory (enable moddb-norm)))
    :rule-classes :linear))

(define moddb-modidx-get-name ((idx natp) moddb)
  :guard (and (moddb-basics-ok moddb)
              (< idx (moddb->nmods moddb)))
  :guard-hints (("goal" :in-theory (enable moddb-basics-ok)))
  (b* (((stobj-get name)
        ((elab-mod (moddb->modsi idx moddb)))
        (elab-mod->name elab-mod)))
    name))

(defsection moddb-add-module
  (define moddb-add-module1 (elab-mod moddb)
    :returns (mv elab-mod1 moddb1)
    :guard (and (moddb-basics-ok moddb)
                (< (moddb->nmods moddb) (moddb->mods-length moddb))
                (not (moddb-modname-get-index (elab-mod->name elab-mod) moddb)))
    (b* ((moddb (moddb-fix moddb))
         (elab-mod (elab-mod-fix elab-mod))
         ((unless (mbt (not (moddb-modname-get-index (elab-mod->name elab-mod) moddb))))
          (mv elab-mod moddb))
         (idx (lnfix (moddb->nmods moddb)))
         (moddb (update-moddb->nmods (+ 1 idx) moddb))
         (moddb (moddb->modname-idxes-put (elab-mod->name elab-mod) idx moddb)))
      (stobj-let ((new-elab-mod (moddb->modsi idx moddb)))
                 (new-elab-mod elab-mod)
                 (swap-elab-mods new-elab-mod elab-mod)
                 (mv elab-mod moddb)))
    ///
    (deffixequiv moddb-add-module1)

    (local (defthm update-nth-of-take-length+1
             (equal (update-nth n v (take (+ 1 (nfix n)) x))
                    (take (+ 1 (nfix n)) (update-nth n v x)))
             :hints(("Goal" :in-theory (enable update-nth)))))

    (local (defthm update-nth-of-take-length
             (equal (update-nth n v (take n x))
                    (take (+ 1 (nfix n)) (update-nth n v x)))
             :hints(("Goal" :in-theory (e/d (acl2::take update-nth))))))

    (local (in-theory (disable acl2::take
                               acl2::take-of-update-nth
                               acl2::take-after-update-nth)))

    (fty::deffixcong moddb-norm-equiv moddb-norm-equiv
      (mv-nth 1 (moddb-add-module1 elab-mod moddb))
      moddb
      :hints((and stable-under-simplificationp
                  '(:in-theory (e/d (moddb-norm))))))

    (local (defthmd my-open-take
             (equal (take n x)
                    (if (zp n)
                        nil
                      (cons (car x) (take (1- n) (cdr x)))))
             :hints(("Goal" :in-theory (enable acl2::take)))
             :rule-classes ((:definition :controller-alist ((take t nil))))))

    (local (defun ind (n m mods)
             (if (zp m)
                 (list n mods)
               (ind (1- n) (1- m) (cdr mods)))))

    (local (defthm name-of-nth-when-not-member
             (implies (and (not (member name (take n (elab-mods->names mods))))
                           (< (nfix m) (nfix n))
                           (<= (nfix n) (len mods)))
                      (not (equal (modname-fix (g :name (nth m mods))) name)))
             :hints (("goal" :use ((:instance acl2::member-of-nth
                                    (acl2::n m) (x (take n (elab-mods->names mods)))))
                      :in-theory (disable acl2::member-of-nth)))))

    (defthm take-of-n+1-update-nth
      (equal (take (+ 1 (nfix n)) (update-nth n v x))
             (append (take n x) (list v)))
      :hints(("Goal" :in-theory (enable update-nth my-open-take))))

    (defthmd moddb-add-module1-under-moddb-norm-equiv
      (moddb-norm-equiv (mv-nth 1 (moddb-add-module1 elab-mod moddb))
                        (if (moddb-modname-get-index (g :name elab-mod) moddb)
                            moddb
                          (list (+ 1 (nfix (nth *moddb->nmods* moddb)))
                                (append (take (nth *moddb->nmods* moddb)
                                              (nth *moddb->modsi* moddb))
                                        (list elab-mod)))))
      :hints(("Goal" :in-theory (e/d (moddb-norm) (acl2::numlist)))))

    (local (in-theory (enable moddb-add-module1-under-moddb-norm-equiv)))

    (defthm moddb-basics-ok-of-moddb-add-module1
      (implies (and (moddb-basics-ok moddb)
                    (< (nfix (moddb->nmods moddb))
                       (moddb->mods-length moddb)))
               (moddb-basics-ok
                (mv-nth 1 (moddb-add-module1 elab-mod moddb))))
      :hints((and stable-under-simplificationp
                  '(:in-theory (enable moddb-basics-ok)))
             (and stable-under-simplificationp
                  '(:in-theory (enable moddb-indices-not-ok
                                       moddb-modname-get-index
                                       moddb-norm)
                    :cases ((member (modname-fix (g :name elab-mod))
                                    (elab-mods->names
                                     (nth *moddb->modsi* (moddb-norm moddb)))))))
             (and stable-under-simplificationp
                  '(:use ((:instance lookup-name-in-moddb-norm
                           (name (modname-fix (g :name elab-mod)))))
                    :in-theory (e/d (moddb-basics-ok moddb-norm)
                                    (lookup-name-in-moddb-norm))))))

    (local (in-theory (disable acl2::zp-open)))

    (defthm moddb-mod-inst-wireoffset-of-update-nmods
      (implies (and (< (nfix modidx) (nfix (nth *moddb->nmods* moddb)))
                    (<= (nfix (nth *moddb->nmods* moddb)) (nfix newnmods)))
               (equal (moddb-mod-inst-wireoffset inst modidx
                                                 (update-nth *moddb->nmods* newnmods moddb))
                      (moddb-mod-inst-wireoffset inst modidx moddb)))
      :hints(("Goal" :in-theory (enable moddb-mod-inst-wireoffset))))

    (defthm moddb-mod-inst-wireoffset-of-update-mod
      (implies (< (nfix modidx) (nfix updidx))
               (equal (moddb-mod-inst-wireoffset inst modidx
                                                 (update-nth *moddb->modsi*
                                                             (update-nth updidx newmod mods)
                                                             moddb))
                      (moddb-mod-inst-wireoffset inst modidx
                                                 (update-nth *moddb->modsi*
                                                             mods moddb))))
      :hints(("Goal" :in-theory (enable moddb-mod-inst-wireoffset))))

    (defthm moddb-mod-inst-wireoffset-of-update-table
      (equal (moddb-mod-inst-wireoffset inst modidx
                                        (update-nth *moddb->modname-idxes-get*
                                                    tab moddb))
             (moddb-mod-inst-wireoffset inst modidx moddb))
      :hints(("Goal" :in-theory (enable moddb-mod-inst-wireoffset))))

    (defthm moddb-mod-inst-instoffset-of-update-nmods
      (implies (and (< (nfix modidx) (nfix (nth *moddb->nmods* moddb)))
                    (<= (nfix (nth *moddb->nmods* moddb)) (nfix newnmods)))
               (equal (moddb-mod-inst-instoffset inst modidx
                                                 (update-nth *moddb->nmods* newnmods moddb))
                      (moddb-mod-inst-instoffset inst modidx moddb)))
      :hints(("Goal" :in-theory (enable moddb-mod-inst-instoffset))))

    (defthm moddb-mod-inst-instoffset-of-update-mod
      (implies (< (nfix modidx) (nfix updidx))
               (equal (moddb-mod-inst-instoffset inst modidx
                                                 (update-nth *moddb->modsi*
                                                             (update-nth updidx newmod mods)
                                                             moddb))
                      (moddb-mod-inst-instoffset inst modidx
                                                 (update-nth *moddb->modsi*
                                                             mods moddb))))
      :hints(("Goal" :in-theory (enable moddb-mod-inst-instoffset))))

    (defthm moddb-mod-inst-instoffset-of-update-table
      (equal (moddb-mod-inst-instoffset inst modidx
                                        (update-nth *moddb->modname-idxes-get*
                                                    tab moddb))
             (moddb-mod-inst-instoffset inst modidx moddb))
      :hints(("Goal" :in-theory (enable moddb-mod-inst-instoffset))))

    (local (defthm update-nth-of-nth-when-redundant
             (and (implies (equal a (nth n b))
                           (moddb-equiv (update-nth n a b)
                                        b))
                  (moddb-equiv (update-nth n (nth n b) b)
                               b))
             :hints(("Goal" :in-theory (enable moddb-fix)))))

    (defthm moddb-mods-ok-of-moddb-add-module1-empty
      (implies (and (moddb-mods-ok moddb)
                    (equal 0 (elab-mod$a-ninsts elab-mod))
                    (equal (elab-mod$a-nwires elab-mod)
                           (nfix (g :totalwires elab-mod)))
                    (zp (g :totalinsts elab-mod)))
               (moddb-mods-ok (mv-nth 1 (moddb-add-module1 elab-mod moddb))))
      :hints((and stable-under-simplificationp
                  '(:in-theory (enable moddb-mods-not-ok
                                       moddb-mod-ok)))
             (and stable-under-simplificationp
                  '(:in-theory (enable moddb-mod-insts-not-ok
                                       moddb-modinst-ok
                                       moddb-mod-order-not-ok
                                       moddb-modinst-order-ok)))
             (and stable-under-simplificationp
                  '(:expand ((:free (modidx moddb) (moddb-mod-inst-wireoffset 0 modidx moddb))
                             (:free (modidx moddb) (moddb-mod-inst-instoffset 0 modidx moddb))))))
      :otf-flg t)

    (defthm elab-mods->names-of-append
      (equal (elab-mods->names (append a b))
             (append (elab-mods->names a) (elab-mods->names b)))
      :hints(("Goal" :in-theory (enable elab-mods->names))))

    (local (Defthm acl2-numberp-index-of
             (iff (acl2-numberp (index-of n x))
                  (index-of n x))
             :hints (("goal" :in-theory (enable index-of)))))


    (defthmd index-of-append
      (equal (index-of k (append a b))
             (or (index-of k a)
                 (let ((bind (index-of k b)))
                   (and bind (+ (len a) bind)))))
      :hints(("Goal" :in-theory (enable index-of))))

    (defthmd index-of-cons
      (equal (index-of k (cons a b))
             (if (equal k a)
                 0
               (let ((bind (index-of k b)))
                 (and bind (+ 1 bind)))))
      :hints(("Goal" :in-theory (enable index-of))))

    (defthm moddb-modname-get-index-of-moddb-add-module1
      (equal (moddb-modname-get-index name (mv-nth 1 (moddb-add-module1 elab-mod moddb)))
             (or (moddb-modname-get-index name moddb)
                 (and (equal (modname-fix name) (modname-fix (g :name elab-mod)))
                      (nfix (nth *moddb->nmods* moddb)))))
      :hints(("Goal" :in-theory (e/d (moddb-modname-get-index)
                                     (moddb-add-module1 acl2::numlist)))
             (and stable-under-simplificationp
                  '(:in-theory (e/d (moddb-norm
                                     index-of-append
                                     index-of-cons
                                     elab-mods->names)
                                    (acl2::numlist))))))

    (defthm nmods-of-moddb-add-module1
      (implies (not (moddb-modname-get-index (g :name elab-mod) moddb))
               (equal (nth *moddb->nmods* (mv-nth 1 (moddb-add-module1 elab-mod moddb)))
                      (+ 1 (nfix (moddb->nmods moddb)))))))

  (define moddb-add-module (elab-mod (moddb moddbp))
    :enabled t
    :guard (and (moddb-ok moddb)
                (not (moddb-modname-get-index (elab-mod->name elab-mod) moddb)))
    (b* ((moddb (moddb-maybe-grow moddb)))
      (moddb-add-module1 elab-mod moddb))))


;; (local (defsection moddb-equiv-of-elab-mod-updates
;;          (defthm elab-modlist-fix-of-update-nth
;;            (equal (elab-modlist-fix (update-nth n (elab-mod$a-fix v) x))
;;                   (elab-modlist-fix (update-nth n v x)))
;;            :hints(("Goal" :in-theory (e/d (elab-modlist-fix update-nth)
;;                                           (acl2::update-nth-when-atom)))))

;;          (defthm moddb-equiv-of-update-elab-mod-fix
;;            (moddb-equiv (UPDATE-NTH *MODDB->MODSI*
;;                                     (UPDATE-NTH n
;;                                                 (ELAB-MOD$A-FIX ELAB-MOD)
;;                                                 mods)
;;                                     MODDB)
;;                         (UPDATE-NTH *MODDB->MODSI*
;;                                     (UPDATE-NTH n elab-mod mods)
;;                                     MODDB))
;;            :hints(("Goal" :in-theory (enable moddb-fix))))

;;          (defthm elab-modlist-fix-of-update-nth-elab-modlist-fix
;;            (equal (elab-modlist-fix (update-nth n v (elab-modlist-fix x)))
;;                   (elab-modlist-fix (update-nth n v x)))
;;            :hints(("Goal" :in-theory (e/d (elab-modlist-fix update-nth)
;;                                           (acl2::update-nth-when-atom)))))

;;          (defthm moddb-equiv-of-update-update-of-elab-modlist-fix
;;            (moddb-equiv (UPDATE-NTH *MODDB->MODSI*
;;                                     (UPDATE-NTH n
;;                                                 elab-mod
;;                                                 (elab-modlist-fix mods))
;;                                     MODDB)
;;                         (UPDATE-NTH *MODDB->MODSI*
;;                                     (UPDATE-NTH n elab-mod mods)
;;                                     MODDB))
;;            :hints(("Goal" :in-theory (enable moddb-fix))))

;;          (defthm moddb-equiv-of-update-elab-modlist-fix
;;            (moddb-equiv (UPDATE-NTH *MODDB->MODSI*
;;                                     (elab-modlist-fix mods)
;;                                     MODDB)
;;                         (UPDATE-NTH *MODDB->MODSI*
;;                                     mods
;;                                     MODDB))
;;            :hints(("Goal" :in-theory (enable moddb-fix))))))


(defsection nrec-defs
  (define nrec (keys r)
    (if (atom keys)
        nil
      (s (car keys) (g (car keys) r)
         (nrec (cdr keys) r))))

  (define nrec-list (keys rs)
    (if (atom rs)
        nil
      (cons (nrec keys (car rs))
            (nrec-list keys (cdr rs)))))

  (define nrec-list-mods (keys moddb)
    :non-executable t
    :hooks nil
    (update-nth *moddb->modsi* (nrec-list keys (nth *moddb->modsi* moddb)) moddb)))

(acl2::defcontext (nrec keys r) 2)

(acl2::defcontext (nrec-list keys rs) 2)

(acl2::defcontext (nrec-list-mods keys moddb) 2)


(local (defsection nrec-reasoning

         (local (in-theory (enable nrec)))

         (defthm nrec-of-cons
           (equal (nrec (cons a b) r)
                  (s a (g a r) (nrec b r))))

         (defthm nrec-of-nil
           (equal (nrec nil r) nil))

         (defthmd g-of-nrec
           (equal (g k (nrec keys x))
                  (and (member k keys)
                       (g k x))))

         (local (in-theory (enable g-of-nrec)))

         (defthmd s-redundant
           (implies (equal v (g k x))
                    (equal (s k v x) X)))

         (local (in-theory (enable s-redundant)))

         (defthm nrec-idempotent
           (equal (nrec keys1 (nrec keys2 x))
                  (nrec (intersection$ keys1 keys2) x)))

         (defcong list-equiv equal (nrec keys r) 1
           :hints (("goal" :induct (acl2::fast-list-equiv keys keys-equiv)
                    :in-theory (enable (:i acl2::fast-list-equiv)))))

         (local (defthm intersect-superset-under-list-equiv
                  (implies (subsetp x y)
                           (list-equiv (intersection$ x y) x))))
         (defthm intersect-self-under-list-equiv
           (list-equiv (intersection$ x x) x))

         (defthm nrec-of-s-when-not-member
           (implies (not (member k keys))
                    (equal (nrec keys (s k v x))
                           (nrec keys x))))

         (defthm nrec-of-nil-rec
           (equal (nrec keys nil) nil))

         ;; The checkpoints of this proof all have the form
         ;; (implies (and ... (equal (s k1 v a) (s k1 v b)))
         ;;          (equal k (g k y)))
         ;; where to prove the conclusion we need to consider g-same-s of the two
         ;; s's assumed equal.  But the literals may not be in that order, so we
         ;; search the clause for the right ones.
         (local (defun find-equal-of-gs-concl (clause)
                  (if (atom clause)
                      nil
                    (let ((lit (car clause)))
                      (case-match lit
                        (('equal ('g k &) ('g k &))
                         (declare (ignore k))
                         lit)
                        (& (find-equal-of-gs-concl (cdr clause))))))))

         (local (defun find-equal-of-ss-hyp (clause)
                  (if (atom clause)
                      nil
                    (let ((lit (car clause)))
                      (case-match lit
                        (('not ('equal ('s k v x) ('s k w y)))
                         (declare (ignore k v x w y))
                         lit)
                        (('not ('equal ('nrec keys x) ('nrec keys y)))
                         (declare (ignore keys x y))
                         lit)
                        (& (find-equal-of-ss-hyp (cdr clause))))))))

         (local (defun equal-of-nrecs-hint (clause)
                  (let* ((glit (find-equal-of-gs-concl clause))
                         (slit (find-equal-of-ss-hyp clause))
                         (both (list glit slit)))
                    (case-match both
                      ((('equal ('g k &) ('g k &))
                        ('not ('equal ('s k1 v x) ('s k1 w y))))
                       `(:computed-hint-replacement
                         ((and stable-under-simplificationp
                               '(:in-theory (enable acl2::g-of-s-redux))))
                         :use ((:instance acl2::g-of-s-redux
                                (acl2::a ,k)
                                (acl2::b ,k1)
                                (acl2::v ,v)
                                (acl2::r ,x))
                               (:instance acl2::g-of-s-redux
                                (acl2::a ,k)
                                (acl2::b ,k1)
                                (acl2::v ,w)
                                (acl2::r ,y)))
                         :in-theory (disable acl2::g-same-s
                                             acl2::g-diff-s
                                             acl2::g-of-s-redux)))
                      ((('equal ('g k &) ('g k &))
                        ('not ('equal ('nrec keys x) ('nrec keys y))))
                       `(:computed-hint-replacement
                         ((and stable-under-simplificationp
                               '(:in-theory (enable g-of-nrec))))
                         :use ((:instance g-of-nrec
                                (k ,k)
                                (keys ,keys)
                                (x ,x))
                               (:instance g-of-nrec
                                (k ,k)
                                (keys ,keys)
                                (x ,y)))
                         :in-theory (disable g-of-nrec)))))))

         (local (include-book "misc/equal-by-g" :dir :system))

         (local (defun equal-of-nrecs-hint-for-cdr (clause)
                  (let ((lit (car (last clause))))
                    (case-match lit
                      (('equal ('nrec keys x) ('nrec keys y))
                       `(:use ((:functional-instance acl2::equal-by-g
                                (acl2::equal-by-g-hyp
                                 (lambda () (not (or . ,(butlast clause 1)))))
                                (acl2::equal-by-g-lhs
                                 (lambda () (nrec ,keys ,x)))
                                (acl2::equal-by-g-rhs
                                 (lambda () (nrec ,keys ,y)))))))))))



         (defthm equal-of-nrecs
           (implies (syntaxp (quotep keys))
                    (equal (equal (nrec keys x) (nrec keys y))
                           (if (atom keys)
                               t
                             (and (equal (g (car keys) x) (g (car keys) y))
                                  (equal (nrec (cdr keys) x) (nrec (cdr keys) y))))))
           :hints (("goal" :do-not-induct t
                    :cases ((member (car keys) (cdr keys))))
                   (and stable-under-simplificationp
                        (equal-of-nrecs-hint-for-cdr clause))
                   (and stable-under-simplificationp
                        (equal-of-nrecs-hint clause)))
           :otf-flg t)

         (acl2::def-ruleset! nrec-reasoning nil)

         (local (in-theory (disable nrec)))
         (local (in-theory (enable nrec-list)))

         (defcong list-equiv equal (nrec-list keys rs) 1)

         (defthm nrec-list-of-nrec-list
           (equal (nrec-list keys1 (nrec-list keys2 rs))
                  (nrec-list (intersection$ keys1 keys2) rs)))

         (defthm nrec-list-of-update-nth-nrec
           (equal (nrec-list keys (update-nth n (nrec keys v) x))
                  (nrec-list keys (update-nth n v x)))
           :hints(("Goal" :in-theory (enable update-nth))))

         (defthm nrec-list-of-update-nth-nrec-list
           (equal (nrec-list keys (update-nth n v (nrec-list keys x)))
                  (nrec-list keys (update-nth n v x)))
           :hints(("Goal" :in-theory (e/d (update-nth)
                                          (acl2::update-nth-when-atom)))))

         (acl2::defcong+ nrec-list-of-update-nth
           (nrec-list keys (update-nth n v x))
           :cong ((v (equal a (nrec keys v)))
                  (x (equal b (nrec-list keys x))))
           :hints (("goal" :use ((:instance nrec-list-of-update-nth-nrec-list
                                  (v a))
                                 (:instance nrec-list-of-update-nth-nrec-list
                                  (v a) (x b))
                                 (:instance nrec-list-of-update-nth-nrec)
                                 (:instance nrec-list-of-update-nth-nrec
                                  (v a)))
                    :in-theory (disable nrec-list-of-update-nth-nrec-list
                                        nrec-list-of-update-nth-nrec))))

         (in-theory (disable nrec-list-of-update-nth))

         (acl2::add-to-ruleset nrec-reasoning nrec-list-of-update-nth)

         (defthm len-of-nrec-list
           (equal (len (nrec-list keys x))
                  (len x)))

         (defthm nth-of-nrec-list
           (equal (nth n (nrec-list keys x))
                  (nrec keys (nth n x)))
           :hints(("Goal" :in-theory (enable nth))))


         (local (defthmd nth-open-const
                  (implies (syntaxp (quotep n))
                           (equal (nth n x)
                                  (if (zp n)
                                      (car x)
                                    (nth (1- n) (cdr x)))))
                  :hints(("Goal" :in-theory (enable nth)))))

         (local (defthmd update-nth-open-const
                  (implies (syntaxp (quotep n))
                           (equal (update-nth n v x)
                                  (if (zp n)
                                      (cons v (cdr x))
                                    (cons (car x)
                                          (update-nth (1- n) v (cdr x))))))
                  :hints(("Goal" :in-theory (enable update-nth)))))

         (local (in-theory (disable nrec-list)))
         (local (in-theory (enable nrec-list-mods)))


         (defthm nrec-list-mods-of-update-mods-of-nrec-list
           (equal (nrec-list-mods keys (update-nth *moddb->modsi* (nrec-list keys mods) moddb))
                  (nrec-list-mods keys (update-nth *moddb->modsi* mods moddb))))

         (acl2::defcong+ nrec-list-mods-propagate-to-keys
           (nrec-list-mods keys (update-nth *moddb->modsi* mods moddb))
           :cong ((mods (equal ms (nrec-list keys mods)))))

         (in-theory (disable nrec-list-mods-propagate-to-keys))
         (acl2::add-to-ruleset nrec-reasoning nrec-list-mods-propagate-to-keys)

         (defthm nrec-list-mods-of-update-nth-nrec-list-mods
           (implies (not (equal (nfix n) *moddb->modsi*))
                    (equal (nrec-list-mods keys (update-nth n mods (nrec-list-mods keys moddb)))
                           (nrec-list-mods keys (update-nth n mods moddb))))
           :hints ((and stable-under-simplificationp
                        '(:in-theory (enable nth-open-const
                                             update-nth-open-const)))))

         (acl2::defcong+ nrec-list-mods-propagate-over-irrelevant-update
           (nrec-list-mods keys (update-nth n mods moddb))
           :cong ((moddb (equal mdb (nrec-list-mods keys moddb))))
           :hyps (not (equal (nfix n) *moddb->modsi*))
           :hints ((and stable-under-simplificationp
                        '(:in-theory (enable nth-open-const
                                             update-nth-open-const)))))

         (in-theory (disable nrec-list-mods-propagate-over-irrelevant-update))
         (acl2::add-to-ruleset nrec-reasoning nrec-list-mods-propagate-over-irrelevant-update)

         (defthm moddb-indices-ok-of-nrec
           (equal (moddb-indices-ok (nrec-list-mods '(:name) moddb))
                  (moddb-indices-ok moddb))
           :hints (("goal" :cases ((moddb-indices-ok moddb)))
                   (and stable-under-simplificationp
                        '(:in-theory (enable moddb-indices-not-ok
                                             nrec-list-mods)))
                   (and stable-under-simplificationp
                        '(:use ((:instance moddb-indices-ok-implies
                                 (idx (moddb-indices-badguy moddb))
                                 (moddb (nrec-list-mods '(:name) moddb)))
                                ;; (:instance moddb-indices-ok-implies
                                ;;  (idx (moddb-indices-badguy (nrec-list-mods '(:name) moddb)))
                                ;;  (moddb moddb))
                                )
                          :in-theory (e/d (nrec-list-mods)
                                          (moddb-indices-ok-implies)))))
           :otf-flg t)

         (acl2::defcong+ nrec-propagate-of-moddb-indices-ok
           (moddb-indices-ok moddb)
           :cong ((moddb (equal mdb (nrec-list-mods '(:name) moddb))))
           :hints(("Goal" :use ((:instance moddb-indices-ok-of-nrec (moddb mdb))
                                (:instance moddb-indices-ok-of-nrec))
                   :in-theory (disable moddb-indices-ok-of-nrec))))

         (in-theory (disable nrec-propagate-of-moddb-indices-ok))
         (add-to-ruleset nrec-reasoning nrec-propagate-of-moddb-indices-ok)

         ;; (local (defthm equal-of-update-nths
         ;;          (equal (equal (update-nth n v x)
         ;;                        (update-nth n w y))
         ;;                 (and (equal v w)
         ;;                      (equal x (update-nth n (nth n x) y))))
         ;;          :hints (("goal" :use ((:instance acl2::nth-of-update-nth-same
         ;;                                 (acl2::n n) (acl2::v v))
         ;;                                (:instance acl2::nth-of-update-nth-same
         ;;                                 (acl2::n n) (acl2::v w) (x y)))
         ;;                   :in-theory (disable acl2::nth-of-update-nth-same))
         ;;                  (and stable-under-simplificationp
         ;;                       (acl2::equal-by-nths-hint)))))

         (local (in-theory (disable nrec-list-mods)))

         (defthm moddb-basics-ok-of-nrec
           (equal (moddb-basics-ok (nrec-list-mods '(:name) moddb))
                  (moddb-basics-ok moddB))
           :hints(("goal" :cases ((moddb-basics-ok moddB)))
                  (and stable-under-simplificationp
                       '(:in-theory (enable moddb-basics-ok
                                            moddb-indices-ok-of-nrec)))
                  (and stable-under-simplificationp
                       '(:in-theory (enable nrec-list-mods)))
                  (and stable-under-simplificationp
                       '(:in-theory (enable nth-open-const
                                            update-nth-open-const)))))

         (acl2::defcong+ nrec-propagate-of-moddb-basics-ok
           (moddb-basics-ok moddb)
           :cong ((moddb (equal mdb (nrec-list-mods '(:name) moddb))))
           :hints(("Goal" :use ((:instance moddb-basics-ok-of-nrec (moddb mdb))
                                (:instance moddb-basics-ok-of-nrec))
                   :in-theory (disable moddb-basics-ok-of-nrec))))

         (in-theory (disable nrec-propagate-of-moddb-basics-ok
                             moddb-basics-ok-of-nrec))
         (add-to-ruleset nrec-reasoning
                         '(nrec-propagate-of-moddb-basics-ok
                           moddb-basics-ok-of-nrec))

         (defun nrec-simplify-bind-free (term)
           (case-match term
             (('s key ('g key rec) . &)
              (declare (ignore key))
              `((rec . ,rec)))))

         (defthmd nrec-simplify-attempt
           (implies (and (bind-free (nrec-simplify-bind-free x) (rec))
                         (equal (nrec keys x) (nrec keys rec)))
                    (equal (nrec keys x)
                           (nrec keys rec))))

         (in-theory (disable nrec-of-cons nrec-of-nil))

         (defthm my-unhide-hide
           (equal (acl2::unhide (hide x))
                  (double-rewrite x)))

         (defthm elab-modlist-fix-of-update-nth
           (implies (<= (nfix n) (len x))
                    (equal (elab-modlist-fix (update-nth n v x))
                           (update-nth n (elab-mod$a-fix v) (elab-modlist-fix x))))
           :hints(("Goal" :in-theory (enable elab-modlist-fix update-nth))))
         (local (include-book "misc/equal-by-g" :dir :system))
         (defthm equal-of-s
           (implies (equal x (s k (g k x) y))
                    (equal (equal (s k v x) y)
                           (equal (g k y) v)))
           ;; :hints (("goal" :use
           ;;          ((:functional-instance acl2::equal-by-g
           ;;            (acl2::equal-by-g-hyp (lambda () (equal (S K NIL X) (S K NIL Y))))
           ;;            (acl2::equal-by-g-lhs (lambda () (S K (G K Y) X)))
           ;;            (acl2::equal-by-g-rhs (lambda () y))))
           ;;          :in-theory (enable acl2::g-of-s-redux))
           ;;         (and stable-under-simplificationp
           ;;              '(:use ((:instance acl2::g-diff-s
           ;;                       (acl2::a acl2::arbitrary-key)
           ;;                       (acl2::b k) (acl2::v nil)
           ;;                       (acl2::r x))
           ;;                      (:instance acl2::g-diff-s
           ;;                       (acl2::a acl2::arbitrary-key)
           ;;                       (acl2::b k) (acl2::v nil)
           ;;                       (acl2::r y)))
           ;;                :in-theory (disable acl2::g-diff-s))))
           )

         (defthm equal-of-s-same
           (implies (equal x y)
                    (equal (equal (s k v x) (s k v y)) t)))

         (defthm g-when-equal-s
           (implies (equal x (s k v y))
                    (equal (g i x)
                           (if (equal i k)
                               v
                             (g i y)))))))


(local (in-theory (e/d
                   ((:rewrite nth-of-elab-modlist-fix)))))

(defsection moddb-add-modinst
  (define moddb-add-modinst-to-last ((instname name-p)
                                     (modidx natp "instantiated module")
                                     moddb)
    :guard (and (moddb-ok moddb)
                (< modidx (+ -1 (moddb->nmods moddb))))
    :prepwork ((local (in-theory (disable len acl2::nth-when-too-large-cheap
                               acl2::nth-when-atom
                               no-duplicatesp
                               elab-modinsts-rem-dups-when-no-duplicates
                               member
                               elab-modinst$cp
                               g-when-equal-s))))
    (flet ((body
            (instname modidx moddb)
            (b* ((instname (mbe :logic (name-fix instname) :exec instname))
                 (modidx (lnfix modidx))
                 ((unless (mbt (< 0 (moddb->nmods moddb))))
                  moddb)
                 (modified-modidx (1- (moddb->nmods moddb)))
                 ((acl2::local-stobjs elab-modinst$c) (mv moddb elab-modinst$c))
                 (elab-modinst$c (update-elab-modinst$c->instname instname elab-modinst$c))
                 (elab-modinst$c (update-elab-modinst$c->modidx modidx elab-modinst$c))
                 ((stobj-get subwires subinsts)
                  ((elab-mod2 (moddb->modsi modidx moddb)))
                  (mv (elab-mod->totalwires elab-mod2)
                      (elab-mod->totalinsts elab-mod2)))
                 ((mv subwires subinsts)
                  (if (mbt (< modidx modified-modidx))
                      (mv subwires subinsts)
                    (mv 0 0))))
              (stobj-let
               ((elab-mod (moddb->modsi modified-modidx moddb)))
               (elab-mod elab-modinst$c)
               (b* (((when (elab-mod-instname->idx instname elab-mod))
                     (mv elab-mod elab-modinst$c))
                    (totalwires (elab-mod->totalwires elab-mod))
                    (totalinsts (elab-mod->totalinsts elab-mod))
                    (elab-modinst$c (update-elab-modinst$c->wire-offset totalwires elab-modinst$c))
                    (elab-mod (update-elab-mod->totalwires (+ totalwires subwires) elab-mod))
                    (elab-modinst$c (update-elab-modinst$c->inst-offset totalinsts elab-modinst$c))
                    (elab-mod (update-elab-mod->totalinsts (+ 1 totalinsts subinsts) elab-mod))
                    (elab-mod (elab-mod-add-inst elab-modinst$c elab-mod)))
                 (mv elab-mod elab-modinst$c))
               (mv moddb elab-modinst$c)))))
      (mbe :logic (non-exec (let ((moddb (moddb-fix moddb)))
                              (body instname modidx moddb)))
           :exec (body instname modidx moddb)))
    ///
    (defthm len-of-cons
      (equal (len (cons a b))
             (+ 1 (len b)))
      :hints(("Goal" :in-theory (enable len))))



    (deffixequiv moddb-add-modinst-to-last)

    (fty::deffixcong moddb-norm-equiv moddb-norm-equiv
      (moddb-add-modinst-to-last instname modidx moddb) moddb
      :hints (("goal" :in-theory (disable elab-mod$a->totalwires
                                          elab-mod$a->totalinsts
                                      (:rewrite nth-of-elab-modlist-fix)))
              (and stable-under-simplificationp
                   '(:in-theory (e/d (moddb-norm)
                                     (elab-mod$a->totalwires
                                      elab-mod$a->totalinsts))))))

    (local (include-book "tools/trivial-ancestors-check" :dir :system))
    (local (acl2::use-trivial-ancestors-check))

    (local (defthm update-nth-of-nth-under-moddb-equiv
             (moddb-equiv (update-nth n (nth n x) x)
                          x)
             :hints(("Goal" :in-theory (enable moddb-fix)))))

    (local (defthm update-nth-of-nth-under-elab-modlist-norm-equiv
             (elab-modlist-norm-equiv (update-nth n (nth n x) x)
                                      x)
             :hints(("Goal" :in-theory (e/d (elab-modlist-norm
                                             update-nth nth)
                                            (acl2::update-nth-when-atom))))))

    (defthm moddb-add-modinst-to-last-basics-ok
      (implies (moddb-basics-ok moddb)
               (moddb-basics-ok
                (moddb-add-modinst-to-last instname modidx moddb)))
      :hints((and stable-under-simplificationp
                  '(:in-theory (enable* elab-mod$a-add-inst
                                        nrec-reasoning)))))

    ;; (local (in-theory (disable elab-mod$a->totalinsts
    ;;                            elab-mod$a->totalwires)))


    ;; (local (defthm my-nth-of-append
    ;;          (equal (nth n (append x y))
    ;;                 (if (< (nfix n) (len x))
    ;;                     (nth n x)
    ;;                   (nth (- (nfix n) (len x)) y)))
    ;;          :hints(("Goal" :in-theory (enable nth len)))))

    (local (defthm my-nth-of-append-less
             (implies (< (nfix n) (len x))
                      (equal (nth n (append x y))
                             (nth n x)))
             :hints(("Goal" :in-theory (enable nth len)))))

    (local (defthm my-nth-of-append-more
             (implies (<= (len x) (nfix n))
                      (equal (nth n (append x y))
                             (nth (- (nfix n) (len x)) y)))
             :hints(("Goal" :in-theory (enable nth len)))))

    (local (defthm modinsts-len-nonzero-when-member-names
             (implies (member instname (acl2::remove-later-duplicates
                                        (elab-modinst-list-names insts)))
                      (< 0 (len (elab-modinsts-rem-dups insts))))
             :hints(("Goal" :in-theory (enable elab-modinst-list-names
                                               elab-modinsts-rem-dups
                                               acl2::remove-later-duplicates
                                               len)))
             :rule-classes :linear))


    (fty::deffixcong elab-mod$a-equiv nat-equiv
      (g :totalwires elab-mod) elab-mod)

    (fty::deffixcong elab-mod$a-equiv nat-equiv
      (g :totalinsts elab-mod) elab-mod
      :thm-suffix "-INSTS")


    ;; (local (defthm moddb-modinst-ok-of-modify-later-module
    ;;          (implies (< (nfix modidx) (nfix modmodidx))
    ;;                   (equal (moddb-modinst-ok
    ;;                           inst modidx (update-nth
    ;;                                        *moddb->modsi*

    (defthm moddb-modinst-order-ok-of-update-other-module
      (implies (not (equal (nfix modmodidx) (nfix modidx)))
               (equal (moddb-modinst-order-ok
                       inst modidx (update-nth *moddb->modsi*
                                               (update-nth modmodidx mod mods)
                                               moddb))
                      (moddb-modinst-order-ok
                       inst modidx (update-nth *moddb->modsi* mods moddb))))
      :hints(("Goal" :in-theory (enable moddb-modinst-order-ok))))

    (local (defthm ninsts-of-add-inst-lower-bound
             (<= (elab-mod$a-ninsts elab-mod)
                 (elab-mod$a-ninsts (elab-mod$a-add-inst inst elab-mod)))
             :hints(("Goal" :in-theory (enable elab-mod$a-add-inst
                                               elab-mod$a-ninsts)))
             :rule-classes :linear))

    (local (defthm ninsts-of-add-inst-upper-bound
             (<= (elab-mod$a-ninsts (elab-mod$a-add-inst inst elab-mod))
                 (+ 1 (elab-mod$a-ninsts elab-mod)))
             :hints(("Goal" :in-theory (enable elab-mod$a-add-inst
                                               elab-mod$a-ninsts
                                               len)))
             :rule-classes :linear))

    (local (defthm moddb-modinst-order-ok-of-add-inst-for-existing
             (implies (case-split (< (nfix instidx) (elab-mod$a-ninsts mod)))
                      (equal (moddb-modinst-order-ok
                              instidx modidx (update-nth *moddb->modsi*
                                                         (update-nth modidx
                                                                     (elab-mod$a-add-inst inst mod)
                                                                     mods)
                                                         moddb))
                             (moddb-modinst-order-ok
                              instidx modidx (update-nth *moddb->modsi*
                                                         (update-nth modidx mod mods)
                                                         moddb))))
             :hints(("Goal" :in-theory (enable moddb-modinst-order-ok
                                               elab-mod$a-add-inst
                                               elab-mod$a->inst-modidx
                                               elab-mod$a-ninsts)))))

    (defthm moddb-modinst-order-ok-of-nrec-list-mods
      (equal (moddb-modinst-order-ok inst modidx
                                     (nrec-list-mods '(:insts) moddb))
             (moddb-modinst-order-ok inst modidx moddb))
      :hints(("Goal" :in-theory (enable moddb-modinst-order-ok
                                        elab-mod$a->inst-modidx
                                        elab-mod$a-ninsts
                                        g-of-nrec
                                        nrec-list-mods))))
    (acl2::defcong+ moddb-modinst-order-ok-apply-nrec
      (moddb-modinst-order-ok inst modidx moddb)
      :cong ((moddb (equal mdb (nrec-list-mods '(:insts) moddb))))
      :hints (("goal" :use ((:instance moddb-modinst-order-ok-of-nrec-list-mods (moddb mdb))
                            (:instance moddb-modinst-order-ok-of-nrec-list-mods))
               :in-theory (disable moddb-modinst-order-ok-of-nrec-list-mods))))

    (in-theory (disable moddb-modinst-order-ok-apply-nrec))
    (acl2::add-to-ruleset nrec-reasoning moddb-modinst-order-ok-apply-nrec)

    (defthm elab-mod$a-ninsts-of-nrec
      (equal (elab-mod$a-ninsts (nrec '(:insts) x))
             (elab-mod$a-ninsts x))
      :hints(("Goal" :in-theory (enable elab-mod$a-ninsts
                                        g-of-nrec))))

    (acl2::defcong+ elab-mod$a-ninsts-apply-nrec
      (elab-mod$a-ninsts elab-mod)
      :cong ((elab-mod (equal elmo (nrec '(:insts) elab-mod))))
      :hints (("goal" :use ((:instance elab-mod$a-ninsts-of-nrec (x elmo))
                            (:instance elab-mod$a-ninsts-of-nrec (x elab-mod)))
               :in-theory (disable elab-mod$a-ninsts-of-nrec))))

    (in-theory (disable elab-mod$a-ninsts-apply-nrec))
    (acl2::add-to-ruleset nrec-reasoning elab-mod$a-ninsts-apply-nrec)

    ;; (local (defthm natp-of-x-minus-1-forward
    ;;          (implies (natp (+ -1 x))
    ;;                   (natp x))
    ;;          :rule-classes :forward-chaining))
    ;; (local (defthm posp-of-x-minus-1-forward
    ;;          (implies (posp (+ -1 x))
    ;;                   (posp x))
    ;;          :rule-classes :forward-chaining))

    (defthm moddb-mod-inst-wireoffset-of-update-later-module
      (implies (case-split (> (nfix modmodidx) (nfix modidx)))
               (equal (moddb-mod-inst-wireoffset
                       inst modidx (update-nth *moddb->modsi*
                                               (update-nth modmodidx mod mods)
                                               moddb))
                      (moddb-mod-inst-wireoffset
                       inst modidx (update-nth *moddb->modsi* mods moddb))))
      :hints(("Goal" :in-theory (enable moddb-mod-inst-wireoffset))))

    (defthm moddb-mod-inst-instoffset-of-update-later-module
      (implies (case-split (> (nfix modmodidx) (nfix modidx)))
               (equal (moddb-mod-inst-instoffset
                       inst modidx (update-nth *moddb->modsi*
                                               (update-nth modmodidx mod mods)
                                               moddb))
                      (moddb-mod-inst-instoffset
                       inst modidx (update-nth *moddb->modsi* mods moddb))))
      :hints(("Goal" :in-theory (enable moddb-mod-inst-instoffset))))

    (defthm moddb-modinst-ok-of-update-later-module
      (implies (case-split (> (nfix modmodidx) (nfix modidx)))
               (equal (moddb-modinst-ok
                       inst modidx (update-nth *moddb->modsi*
                                               (update-nth modmodidx mod mods)
                                               moddb))
                      (moddb-modinst-ok
                       inst modidx (update-nth *moddb->modsi* mods moddb))))
      :hints(("Goal" :in-theory (enable moddb-modinst-ok))))

    (defthm moddb-mod-inst-instoffset-of-update-later
      (implies (and (case-split (< (nfix instidx) (elab-mod$a-ninsts mod))))
               (equal (moddb-mod-inst-instoffset
                       instidx modidx (update-nth *moddb->modsi*
                                                  (update-nth modidx
                                                              (elab-mod$a-add-inst inst mod)
                                                              mods)
                                                  moddb))
                      (moddb-mod-inst-instoffset
                       instidx modidx (update-nth *moddb->modsi*
                                                  (update-nth modidx mod mods)
                                                  moddb))))
      :hints(("Goal" :in-theory (enable moddb-mod-inst-instoffset
                                        elab-mod$a-add-inst
                                        elab-mod$a->inst-instoffset
                                        elab-mod$a->inst-wireoffset
                                        elab-mod$a->inst-modidx
                                        elab-mod$a-ninsts))))

    (defthm moddb-mod-inst-wireoffset-of-update-later
      (implies (and (case-split (< (nfix instidx) (elab-mod$a-ninsts mod))))
               (equal (moddb-mod-inst-wireoffset
                       instidx modidx (update-nth *moddb->modsi*
                                                  (update-nth modidx
                                                              (elab-mod$a-add-inst inst mod)
                                                              mods)
                                                  moddb))
                      (moddb-mod-inst-wireoffset
                       instidx modidx (update-nth *moddb->modsi*
                                                  (update-nth modidx mod mods)
                                                  moddb))))
      :hints(("Goal" :in-theory (enable moddb-mod-inst-wireoffset
                                        elab-mod$a-add-inst
                                        elab-mod$a->inst-wireoffset
                                        elab-mod$a->inst-modidx
                                        elab-mod$a-ninsts
                                        elab-mod$a-nwires))))

    (local (defthm moddb-modinst-ok-of-add-inst-for-existing
             (implies (and (case-split (< (nfix instidx) (elab-mod$a-ninsts mod))))
                      (equal (moddb-modinst-ok
                              instidx modidx (update-nth *moddb->modsi*
                                                         (update-nth modidx
                                                                     (elab-mod$a-add-inst inst mod)
                                                                     mods)
                                                         moddb))
                             (moddb-modinst-ok
                              instidx modidx (update-nth *moddb->modsi*
                                                         (update-nth modidx mod mods)
                                                         moddb))))
             :hints(("Goal" :in-theory (enable moddb-modinst-ok
                                               elab-mod$a->inst-instoffset
                                               elab-mod$a->inst-wireoffset
                                               elab-mod$a->inst-modidx
                                               elab-mod$a-ninsts))
                    (and stable-under-simplificationp
                         '(:in-theory (enable moddb-modinst-ok
                                              elab-mod$a-add-inst
                                              elab-mod$a->inst-instoffset
                                              elab-mod$a->inst-wireoffset
                                              elab-mod$a->inst-modidx
                                              elab-mod$a-ninsts))))))


    (defthm moddb-mod-inst-wireoffset-of-update-mod-nrec
      (equal (moddb-mod-inst-wireoffset
              instidx modidx
              (update-nth *moddb->modsi*
                          (update-nth modidx
                                      (nrec '(:insts :wires) mod)
                                      mods)
                          moddb))
             (moddb-mod-inst-wireoffset
              instidx modidx
              (update-nth *moddb->modsi*
                          (update-nth modidx mod mods)
                          moddb)))
      :hints(("Goal" :in-theory (enable moddb-mod-inst-wireoffset
                                        elab-mod$a->inst-wireoffset
                                        elab-mod$a->inst-modidx
                                        elab-mod$a-ninsts
                                        elab-mod$a-nwires
                                        g-of-nrec))))

    (acl2::defcong+ moddb-mod-inst-wireoffset-of-update-mod-propagate-nrec
      (moddb-mod-inst-wireoffset
       instidx modidx
       (update-nth *moddb->modsi*
                   (update-nth modidx mod mods)
                   moddb))
      :cong ((mod (equal m (nrec '(:insts :wires) mod))))
      :hints (("goal" :use ((:instance moddb-mod-inst-wireoffset-of-update-mod-nrec (mod m))
                            (:instance moddb-mod-inst-wireoffset-of-update-mod-nrec))
               :in-theory (disable moddb-mod-inst-wireoffset-of-update-mod-nrec))))

    (in-theory (disable moddb-mod-inst-wireoffset-of-update-mod-propagate-nrec))
    (acl2::add-to-ruleset nrec-reasoning moddb-mod-inst-wireoffset-of-update-mod-propagate-nrec)

    (defthm moddb-mod-inst-instoffset-of-update-mod-nrec
      (equal (moddb-mod-inst-instoffset
              instidx modidx
              (update-nth *moddb->modsi*
                          (update-nth modidx
                                      (nrec '(:insts :wires) mod)
                                      mods)
                          moddb))
             (moddb-mod-inst-instoffset
              instidx modidx
              (update-nth *moddb->modsi*
                          (update-nth modidx mod mods)
                          moddb)))
      :hints(("Goal" :in-theory (enable moddb-mod-inst-instoffset
                                        elab-mod$a->inst-instoffset
                                        elab-mod$a->inst-modidx
                                        elab-mod$a-ninsts
                                        g-of-nrec))))

    (acl2::defcong+ moddb-mod-inst-instoffset-of-update-mod-propagate-nrec
      (moddb-mod-inst-instoffset
       instidx modidx
       (update-nth *moddb->modsi*
                   (update-nth modidx mod mods)
                   moddb))
      :cong ((mod (equal m (nrec '(:insts :wires) mod))))
      :hints (("goal" :use ((:instance moddb-mod-inst-instoffset-of-update-mod-nrec (mod m))
                            (:instance moddb-mod-inst-instoffset-of-update-mod-nrec))
               :in-theory (disable moddb-mod-inst-instoffset-of-update-mod-nrec))))

    (in-theory (disable moddb-mod-inst-instoffset-of-update-mod-propagate-nrec))
    (acl2::add-to-ruleset nrec-reasoning moddb-mod-inst-instoffset-of-update-mod-propagate-nrec)


    (defthm moddb-modinst-ok-of-add-inst-nrec
      (equal (moddb-modinst-ok
              instidx modidx (update-nth *moddb->modsi*
                                         (update-nth modidx
                                                     (nrec '(:insts :wires) mod)
                                                     mods)
                                         moddb))
             (moddb-modinst-ok
              instidx modidx (update-nth *moddb->modsi*
                                         (update-nth modidx mod mods)
                                         moddb)))
      :hints(("Goal" :in-theory (enable moddb-modinst-ok
                                        elab-mod$a->inst-instoffset
                                        elab-mod$a->inst-wireoffset
                                        elab-mod$a->inst-modidx
                                        elab-mod$a-ninsts
                                        g-of-nrec))))

    (acl2::defcong+ moddb-modinst-ok-of-add-inst-apply-nrec
      (moddb-modinst-ok instidx modidx (update-nth *moddb->modsi*
                                                   (update-nth modidx mod mods)
                                                   moddb))
      :cong ((mod (equal m (nrec '(:insts :wires) mod))))
      :hints (("goal" :use ((:instance moddb-modinst-ok-of-add-inst-nrec)
                            (:instance moddb-modinst-ok-of-add-inst-nrec (mod m)))
               :in-theory (disable moddb-modinst-ok-of-add-inst-nrec))))

    (in-theory (disable moddb-modinst-ok-of-add-inst-nrec))
    (acl2::add-to-ruleset nrec-reasoning moddb-modinst-ok-of-add-inst-nrec)





    (defthm s-of-nrec-when-member
      (implies (member k keys)
               (equal (s k v (nrec keys x))
                      (nrec keys (s k v x))))
      :hints(("Goal" :in-theory (e/d (nrec acl2::g-of-s-redux
                                           g-of-nrec s-redundant)
                                     (equal-of-s))
              :induct t)
             (and stable-under-simplificationp
                  '(:cases ((member (car keys) (Cdr keys)))))))

    (acl2::defcong+ propagate-nrec-over-s
      (nrec keys (s k v x))
      :cong ((x (equal xx (nrec keys x))))
      :hyps (member k keys)
      :hints (("goal" :use ((:instance s-of-nrec-when-member (x xx))
                            (:instance s-of-nrec-when-member))
               :in-theory (disable s-of-nrec-when-member))))


    (defthm moddb-mod-inst-wireoffset-of-append-insts
      (implies (<= (nfix instidx) (len (elab-modinsts-rem-dups insts)))
               (equal (moddb-mod-inst-wireoffset
                       instidx modidx
                       (update-nth *moddb->modsi*
                                   (update-nth modidx
                                               (s :insts
                                                  (append insts new)
                                                  mod)
                                               mods)
                                   moddb))
                      (moddb-mod-inst-wireoffset
                       instidx modidx
                       (update-nth *moddb->modsi*
                                   (update-nth modidx
                                               (s :insts insts mod)
                                               mods)
                                   moddb))))
      :hints(("Goal" :in-theory (enable moddb-mod-inst-wireoffset
                                        elab-mod$a->inst-wireoffset
                                        elab-mod$a->inst-modidx
                                        elab-mod$a-ninsts
                                        elab-mod$a-nwires)
              :do-not-induct t)))

    (defthm moddb-mod-inst-instoffset-of-append-insts
      (implies (<= (nfix instidx) (len (elab-modinsts-rem-dups insts)))
               (equal (moddb-mod-inst-instoffset
                       instidx modidx
                       (update-nth *moddb->modsi*
                                   (update-nth modidx
                                               (s :insts
                                                  (append insts new)
                                                  mod)
                                               mods)
                                   moddb))
                      (moddb-mod-inst-instoffset
                       instidx modidx
                       (update-nth *moddb->modsi*
                                   (update-nth modidx
                                               (s :insts insts mod)
                                               mods)
                                   moddb))))
      :hints(("Goal" :in-theory (enable moddb-mod-inst-instoffset
                                        elab-mod$a->inst-instoffset
                                        elab-mod$a->inst-modidx
                                        elab-mod$a-ninsts)
              :do-not-induct t)))

    (fty::deffixcong elab-modinsts-nodups-equiv elab-mod$a-equiv
      (s :insts v x) v
      :hints(("Goal" :in-theory (enable elab-mod$a-fix))))

    (defthm fix-of-number
      (implies (acl2-numberp x)
               (equal (fix x) x))
      :rule-classes ((:rewrite :backchain-limit-lst 0)))

    (local (in-theory (disable fix not acl2::zp-open
                               nth-update-nth
                               default-+-2
                               default-+-1
                               acl2::nfix-when-not-natp
                               MODDB-MOD-INST-WIREOFFSET-OF-UPDATE-LATER)))

    (defthm moddb-add-modinst-to-last-mods-ok
      (implies (and (moddb-mods-ok moddb)
                    (< (nfix modidx) (+ -1 (moddb->nmods moddb))))
               (moddb-mods-ok
                (moddb-add-modinst-to-last instname modidx moddb)))
      :hints(;; (and stable-under-simplificationp
             ;;      '(:in-theory (enable* elab-mod$a-add-inst)))
             ("Goal" :in-theory (disable
                                 (:rewrite nth-of-elab-modlist-fix)))
             (and stable-under-simplificationp
                  '(
                    :in-theory (e/d (moddb-mods-not-ok
                                     moddb-mod-ok)
                                    (moddb-add-modinst-to-last))))
             (and stable-under-simplificationp
                  '(:in-theory (enable moddb-add-modinst-to-last
                                       moddb-mod-insts-not-ok
                                       moddb-mod-order-not-ok
                                       elab-mod$a-instname->idx
; moddb-modinst-order-ok
                                       ;; moddb-modinst-ok
; elab-mod$a-ninsts
; elab-mod$a->inst-modidx
                                       )))
             (and stable-under-simplificationp
                  `(:computed-hint-replacement
                    ('(:clause-processor
                       (acl2::generalize-termlist-cp
                        clause (list (acl2::find-calls-of-fns-lst
                                      '(moddb-mod-badguy) clause)
                                     'modbad))))
                    :clause-processor
                    (acl2::generalize-termlist-cp
                     clause (list (acl2::find-calls-of-fns-lst
                                   '(moddb-modinst-order-badguy
                                     moddb-modinst-badguy) clause)
                                  'instbad))))

             (and stable-under-simplificationp
                  '(:in-theory (enable* nrec-reasoning)))

             (and stable-under-simplificationp
                  (let ((lit (car (last clause))))
                    (case-match lit
                      (('moddb-modinst-order-ok . &)
                       '(:in-theory (enable moddb-modinst-order-ok
                                            elab-mod$a->inst-modidx
                                            elab-mod$a-add-inst
                                            elab-mod$a-ninsts)))
                      (('moddb-modinst-ok . &)
                       '(:in-theory (e/d* (moddb-modinst-ok
                                           elab-mod$a->inst-modidx
                                           elab-mod$a-add-inst
                                           elab-mod$a-ninsts
                                           elab-mod$a-nwires
                                           elab-mod$a->inst-wireoffset
                                           elab-mod$a->inst-instoffset
                                           ;; moddb-mod-inst-instoffset
                                           ;; moddb-mod-inst-wireoffset
                                           )
                                          (moddb-modinst-ok-implies-instoffset
                                           moddb-modinst-ok-implies-wireoffset
                                           moddb-mod-ok-implies-totalwires
                                           moddb-mod-ok-implies-totalinsts))))
                      (('equal ('moddb-mod-inst-wireoffset & modidx &) . &)
                       (declare (ignorable modidx))
                       `(:computed-hint-replacement
                         ((and stable-under-simplificationp
                               '(:in-theory (e/d* (elab-mod$a->inst-modidx
                                                   elab-mod$a-add-inst
                                                   elab-mod$a-ninsts
                                                   elab-mod$a-nwires
                                                   elab-mod$a->inst-wireoffset
                                                   elab-mod$a->inst-instoffset
                                                   moddb-mod-inst-instoffset
                                                   moddb-mod-inst-wireoffset
                                                   )
                                                  (moddb-modinst-ok-implies-instoffset
                                                   moddb-modinst-ok-implies-wireoffset
                                                   moddb-mod-ok-implies-totalwires
                                                   moddb-mod-ok-implies-totalinsts)))))
                         ;; :use ((:instance moddb-mod-ok-implies-totalwires
                         ;;        (modidx modidx)))
                         :expand (,(cadr (car (last clause))))
                         ))
                      (('equal ('moddb-mod-inst-instoffset & modidx &) . &)
                       (declare (ignorable modidx))
                       `(:computed-hint-replacement
                         ((and stable-under-simplificationp
                               '(:in-theory (e/d* (elab-mod$a->inst-modidx
                                                   elab-mod$a-add-inst
                                                   elab-mod$a-ninsts
                                                   elab-mod$a-nwires
                                                   elab-mod$a->inst-wireoffset
                                                   elab-mod$a->inst-instoffset
                                                   moddb-mod-inst-instoffset
                                                   moddb-mod-inst-wireoffset
                                                   )
                                                  (moddb-modinst-ok-implies-instoffset
                                                   moddb-modinst-ok-implies-wireoffset
                                                   moddb-mod-ok-implies-totalwires
                                                   moddb-mod-ok-implies-totalinsts)))))
                         ;; :use ((:instance moddb-mod-ok-implies-totalwires
                         ;;        (modidx modidx)))
                         :expand (,(cadr (car (last clause))))
                         ))
                      )))

             (and stable-under-simplificationp
                  '(:in-theory (e/d* (nrec-reasoning)
                                     (moddb-modinst-ok-implies-instoffset
                                      moddb-modinst-ok-implies-wireoffset
                                      moddb-mod-ok-implies-totalwires
                                      moddb-mod-ok-implies-totalinsts)))))))


  (define moddb-add-modinst ((instname name-p)
                             (modidx natp "instantiated module")
                             (elab-mod "module to which the instance will be added")
                             moddb)
    :guard (and (moddb-ok moddb)
                (< modidx (moddb->nmods moddb))
                (not (elab-mod-instname->idx instname elab-mod)))
    :returns (elab-mod1)
    (flet ((body
            (instname modidx elab-mod moddb)
            (b* ((elab-mod (elab-mod-fix elab-mod))
                 (instname (mbe :logic (name-fix instname) :exec instname))
                 (modidx (lnfix modidx))
                 ((unless (mbt (not (elab-mod-instname->idx instname elab-mod))))
                  elab-mod)
                 ((acl2::local-stobjs elab-modinst$c) (mv elab-mod elab-modinst$c))
                 (elab-modinst$c (update-elab-modinst$c->instname instname elab-modinst$c))
                 (elab-modinst$c (update-elab-modinst$c->modidx modidx elab-modinst$c))
                 ((stobj-get subwires subinsts)
                  ((elab-mod2 (moddb->modsi modidx moddb)))
                  (mv (elab-mod->totalwires elab-mod2)
                      (elab-mod->totalinsts elab-mod2)))
                 ((mv subwires subinsts)
                  (if (mbt (< (lnfix modidx) (moddb->nmods moddb)))
                      (mv subwires subinsts)
                    (mv 0 0)))
                 (totalwires (elab-mod->totalwires elab-mod))
                 (elab-modinst$c (update-elab-modinst$c->wire-offset totalwires elab-modinst$c))
                 (elab-mod (update-elab-mod->totalwires (+ totalwires subwires) elab-mod))
                 (totalinsts (elab-mod->totalinsts elab-mod))
                 (elab-modinst$c (update-elab-modinst$c->inst-offset totalinsts elab-modinst$c))
                 (elab-mod (update-elab-mod->totalinsts (+ 1 totalinsts subinsts) elab-mod))
                 (elab-mod (elab-mod-add-inst elab-modinst$c elab-mod)))
              (mv elab-mod elab-modinst$c))))
      (mbe :logic (non-exec (let ((moddb (moddb-fix moddb)))
                              (body instname modidx elab-mod moddb)))
           :exec (body instname modidx elab-mod moddb)))
    ///
    (deffixequiv moddb-add-modinst)

    (fty::deffixcong moddb-norm-equiv equal
      (moddb-add-modinst instname modidx elab-mod moddb) moddb
      :hints (("goal" :in-theory (disable elab-mod$a->totalwires
                                          elab-mod$a->totalinsts))))

    (local (defthm update-nth-of-nth-under-moddb-equiv
             (moddb-equiv (update-nth n (nth n x) x)
                          x)
             :hints(("Goal" :in-theory (enable moddb-fix)))))

    (local (defthm update-nth-of-nth-under-elab-modlist-norm-equiv
             (elab-modlist-norm-equiv (update-nth n (nth n x) x)
                                      x)
             :hints(("Goal" :in-theory (e/d (elab-modlist-norm
                                             update-nth nth)
                                            (acl2::update-nth-when-atom))))))

    (local (defthm update-nth-same
             (implies (nat-equiv n m)
                      (equal (update-nth n v (update-nth m w x))
                             (update-nth n v x)))
             :hints(("Goal" :in-theory (enable update-nth)))))


    (defthm name-of-elab-mod$a-add-inst
      (equal (g :name (elab-mod$a-add-inst inst mod))
             (modname-fix (g :name mod)))
      :hints(("Goal" :in-theory (enable elab-mod$a-add-inst))))


    (defthm moddb-add-module1-of-moddb-add-modinst
      (implies (not (moddb-modname-get-index (g :name elab-mod) moddb))
               (moddb-norm-equiv (mv-nth 1 (moddb-add-module1
                                            (moddb-add-modinst instname modidx elab-mod moddb)
                                            moddb))
                                 (moddb-add-modinst-to-last
                                  instname modidx
                                  (mv-nth 1 (moddb-add-module1 elab-mod moddb)))))
      :hints(("Goal" :in-theory (enable* moddb-add-modinst-to-last
                                         moddb-add-module1
                                         acl2::arith-equiv-forwarding))))))

(define elab-mod-add-wires ((wires wirelist-p) elab-mod)
  :verbosep t
  :prepwork ((local (defthm wirelist-remove-commute
                      (equal (wirelist-remove-name b (wirelist-remove-name a c))
                             (wirelist-remove-name a (wirelist-remove-name b c)))
                      :hints(("Goal" :in-theory (enable wirelist-remove-name)))))
             (local (defthm wirelist-remove-names-of-remove
                      (equal (wirelist-remove-names c (wirelist-remove-name a b))
                             (wirelist-remove-name a (wirelist-remove-names c b)))
                      :hints(("Goal" :in-theory (enable wirelist-remove-names
                                                        ;; wirelist-remove-name
                                                        )))))
             (local (defthm wirelist-remove-name-of-remove-names-when-member
                      (implies (member name names)
                               (equal (wirelist-remove-name name (wirelist-remove-names names x))
                                      (wirelist-remove-names names x)))
                      :hints(("Goal" :in-theory (enable wirelist-remove-names)))))
             (local (defthm wirelist-remove-names-of-append
                      (equal (wirelist-remove-names (append a b) c)
                             (wirelist-remove-names a (wirelist-remove-names b c)))
                      :hints(("Goal" :in-theory (enable wirelist-remove-names))))))
  :guard-hints (("goal" :in-theory (enable elab-mod$a-add-wire
                                           elab-mod$ap
                                           elab-mod$a-fix
                                           s-redundant)
                 :do-not-induct t
                 :expand ((:free (elab-mod)
                           (elab-mod-add-wires (cdr wires) elab-mod))
                          (:free (a b)
                           (wirelist-rem-dups (cons a b)))
                          (wirelist-rem-dups wires)
                          (:free (a b c)
                           (wirelist-remove-names (cons a b) C)))))
  (mbe :logic (non-exec (s :wires (wirelist-rem-dups
                                   (append (g :wires elab-mod)
                                           wires))
                           (elab-mod-fix elab-mod)))
       :exec
       (if (atom wires)
           (elab-mod-fix elab-mod)
         (let* ((elab-mod (elab-mod-add-wire (car wires) elab-mod)))
           (elab-mod-add-wires (cdr wires) elab-mod)))))

(define moddb-contains-modnames ((x modnamelist-p)
                                 (moddb moddb-basics-ok))
  :enabled t
  (if (atom x)
      t
    (and (moddb-modname-get-index (car x) moddb)
         (moddb-contains-modnames (cdr x) moddb))))

(define modinstlist-add-modinsts ((modinsts modinstlist-p)
                                  (modalist modalist-p)
                                  elab-mod
                                  (moddb moddb-ok))
  :guard-hints (("goal" :expand ((modinstlist->modnames modinsts))
                 :do-not-induct t))
  :guard (moddb-contains-modnames (modinstlist->modnames modinsts) moddb)
  :returns (elab-mod1)
  (b* (((when (atom modinsts)) (elab-mod-fix elab-mod))
       ((modinst inst) (car modinsts))
       (modidx (moddb-modname-get-index inst.modname moddb))
       ((unless (mbt (natp modidx)))
        (modinstlist-add-modinsts (cdr modinsts) modalist elab-mod moddb))
       ((when (elab-mod-instname->idx inst.instname elab-mod))
        (modinstlist-add-modinsts (cdr modinsts) modalist elab-mod moddb))
       (elab-mod (moddb-add-modinst inst.instname modidx elab-mod moddb)))
    (modinstlist-add-modinsts (cdr modinsts) modalist elab-mod moddb))
  ///
  (deffixequiv modinstlist-add-modinsts)

  (defthm modname-of-moddb-add-modinst
    (equal (g :name (moddb-add-modinst instname modidx elab-mod moddb))
           (modname-fix (g :name elab-mod)))
    :hints(("Goal" :in-theory (enable moddb-add-modinst))))

  (defthm modname-of-modinstlist-add-modinsts
    (equal (g :name (modinstlist-add-modinsts modinsts modalist elab-mod moddb))
           (modname-fix (g :name elab-mod))))

  (defthm modinstlist-add-modinsts-preserves-moddb-mods-ok-of-add-module
    (implies (and (moddb-mods-ok (mv-nth 1 (moddb-add-module1 elab-mod moddb)))
                  (not (moddb-modname-get-index (g :name elab-mod) moddb)))
             (moddb-mods-ok
              (mv-nth 1 (moddb-add-module1
                         (modinstlist-add-modinsts modinsts modalist elab-mod moddb)
                         moddb))))))

(defines module->db
  :ruler-extenders :all ;; flag needs this
  (define module->db ((modname modname-p)
                      (modalist modalist-p)
                      (moddb moddb-ok))
    :guard (modhier-loopfree-p modname modalist)
    :returns (moddb1)
    :measure (mod-meas (modname-fix modname) modalist)
    :ruler-extenders :all
    :verify-guards nil
    :short "Copy the wire hierarchy of an SV module into a moddb."
    (b* ((modalist (mbe :logic (modalist-fix modalist) :exec modalist))
         (modname (mbe :logic (modname-fix modname) :exec modname))
         ((when (moddb-modname-get-index modname moddb))
          (moddb-fix moddb))
         (mod (modalist-lookup modname modalist))
         ((acl2::local-stobjs new-elab-mod) (mv new-elab-mod moddb))
         (new-elab-mod (update-elab-mod->name modname new-elab-mod))
         ((unless (and mod
                       (mbt (modhier-loopfree-p modname modalist))))
          (moddb-add-module new-elab-mod moddb))
         (moddb (modinstlist-add-submodules
                 (module->insts mod) modalist moddb))
         (wires (module->wires mod))
         (new-elab-mod (elab-mod-add-wires wires new-elab-mod))
         (new-elab-mod (update-elab-mod->totalwires (elab-mod-nwires new-elab-mod) new-elab-mod))
         (new-elab-mod
          (modinstlist-add-modinsts
           (module->insts mod) modalist new-elab-mod moddb)))
      (moddb-add-module new-elab-mod moddb)))

  (define modinstlist-add-submodules ((modinsts modinstlist-p)
                                      (modalist modalist-p)
                                      (moddb moddb-ok))
    :guard (modhier-loopfreelist-p (modinstlist->modnames modinsts) modalist)
    :returns (moddb1)
    :measure (modinstlist-meas modinsts modalist)
    (b* (((when (atom modinsts)) (moddb-fix moddb))
         (moddb (module->db (modinst->modname (car modinsts)) modalist moddb)))
      (modinstlist-add-submodules (cdr modinsts) modalist moddb)))



  ///

  (deffixequiv-mutual module->db)

  (defthm-module->db-flag
    (defthm modnames-preserved-of-module->db
      (implies (moddb-modname-get-index name moddb)
               (equal (moddb-modname-get-index name (module->db modname modalist moddb))
                      (moddb-modname-get-index name moddb)))
      :hints ('(:expand ((module->db modname modalist moddb))))
      :flag module->db)
    (defthm modnames-preserved-of-modinstlist-add-submodules
      (implies (moddb-modname-get-index name moddb)
               (equal (moddb-modname-get-index
                       name (modinstlist-add-submodules modinsts modalist moddb))
                      (moddb-modname-get-index name moddb)))
      :hints ('(:expand ((modinstlist-add-submodules modinsts modalist moddb))))
      :flag modinstlist-add-submodules)
    :skip-others t)


  (defthm new-modname-of-module->db
    (moddb-modname-get-index modname (module->db modname modalist moddb))
    :hints ('(:expand ((module->db modname modalist moddb))
              :in-theory (enable elab-mod-add-wires))))

  (defthm-module->db-flag
    (defthm new-modnames-of-modinstlist-add-submodules
      (moddb-contains-modnames (modinstlist->modnames modinsts)
                               (modinstlist-add-submodules modinsts modalist moddb))
      :hints ('(:expand ((modinstlist-add-submodules modinsts modalist moddb))))
      :flag modinstlist-add-submodules)
    :skip-others t)

  (defthm-module->db-flag
    (defthm moddb-basics-ok-of-module->db
      (implies (moddb-basics-ok moddb)
               (moddb-basics-ok (module->db modname modalist moddb)))
      :hints ('(:expand ((module->db modname modalist moddb))))
      :flag module->db)
    (defthm moddb-basics-ok-of-modinstlist-add-submodules
      (implies (moddb-basics-ok moddb)
               (moddb-basics-ok (modinstlist-add-submodules modinsts modalist moddb)))
      :hints ('(:expand ((modinstlist-add-submodules modinsts modalist moddb))))
      :flag modinstlist-add-submodules)
    :skip-others t)

  (defthm-module->db-flag
    (defthm module->db-bigger-module-not-added
      (implies (and (not (moddb-modname-get-index name moddb))
                    (< (mod-meas (modname-fix modname) modalist)
                       (mod-meas (modname-fix name) modalist)))
               (not (moddb-modname-get-index name (module->db modname modalist moddb))))
      :hints ('(:expand ((module->db modname modalist moddb))
                :in-theory (enable elab-mod-add-wires)))
      :flag module->db)
    (defthm modinstlist-add-submodules-bigger-module-not-added
      (implies (and (not (moddb-modname-get-index name moddb))
                    (< (modinstlist-meas modinsts modalist)
                       (mod-meas (modname-fix name) modalist)))
               (not (moddb-modname-get-index
                     name (modinstlist-add-submodules modinsts modalist moddb))))
      :hints ('(:expand ((modinstlist-add-submodules modinsts modalist moddb))))
      :flag modinstlist-add-submodules))

  (defthm-module->db-flag
    (defthm moddb-mods-ok-of-module->db
      (implies (moddb-mods-ok moddb)
               (moddb-mods-ok (module->db modname modalist moddb)))
      :hints ('(:expand ((module->db modname modalist moddb))
                :in-theory (enable elab-mod$a-ninsts
                                   elab-mod$a-nwires
                                   elab-mod-add-wires)))
      :flag module->db)
    (defthm moddb-mods-ok-of-modinstlist-add-submodules
      (implies (moddb-mods-ok moddb)
               (moddb-mods-ok (modinstlist-add-submodules modinsts modalist moddb)))
      :hints ('(:expand ((modinstlist-add-submodules modinsts modalist moddb))))
      :flag modinstlist-add-submodules)
    :skip-others t)


  (verify-guards module->db
    :hints(("Goal" :in-theory (enable elab-mod-add-wires)))))


(define moddb-elab-mod-stats ((modidx natp)
                              (moddb moddb-basics-ok))
  :guard (< modidx (moddb->nmods moddb))
  (b* (((stobj-get ninsts nwires totalinsts totalwires)
        ((elab-mod (moddb->modsi modidx moddb)))
        (mv (elab-mod-ninsts elab-mod)
            (elab-mod-nwires elab-mod)
            (elab-mod->totalinsts elab-mod)
            (elab-mod->totalwires elab-mod))))
    (mv ninsts nwires totalinsts totalwires)))






(local
 (defthm natp-of-decr-when-posp
   (implies (posp x)
            (natp (+ -1 x)))
   :rule-classes :type-prescription))



;; (defthm moddb-mod-inst-wireoffset-recursive1
;;   (implies (and (moddb-mods-ok moddb)
;;                 (<= (nfix instidx)
;;                     (elab-mod$a-ninsts (moddb->modsi modidx moddb))))
;;            (equal (moddb-mod-inst-wireoffset instidx modidx moddb)
;;                   (if (>= (nfix modidx) (nfix (moddb->nmods moddb)))
;;                       0
;;                     (if (zp instidx)
;;                         (elab-mod$a-nwires (moddb->modsi modidx moddb))
;;                       (+ (moddb-mod-inst-wireoffset
;;                           (1- instidx) modidx moddb)
;;                          (let* ((submod-idx
;;                                  (elab-mod$a->inst-modidx
;;                                   (1- instidx)
;;                                   (moddb->modsi modidx moddb)))
;;                                 (submod (moddb->modsi submod-idx moddb))
;;                                 (ninsts (elab-mod$a-ninsts submod)))
;;                            (if (< submod-idx (nfix modidx))
;;                                (moddb-mod-inst-wireoffset ninsts submod-idx moddb)
;;                              0)))))))
;;   :hints (("goal" :expand ((moddb-mod-inst-wireoffset instidx modidx moddb)))
;;           (and stable-under-simplificationp
;;                '(:in-theory (enable elab-mod$a->inst-wireoffset
;;                                     elab-mod$a-ninsts))))
;;   :rule-classes nil
;;   :otf-flg t)


(define moddb-mod-nwires ((modidx natp)
                          (moddb moddb-basics-ok))
  :guard (< modidx (moddb->nmods moddb))
  :returns (nwires natp :rule-classes :type-prescription)
  (b* (((unless (mbt (< (lnfix modidx) (moddb->nmods moddb)))) 0)
       ((stobj-get nwires)
        ((elab-mod (moddb->modsi modidx moddb)))
        (elab-mod-nwires elab-mod)))
    nwires))

(define moddb-mod-ninsts ((modidx natp)
                          (moddb moddb-basics-ok))
  :guard (< modidx (moddb->nmods moddb))
  :returns (ninsts natp :rule-classes :type-prescription)
  (b* (((unless (mbt (< (lnfix modidx) (moddb->nmods moddb)))) 0)
       ((stobj-get ninsts)
        ((elab-mod (moddb->modsi modidx moddb)))
        (elab-mod-ninsts elab-mod)))
    ninsts))


(define moddb-mod-totalwires ((modidx natp)
                              (moddb moddb-basics-ok))
  :guard (< modidx (moddb->nmods moddb))
  :returns (totalwires natp :rule-classes :type-prescription)
  (b* (((unless (mbt (< (lnfix modidx) (moddb->nmods moddb)))) 0)
       ((stobj-get totalwires)
        ((elab-mod (moddb->modsi modidx moddb)))
        (elab-mod->totalwires elab-mod)))
    totalwires)
  ///

  (defthm moddb-mod-totalwires-in-terms-of-wireoffset
    (implies (moddb-mods-ok moddb)
             (equal (moddb-mod-totalwires modidx moddb)
                    (moddb-mod-inst-wireoffset (moddb-mod-ninsts modidx moddb)
                                               modidx moddb)))
    :hints(("Goal" :in-theory (enable moddb-mod-ninsts
                                      acl2::nth-when-too-large)
            :expand ((moddb-mod-inst-wireoffset
                       (elab-mod$a-ninsts (nth modidx (nth *moddb->modsi* moddb)))
                       modidx moddb)
                     (MODDB-MOD-INST-WIREOFFSET 0 MODIDX MODDB))))
    :rule-classes ((:definition :install-body nil
                    :clique (moddb-mod-inst-wireoffset
                             moddb-mod-totalwires)
                    :controller-alist ((moddb-mod-inst-wireoffset t t nil)
                                       (moddb-mod-totalwires t nil)))))


  (defthm moddb-mod-inst-wireoffset-recursive
    (implies (moddb-mods-ok moddb)
             (equal (moddb-mod-inst-wireoffset instidx modidx moddb)
                    (if (>= (nfix modidx) (nfix (moddb->nmods moddb)))
                        0
                      (if (or (zp instidx)
                              (zp (elab-mod$a-ninsts (moddb->modsi modidx moddb))))
                          (elab-mod$a-nwires (moddb->modsi modidx moddb))
                        (+ (moddb-mod-inst-wireoffset
                            (1- instidx) modidx moddb)
                           (let* ((submod-idx
                                   (elab-mod$a->inst-modidx
                                    (1- instidx)
                                    (moddb->modsi modidx moddb))))
                             (if (and (< submod-idx (nfix modidx))
                                      (<= (nfix instidx)
                                          (elab-mod$a-ninsts (moddb->modsi modidx moddb))))
                                 (moddb-mod-totalwires submod-idx moddb)
                               0)))))))
    :hints (("goal"
             :expand ((moddb-mod-inst-wireoffset instidx modidx moddb)
                      (moddb-mod-inst-wireoffset 0 modidx moddb)
                      (moddb-mod-inst-wireoffset
                       (elab-mod$a-ninsts (nth modidx (nth *moddb->modsi* moddb)))
                       modidx moddb))
             :cases ((eql (nfix instidx)
                          (elab-mod$a-ninsts (moddb->modsi modidx moddb))))))
    :rule-classes ((:definition :install-body nil
                    :clique (moddb-mod-inst-wireoffset
                             moddb-mod-totalwires)
                    :controller-alist ((moddb-mod-inst-wireoffset t t nil)
                                       (moddb-mod-totalwires t nil)))))

  (defthm moddb-mod-inst-wireoffset-monotonic
    (implies (and (<= (nfix n) (nfix m))
                  (moddb-mods-ok moddb))
             (<= (moddb-mod-inst-wireoffset n modidx moddb)
                 (moddb-mod-inst-wireoffset m modidx moddb)))
    :hints (("goal" :induct (count-down m n)
             :expand ((:with moddb-mod-inst-wireoffset-recursive
                       (moddb-mod-inst-wireoffset m modidx moddb)))))
    :rule-classes (:rewrite :linear))

  (in-theory (Disable moddb-mod-ok-implies-totalwires))
  (defthm moddb-totalwires-rewrite
    (implies (< (nfix modidx) (nfix (moddb->nmods moddb)))
             (nat-equiv (g :totalwires (nth modidx (nth *moddb->modsi* moddb)))
                        (moddb-mod-totalwires modidx moddb))))

  (local (in-theory (Disable moddb-mod-totalwires))))


(define moddb-mod-totalinsts ((modidx natp)
                              (moddb moddb-basics-ok))
  :guard (< modidx (moddb->nmods moddb))
  :returns (totalinsts natp :rule-classes :type-prescription)
  (b* (((unless (mbt (< (lnfix modidx) (moddb->nmods moddb)))) 0)
       ((stobj-get totalinsts)
        ((elab-mod (moddb->modsi modidx moddb)))
        (elab-mod->totalinsts elab-mod)))
    totalinsts)
  ///
  (defthm moddb-mod-totalinsts-in-terms-of-instoffset
    (implies (moddb-mods-ok moddb)
             (equal (moddb-mod-totalinsts modidx moddb)
                    (moddb-mod-inst-instoffset (moddb-mod-ninsts modidx moddb)
                                               modidx moddb)))
    :hints(("Goal" :in-theory (enable moddb-mod-ninsts
                                      acl2::nth-when-too-large)
            :expand ((moddb-mod-inst-instoffset
                      (elab-mod$a-ninsts (nth modidx (nth *moddb->modsi* moddb)))
                      modidx moddb)
                     (MODDB-MOD-INST-INSTOFFSET 0 MODIDX MODDB))))
    :rule-classes ((:definition :install-body nil
                    :clique (moddb-mod-inst-instoffset
                             moddb-mod-totalinsts)
                    :controller-alist ((moddb-mod-inst-instoffset t t nil)
                                       (moddb-mod-totalinsts t nil)))))

  (defthm moddb-mod-inst-instoffset-recursive
    (implies (moddb-mods-ok moddb)
             (equal (moddb-mod-inst-instoffset instidx modidx moddb)
                    (if (or (>= (nfix modidx) (nfix (moddb->nmods moddb)))
                            (zp instidx)
                            (zp (elab-mod$a-ninsts (moddb->modsi modidx moddb))))
                        0
                      (+ (moddb-mod-inst-instoffset
                          (1- instidx) modidx moddb)
                         (let* ((submod-idx
                                 (elab-mod$a->inst-modidx
                                  (1- instidx)
                                  (moddb->modsi modidx moddb))))
                           (if (and (< submod-idx (nfix modidx))
                                    (<= (nfix instidx)
                                        (elab-mod$a-ninsts (moddb->modsi modidx moddb))))
                               (+ 1 (moddb-mod-totalinsts submod-idx moddb))
                             0))))))
    :hints (("goal"
             :expand ((moddb-mod-inst-instoffset instidx modidx moddb)
                      (moddb-mod-inst-instoffset 0 modidx moddb)
                      (moddb-mod-inst-instoffset
                       (elab-mod$a-ninsts (nth modidx (nth *moddb->modsi* moddb)))
                       modidx moddb))
             :cases ((eql (nfix instidx)
                          (elab-mod$a-ninsts (moddb->modsi modidx moddb))))))
    :rule-classes ((:definition :install-body nil
                    :clique (moddb-mod-inst-instoffset
                             moddb-mod-totalinsts)
                    :controller-alist ((moddb-mod-inst-instoffset t t nil)
                                       (moddb-mod-totalinsts t nil)))))

  (defthm moddb-mod-inst-instoffset-monotonic
    (implies (and (<= (nfix n) (nfix m))
                  (moddb-mods-ok moddb))
             (<= (moddb-mod-inst-instoffset n modidx moddb)
                 (moddb-mod-inst-instoffset m modidx moddb)))
    :hints (("goal" :induct (count-down m n)
             :expand ((:with moddb-mod-inst-instoffset-recursive
                       (moddb-mod-inst-instoffset m modidx moddb)))))
    :rule-classes (:rewrite :linear))

  (in-theory (Disable moddb-mod-ok-implies-totalinsts))
  (defthm moddb-totalinsts-rewrite
    (implies (< (nfix modidx) (nfix (moddb->nmods moddb)))
             (nat-equiv (g :totalinsts (nth modidx (nth *moddb->modsi* moddb)))
                        (moddb-mod-totalinsts modidx moddb))))

  (local (in-theory (Disable moddb-mod-totalinsts))))


(defsection elab-mod-of-good-moddb
  (defun-sk elab-mod-of-good-moddb (elab-mod)
    (exists (n moddb)
            (non-exec (and (ec-call (elab-mod$a-equiv (moddb->modsi n moddb) elab-mod))
                           (< (nfix n) (nfix (moddb->nmods moddb)))
                           (moddb-mods-ok moddb)
                           (moddb-basics-ok (ec-call (moddb-norm moddb)))))))

  (defun-nx index-for-good-elab-mod (elab-mod)
    (nfix (mv-nth 0 (elab-mod-of-good-moddb-witness (elab-mod$a-fix elab-mod)))))

  (defun-nx moddb-for-good-elab-mod (elab-mod)
    (moddb-norm (mv-nth 1 (elab-mod-of-good-moddb-witness (elab-mod$a-fix elab-mod)))))

  (defthm elab-mod-of-good-moddb-redef
    (equal (elab-mod-of-good-moddb elab-mod)
           (let ((moddb (moddb-for-good-elab-mod elab-mod))
                 (n (index-for-good-elab-mod elab-mod)))
             (and (moddb-ok moddb)
                  (< (nfix n) (nfix (moddb->nmods moddb)))
                  (elab-mod$a-equiv (moddb->modsi n moddb) elab-mod))))
    :hints (("goal" :cases ((elab-mod-of-good-moddb elab-mod))
             :in-theory (disable elab-mod-of-good-moddb
                                 elab-mod-of-good-moddb-suff)
             :use ((:instance elab-mod-of-good-moddb-suff
                    (n (index-for-good-elab-mod elab-mod))
                    (moddb (moddb-for-good-elab-mod elab-mod)))
                   (:instance elab-mod-of-good-moddb-suff
                    (elab-mod (elab-mod$a-fix elab-mod))
                    (n (mv-nth 0 (elab-mod-of-good-moddb-witness elab-mod)))
                    (moddb (mv-nth 1 (elab-mod-of-good-moddb-witness elab-mod))))))
            (and stable-under-simplificationp
                 '(:expand ((elab-mod-of-good-moddb elab-mod)
                            (elab-mod-of-good-moddb (elab-mod$a-fix elab-mod))))))
    :rule-classes :definition)

  (deffixequiv elab-mod-of-good-moddb :args ((elab-mod elab-modp)))

  (in-theory (Disable elab-mod-of-good-moddb
                      index-for-good-elab-mod
                      moddb-for-good-elab-mod))

  (verify-guards elab-mod-of-good-moddb)

  (defthm elab-mod-of-good-moddb-direct
    (implies (and (< (nfix modidx) (nfix (nth *moddb->nmods* moddb)))
                  (moddb-mods-ok moddb)
                  (moddb-basics-ok (moddb-norm moddb)))
             (elab-mod-of-good-moddb
              (nth modidx (nth *moddb->modsi* moddb))))
    :hints (("goal" :use ((:instance elab-mod-of-good-moddb-suff
                           (elab-mod (nth modidx (nth *moddb->modsi* moddb)))
                           (n modidx)))
             :in-theory (disable elab-mod-of-good-moddb-suff
                                 elab-mod-of-good-moddb)))))


(defsection elab-mod-wiresearch-pivot
  (define elab-mod-wiresearch-smartpivot ((wire natp)
                                          (mininst natp)
                                          (minoffset natp)
                                          (maxinst natp)
                                          (maxoffset natp))
    :guard (and (< (+ 1 mininst) maxinst)
                (<= minoffset wire)
                (< wire maxoffset))
    :returns (pivotinst natp :rule-classes :type-prescription
                        :hints(("Goal" :in-theory (disable floor))))
    :hooks nil
    (b* ((maxinst (mbe :logic (acl2::pos-fix maxinst) :exec maxinst))
         (mininst (lnfix mininst))
         (maxoffset (lnfix maxoffset))
         (minoffset (lnfix minoffset))
         (guess (+ 1 mininst (floor (* (- maxinst mininst) (- wire minoffset))
                                    (- maxoffset minoffset)))))
      (min (+ -1 maxinst) (max (+ 1 mininst) guess)))
    ///
    (defthm elab-mod-wiresearch-smartpivot-lower-bound
      (implies (< (+ 1 (nfix mininst)) (nfix maxinst))
               (< (nfix mininst)
                  (elab-mod-wiresearch-smartpivot wire mininst minoffset maxinst maxoffset)))
      :rule-classes :linear)
    (defthm elab-mod-wiresearch-smartpivot-upper-bound
      (implies (< (+ 1 (nfix mininst)) (nfix maxinst))
               (< (elab-mod-wiresearch-smartpivot wire mininst minoffset maxinst maxoffset)
                  (nfix maxinst)))
      :rule-classes :linear))

  (define elab-mod-wiresearch-dumbpivot ((mininst natp)
                                         (maxinst natp))
    :guard (< (+ 1 mininst) maxinst)
    :hooks nil
    :returns (pivotinst natp :rule-classes :type-prescription
                        :hints(("Goal" :in-theory (disable floor))))
    (b* ((maxinst (mbe :logic (acl2::pos-fix maxinst) :exec maxinst))
         (mininst (lnfix mininst))
         (guess (ash (- maxinst mininst) -1)))
      (min (+ -1 maxinst) (max (+ 1 mininst) guess)))
    ///
    (defthm elab-mod-wiresearch-dumbpivot-lower-bound
      (implies (< (+ 1 (nfix mininst)) (nfix maxinst))
               (< (nfix mininst)
                  (elab-mod-wiresearch-dumbpivot mininst maxinst)))
      :rule-classes :linear)
    (defthm elab-mod-wiresearch-dumbpivot-upper-bound
      (implies (< (+ 1 (nfix mininst)) (nfix maxinst))
               (< (elab-mod-wiresearch-dumbpivot mininst maxinst)
                  (nfix maxinst)))
      :rule-classes :linear))


  (define elab-mod-wiresearch-pivot ((wire natp)
                                     (mininst natp)
                                     (minoffset natp)
                                     (maxinst natp)
                                     (maxoffset natp)
                                     smartp)
    :guard (and (< (+ 1 mininst) maxinst)
                (<= minoffset wire)
                (< wire maxoffset))
    :hooks nil
    :returns (pivotinst natp :rule-classes :type-prescription
                        :hints(("Goal" :in-theory (disable floor))))
    (if smartp
        (elab-mod-wiresearch-smartpivot wire mininst minoffset maxinst maxoffset)
      (elab-mod-wiresearch-dumbpivot mininst maxinst))
    ///
    (defthm elab-mod-wiresearch-pivot-lower-bound
      (implies (< (+ 1 (nfix mininst)) (nfix maxinst))
               (< (nfix mininst)
                  (elab-mod-wiresearch-pivot wire mininst minoffset maxinst maxoffset smartp)))
      :rule-classes :linear)
    (defthm elab-mod-wiresearch-pivot-upper-bound
      (implies (< (+ 1 (nfix mininst)) (nfix maxinst))
               (< (elab-mod-wiresearch-pivot wire mininst minoffset maxinst maxoffset smartp)
                  (nfix maxinst)))
      :rule-classes :linear))


  (define elab-mod-wiresearch-next-smartp ((wire natp)
                                           (pivotoffset natp)
                                           (mininst natp)
                                           (maxinst natp)
                                           smartp
                                           elab-mod)
    :guard (and (< (+ 1 mininst) maxinst)
                (<= maxinst (elab-mod-ninsts elab-mod)))
    :hooks nil
    (b* (((when (not smartp)) t)
         (dumbpivot (elab-mod-wiresearch-dumbpivot mininst maxinst))
         (dumboffset (elab-mod->inst-wireoffset dumbpivot elab-mod)))
      (if (< wire pivotoffset)
          (<= pivotoffset dumboffset)
        (<= dumboffset pivotoffset)))))


(define elab-mod-wire-find-inst-aux ((wire natp)
                                     (mininst natp)
                                     (minoffset natp)
                                     (maxinst natp)
                                     (maxoffset natp)
                                     (smartp
                                      "Try a smart guess for the pivot, versus a dumb binary split")
                                     (elab-mod elab-mod-of-good-moddb))
  :guard (and (< mininst maxinst)
              (<= maxinst (elab-mod-ninsts elab-mod))
              (equal minoffset (elab-mod->inst-wireoffset mininst elab-mod))
              (<= minoffset wire)
              (equal maxoffset (elab-mod-wireoffset maxinst elab-mod))
              (< wire maxoffset))
  :hooks nil
  :guard-hints (("goal" :in-theory (enable elab-mod-inst-wireoffset-norm)))
  :measure (nfix (- (nfix maxinst) (nfix mininst)))
  :returns (inst natp :rule-classes :type-prescription)
  (b* ((maxinst (lnfix maxinst))
       (mininst (lnfix mininst))
       (wire (lnfix wire))
       (maxoffset (mbe :logic (elab-mod-wireoffset maxinst elab-mod)
                       :exec maxoffset))
       (minoffset (mbe :logic (elab-mod->inst-wireoffset mininst elab-mod)
                       :exec minoffset))
       ((when (<= maxinst (+ 1 mininst))) mininst)
       (pivot (elab-mod-wiresearch-pivot wire
                                         mininst
                                         minoffset
                                         maxinst
                                         maxoffset
                                         smartp))
       (pivotoffset (elab-mod->inst-wireoffset pivot elab-mod))
       (smartp-next (elab-mod-wiresearch-next-smartp wire pivotoffset mininst maxinst smartp elab-mod)))
    (if (< wire pivotoffset)
        (elab-mod-wire-find-inst-aux
         wire mininst minoffset pivot pivotoffset smartp-next elab-mod)
      (elab-mod-wire-find-inst-aux
       wire pivot pivotoffset maxinst maxoffset smartp-next elab-mod)))
  ///
  (defthm elab-mod-wire-find-inst-aux-norm
    (implies (syntaxp (not (and (equal minoffset ''0)
                                (equal maxoffset ''0))))
             (equal (elab-mod-wire-find-inst-aux wire mininst minoffset maxinst maxoffset smartp elab-mod)
                    (elab-mod-wire-find-inst-aux wire mininst 0 maxinst 0 smartp elab-mod))))

  (defthm elab-mod-wire-find-inst-aux-upper-bound
    (implies (< (nfix mininst) (nfix maxinst))
             (< (elab-mod-wire-find-inst-aux wire mininst minoffset maxinst maxoffset smartp elab-mod)
                (nfix maxinst)))
    :rule-classes :linear)

  (defthm elab-mod-wire-find-inst-aux-lower-bound
    (implies (< (nfix mininst) (nfix maxinst))
             (<= (nfix mininst)
                 (elab-mod-wire-find-inst-aux
                  wire mininst minoffset maxinst maxoffset smartp elab-mod)))
    :rule-classes :linear)

  (defthm elab-mod-wire-find-inst-aux-correct1
    (implies (and (< (nfix mininst) (nfix maxinst))
                  (<= (elab-mod->inst-wireoffset mininst elab-mod) (nfix wire))
                  (< (nfix wire) (elab-mod-wireoffset maxinst elab-mod))
                  (<= (nfix maxinst) (elab-mod$a-ninsts elab-mod))
                  (elab-mod-of-good-moddb elab-mod))
             (<= (elab-mod-wireoffset
                  (elab-mod-wire-find-inst-aux
                   wire mininst minoffset maxinst maxoffset smartp elab-mod)
                  elab-mod)
                 (nfix wire)))
    :hints (("goal" :induct (elab-mod-wire-find-inst-aux
                             wire mininst minoffset maxinst maxoffset smartp elab-mod)
             :expand ((elab-mod-wire-find-inst-aux
                       wire mininst minoffset maxinst maxoffset smartp elab-mod))
             :in-theory (e/d (elab-mod-inst-wireoffset-norm)))
            (and stable-under-simplificationp
                 '(:expand ((nfix (+ -1 maxinst))))))
    :rule-classes :linear)

  (defthm elab-mod-wire-find-inst-aux-correct2
    (implies (and (< (nfix mininst) (nfix maxinst))
                  (<= (elab-mod->inst-wireoffset mininst elab-mod) (nfix wire))
                  (< (nfix wire) (elab-mod-wireoffset maxinst elab-mod))
                  (<= (nfix maxinst) (elab-mod$a-ninsts elab-mod))
                  (elab-mod-of-good-moddb elab-mod))
             (< (nfix wire)
                (elab-mod-wireoffset
                 (+ 1 (elab-mod-wire-find-inst-aux
                       wire mininst minoffset maxinst maxoffset smartp elab-mod))
                 elab-mod)))
    :hints (("goal" :induct (elab-mod-wire-find-inst-aux
                             wire mininst minoffset maxinst maxoffset smartp elab-mod)
             :expand ((elab-mod-wire-find-inst-aux
                       wire mininst minoffset maxinst maxoffset smartp elab-mod))
             :in-theory (e/d (elab-mod-inst-wireoffset-norm)))
            (and stable-under-simplificationp
                 '(:expand ((nfix (+ -1 maxinst))))))
    :rule-classes :linear))


;; BOZO maybe we should normalize to moddb-mod-inst-wireoffset much earlier in the file?
(local (defthm moddb-mod-ok-implies-wireoffset-free
         (implies (and (elab-mod$a-equiv elab-mod (nth modidx (nth *moddb->modsi* moddb)))
                       (moddb-mod-ok modidx moddb)
                       (< (nfix modidx) (nfix (nth *moddb->nmods* moddb))))
                  (equal (elab-mod-wireoffset instidx elab-mod)
                         (moddb-mod-inst-wireoffset instidx modidx moddb)))
         :hints(("Goal" :in-theory (disable elab-mod$a-equiv)))))

;; (defthm EQUAL-OF-ELAB-MOD$A-FIX-both-FORWARD-TO-ELAB-MOD$A-EQUIV
;;   (implies (equal (elab-mod$a-fix x) (elab-mod$a-fix y))
;;            (elab-mod$a-equiv x y))
;;   :rule-classes :forward-chaining)

(define elab-mod-wire-find-inst ((wire natp)
                                 (elab-mod elab-mod-of-good-moddb))
  :prepwork ((local (in-theory (enable elab-mod-inst-wireoffset-norm
                                       elab-mod-totalwires-norm))))
  :guard (and (<= (elab-mod-nwires elab-mod) wire)
              (< wire (elab-mod->totalwires elab-mod)))
  :otf-flg t
  :verbosep t
  (flet ((fn (wire elab-mod)
             (if (<= (elab-mod-ninsts elab-mod) 1)
                 0
               (elab-mod-wire-find-inst-aux
                (lnfix wire) 0 (elab-mod-nwires elab-mod)
                (elab-mod-ninsts elab-mod)
                (elab-mod->totalwires elab-mod)
                t elab-mod))))
    (mbe :logic (non-exec (let ((elab-mod (elab-mod-fix elab-mod)))
                            (fn wire elab-mod)))
         :exec (fn wire elab-mod)))
  ///

  (defthm elab-mod-wire-find-inst-upper-bound
    (implies (< 0 (elab-mod$a-ninsts elab-mod))
             (< (elab-mod-wire-find-inst wire elab-mod)
                (elab-mod$a-ninsts elab-mod)))
    :rule-classes (:rewrite :linear))

  (defthm elab-mod-wire-find-inst-correct1
    (implies (and (<= (elab-mod-nwires elab-mod) (nfix wire))
                  (< (nfix wire) (elab-mod->totalwires elab-mod))
                  (elab-mod-of-good-moddb elab-mod))
             (<= (elab-mod-wireoffset
                  (elab-mod-wire-find-inst wire elab-mod)
                  elab-mod)
                 (nfix wire)))
    :hints (("goal" :use ((:instance elab-mod-wire-find-inst-aux-correct1
                           (mininst 0) (maxinst (elab-mod$a-ninsts elab-mod))
                           (smartp t) (wire (nfix wire))
                           (elab-mod (elab-mod-fix elab-mod))))
             :in-theory (disable elab-mod-wire-find-inst-aux-correct1)))
    :rule-classes :linear)

  (defthm elab-mod-wire-find-inst-correct2
    (implies (and (<= (elab-mod-nwires elab-mod) (nfix wire))
                  (< (nfix wire) (elab-mod->totalwires elab-mod))
                  (elab-mod-of-good-moddb elab-mod))
             (< (nfix wire)
                (elab-mod-wireoffset
                 (+ 1 (elab-mod-wire-find-inst wire elab-mod))
                 elab-mod)))
    :hints (("goal" :use ((:instance elab-mod-wire-find-inst-aux-correct2
                           (mininst 0) (maxinst (elab-mod$a-ninsts elab-mod))
                           (smartp t) (wire (nfix wire))
                           (elab-mod (elab-mod-fix elab-mod))))
             :in-theory (disable elab-mod-wire-find-inst-aux-correct1)))
    :rule-classes :linear))


(defthm len-of-elab-modinsts-rem-dups
  (equal (len (elab-modinsts-rem-dups insts))
         (len (acl2::remove-later-duplicates
               (elab-modinst-list-names insts))))
  :hints (("goal" :Use ((:instance LEN-OF-ELAB-MODINST-LIST-NAMES
                         (x (elab-modinsts-rem-dups insts))))
           :in-theory (disable len-of-elab-modinst-list-names))))

(local (in-theory (disable
                   (:rewrite nth-of-elab-modlist-fix))))

(define moddb-wireidx->path/decl ((wireidx natp)
                                  (modidx natp)
                                  (moddb moddb-ok))
  :parents (moddb)
  :short "Convert a wire index to a path relative to the module it's in, and additionally
          return the wire declaation."
  :verify-guards nil
  :guard (and (< modidx (moddb->nmods moddb))
              (< wireidx (moddb-mod-totalwires modidx moddb)))
  :measure (nfix modidx)
  :returns (mv (path (path-p path))
               (wire (wire-p wire)))
  :prepwork ((local (in-theory (disable acl2::nth-when-too-large-cheap
                                        acl2::nfix-when-not-natp
                                        acl2::nth-when-atom
                                        acl2::natp-rw))))
  :hooks ((:fix :hints (("goal" :induct (moddb-wireidx->path/decl wireidx modidx moddb)
                         :expand ((:free (moddb) (moddb-wireidx->path/decl wireidx modidx moddb)))))))
  (b* ((wireidx (lnfix wireidx))
       (modidx (lnfix modidx))
       ((unless (mbt (< modidx (moddb->nmods moddb))))
        ;; impossible
        (mv (path-fix nil) (wire-fix nil)))
       ((stobj-get donep wire/name nextmod nextwire)
        ((elab-mod (moddb->modsi modidx moddb)))
        (b* (((unless (mbt (< wireidx (elab-mod->totalwires elab-mod))))
              (mv t (wire-fix nil) nil nil))
             ((when (< wireidx (elab-mod-nwires elab-mod)))
              (mv t (elab-mod-wiretablei wireidx elab-mod) nil nil))
             (inst (elab-mod-wire-find-inst wireidx elab-mod))
             (name (elab-mod->instname inst elab-mod))
             (nextmod (elab-mod->inst-modidx inst elab-mod))
             (offset (elab-mod->inst-wireoffset inst elab-mod))
             (nextwire (- wireidx offset)))
          (mv nil name nextmod nextwire)))
       ((when donep) ;; done
        (mv (make-path-wire :name (wire->name wire/name)) wire/name))
       ((unless (mbt (< nextmod modidx)))
        (mv (path-fix nil) (wire-fix nil)))
       ((mv subpath wire) (moddb-wireidx->path/decl nextwire nextmod moddb)))
    (mv (make-path-scope :subpath subpath
                         :namespace wire/name)
        wire))
  ///
  (local (defthm have-insts-when-totalwires->-nwires
           (implies (and (elab-mod-of-good-moddb elab-mod)
                         (< (elab-mod$a-nwires elab-mod)
                            (elab-mod$a->totalwires elab-mod)))
                    (< 0 (elab-mod$a-ninsts elab-mod)))
           :hints(("Goal" :in-theory (e/d (elab-mod-totalwires-norm
                                           elab-mod-of-good-moddb-redef)
                                          (elab-mod$a-equiv))))
           :rule-classes (:rewrite :linear)))


  (verify-guards moddb-wireidx->path/decl
    :hints (("goal" :in-theory (disable elab-mod-of-good-moddb-redef
                                        elab-mod-wire-find-inst-correct1
                                        elab-mod-wire-find-inst-correct2)
             :use ((:instance elab-mod-wire-find-inst-correct1
                    (elab-mod (nth modidx (nth *moddb->modsi* moddb)))
                    (wire wireidx))
                   (:instance elab-mod-wire-find-inst-correct2
                    (elab-mod (nth modidx (nth *moddb->modsi* moddb)))
                    (wire wireidx)))
             :do-not-induct t))))


(define moddb-wireidx->path ((wireidx natp)
                             (modidx natp)
                             (moddb moddb-ok))
  :parents (moddb)
  :short "Convert a wire index to a path relative to the module it's in."
  :guard (and (< modidx (moddb->nmods moddb))
              (< wireidx (moddb-mod-totalwires modidx moddb)))
  :returns (path path-p)
  ;; (b* ((wireidx (lnfix wireidx))
  ;;      (modidx (lnfix modidx))
  ;;      ((unless (mbt (< modidx (moddb->nmods moddb))))
  ;;       (make-path-wire :name "ERROR"))
  ;;      ((stobj-get donep name nextmod nextwire)
  ;;       ((elab-mod (moddb->modsi modidx moddb)))
  ;;       (b* (((unless (mbt (< wireidx (elab-mod->totalwires elab-mod))))
  ;;             (mv t "ERROR" nil nil))
  ;;            ((when (< wireidx (elab-mod-nwires elab-mod)))
  ;;             (mv t (wire->name (elab-mod-wiretablei wireidx elab-mod)) nil nil))
  ;;            (inst (elab-mod-wire-find-inst wireidx elab-mod))
  ;;            (name (elab-mod->instname inst elab-mod))
  ;;            (nextmod (elab-mod->inst-modidx inst elab-mod))
  ;;            (offset (elab-mod->inst-wireoffset inst elab-mod))
  ;;            (nextwire (- wireidx offset)))
  ;;         (mv nil name nextmod nextwire)))
  ;;      ((when donep) (make-path-wire :name name))
  ;;      ((unless (mbt (< nextmod modidx)))
  ;;       (make-path-wire :name "ERROR")))
  ;;   (make-path-scope :subpath (moddb-wireidx->path nextwire nextmod moddb)
  ;;                    :namespace name))
  (b* (((mv path ?wire) (moddb-wireidx->path/decl wireidx modidx moddb)))
    path))


(define moddb-path->wireidx/decl ((path path-p)
                                  (modidx natp)
                                  (moddb moddb-ok))
  :prepwork ((local (in-theory (disable acl2::nth-when-too-large-cheap
                                        len acl2::nth-when-atom))))
  :parents (moddb)
  :short "Convert a wire path relative to a module into a wire index and get
its wire structure.  The path may have one extra numeric component which is
checked to see if it is a valid bitselect and returned as a separate value."
  :guard (< modidx (moddb->nmods moddb))
  :returns (mv (errmsg)
               (wire (implies (not errmsg) (wire-p wire)))
               (idx (implies (not errmsg) (natp idx)) :rule-classes :type-prescription)
               (bitsel acl2::maybe-natp :rule-classes :type-prescription))
  :verify-guards nil
  :measure (path-count path)
  (path-case path
    :wire
    (b* (((stobj-get err idx wire)
          ((elab-mod (moddb->modsi modidx moddb)))
          (b* ((idx (elab-mod-wirename->idx path.name elab-mod))
               ((unless idx)
                (mv (msg "In module ~x0: Missing: ~s1" (elab-mod->name elab-mod) path.name)
                    nil nil))
               (wire (elab-mod-wiretablei idx elab-mod)))
            (mv nil idx wire)))
         ((when err) (mv err nil nil nil)))
      (mv nil wire idx nil))
    :scope
    (b* ((bit ;; Check for a possible bitselect, in which case this scopename
              ;; may actually be the wirename.
          (path-case path.subpath
            :wire (and (natp path.subpath.name) path.subpath.name)
            :scope nil))
         ((stobj-get ;; We either have a bitselect, an index into a submod, or
                     ;; it might be that both work.
           wireidx wire  ;; bitselect case
           offset submod     ;; submod case
           modname
           err)              ;; neither
          ((elab-mod (moddb->modsi modidx moddb)))
          (b* (;; first check for bitselect.  The next path component must be
               ;; the end and must have a name that's a natural.
               (wireidx (and bit (elab-mod-wirename->idx path.namespace elab-mod)))
               (instidx (elab-mod-instname->idx path.namespace elab-mod))
               (modname (elab-mod->name elab-mod))
               ((unless (or instidx wireidx))
                (mv nil nil nil nil modname (msg "missing: ~s0" path.namespace))))

            (mv wireidx
                (and wireidx (elab-mod-wiretablei wireidx elab-mod))
                (and instidx (elab-mod->inst-wireoffset instidx elab-mod))
                (and instidx (elab-mod->inst-modidx instidx elab-mod))
                modname
                nil)))
         ((when err) (mv (msg "In module ~x0: ~@1" modname err) nil nil nil))
         ((mv err submod-wire rest-index bitsel)
          (if submod
              (moddb-path->wireidx/decl path.subpath submod moddb)
            (mv (msg "In module ~x0: missing submod: ~s1" modname path.namespace)
                nil nil nil)))
         ((unless err) (mv nil submod-wire (+ offset rest-index) bitsel))
         ((unless wire) (mv err nil nil nil))
         ((wire wire))
         (in-bounds (and (>= bit wire.low-idx)
                         (< bit (+ wire.low-idx wire.width))))
         ((unless in-bounds)
          (mv (msg "In module ~x0: bitselect out of bounds: ~x1" modname bit) nil nil nil)))
      (mv nil wire wireidx bit)))
  ///

  (local (in-theory (disable (:d moddb-path->wireidx/decl))))

  (local (defthm elab-mod$a-instname->idx-bound
           (implies (elab-mod$a-instname->idx name elab-mod$a)
                    (< (elab-mod$a-instname->idx name elab-mod$a)
                       (elab-mod$a-ninsts elab-mod$a)))
           :hints(("Goal" :in-theory (enable elab-mod$a-ninsts
                                             elab-mod$a-instname->idx)))
           :rule-classes :linear))

  (local (defthm len-of-wirelist-rem-dups
           (equal (len (wirelist-rem-dups wires))
                  (len (acl2::remove-later-duplicates
                        (wirelist->names wires))))
           :hints (("goal" :Use ((:instance LEN-OF-wirelist->NAMES
                                  (x (wirelist-rem-dups wires))))
                    :in-theory (disable len-of-wirelist->names)))))

  (local (defthm elab-mod$a-wirename->idx-bound
           (implies (elab-mod$a-wirename->idx name elab-mod$a)
                    (< (elab-mod$a-wirename->idx name elab-mod$a)
                       (elab-mod$a-nwires elab-mod$a)))
           :hints(("Goal" :in-theory (enable elab-mod$a-nwires
                                             elab-mod$a-wirename->idx)))
           :rule-classes :linear))

  (verify-guards moddb-path->wireidx/decl)


  (deffixequiv moddb-path->wireidx/decl)

  (local (defthm rem-dups-of-wirelist->names
           (equal (acl2::remove-later-duplicates (wirelist->names x))
                  (wirelist->names (wirelist-rem-dups x)))
           :hints(("Goal" :in-theory (enable wirelist->names wirelist-rem-dups
                                             acl2::remove-later-duplicates)))))
  (local (in-theory (disable WIRELIST->NAMES-OF-REMOVE-DUPLICATE-NAMES
                             len-of-wirelist-rem-dups)))

  (defret moddb-path->wireidx/decl-bound
      (implies (and (moddb-ok moddb)
                    (< (nfix modidx) (nfix (nth *moddb->nmods* moddb)))
                    (not errmsg))
               (< idx (moddb-mod-totalwires modidx moddb)))
    :hints (("goal" :induct t :do-not '(preprocess)
             :expand ((:with moddb-mod-totalwires-in-terms-of-wireoffset
                       (moddb-mod-totalwires modidx moddb))
                      (moddb-path->wireidx/decl path modidx moddb))
             :in-theory (enable moddb-mod-ninsts))
            (and stable-under-simplificationp
                 (if (member-equal '(not (equal (path-kind$inline path) ':wire)) clause)
                     '(:in-theory (e/d (elab-mod$a-wirename->idx
                                        elab-mod$a-nwires)
                                       (moddb-mod-inst-wireoffset-monotonic))
                       :use ((:instance moddb-mod-inst-wireoffset-monotonic
                              (n 0) (m (elab-mod$a-ninsts (nth modidx (nth *moddb->modsi* moddb)))))))
                   '(:in-theory (e/d (;; elab-mod$a-wirename->idx
                                      ;;   elab-mod$a-nwires
                                        )
                                     (moddb-mod-inst-wireoffset-monotonic))
                     :use ((:instance moddb-mod-inst-wireoffset-monotonic
                            (n 0) (m (elab-mod$a-ninsts (nth modidx (nth *moddb->modsi* moddb)))))
                           (:instance moddb-mod-inst-wireoffset-monotonic
                            (n (+ 1 (elab-mod$a-instname->idx (path-scope->namespace path)
                                                              (nth modidx (nth *moddb->modsi* moddb)))))
                            (m (elab-mod$a-ninsts (nth modidx (nth *moddb->modsi* moddb))))))
                     :expand ((moddb-mod-inst-wireoffset
                               (+ 1 (elab-mod$a-instname->idx (path-scope->namespace path)
                                                              (nth modidx (nth *moddb->modsi* moddb))))
                               modidx moddb))))))
    :rule-classes :linear))



(define moddb-path->wireidx ((path path-p)
                             (modidx natp)
                             (moddb moddb-ok))
  :prepwork ((local (in-theory (disable acl2::nth-when-too-large-cheap
                                        len acl2::nth-when-atom))))
  :parents (moddb)
  :short "Convert a wire path relative to a module into a wire index."
  :guard (< modidx (moddb->nmods moddb))
  :returns (idx (iff (natp idx) idx))

  (b* (((mv err & idx bitsel)
        (moddb-path->wireidx/decl path modidx moddb))
       ((when err)
        (b* (((stobj-get name)
              ((elab-mod (moddb->modsi modidx moddb)))
              (elab-mod->name elab-mod)))
          (cw "Error looking up ~x1: ~@0~%from module: ~x2~%"
                          err path name)))
       ((when bitsel) (cw "Didn't expect a bit select: ~x0" path)))
    idx)
  ///

  (deffixequiv moddb-path->wireidx)

  (defret moddb-path->wireidx-type
    (or (not idx) (natp idx))
    :rule-classes :type-prescription)

  (defret moddb-path->wireidx-bound
      (implies (and (moddb-ok moddb)
                    (< (nfix modidx) (nfix (nth *moddb->nmods* moddb)))
                    idx)
               (< idx (moddb-mod-totalwires modidx moddb)))
    :rule-classes :linear))




(define moddb-path->wiredecl ((path path-p)
                              (modidx natp)
                              (moddb moddb-ok))
  :prepwork ((local (defthm moddb-path->wiredecl-wire-exists
                      (b* (((mv err wire & &)
                            (moddb-path->wireidx/decl path modidx moddb)))
                        (implies (not err) wire))
                      :hints (("goal" :in-theory (disable return-type-of-moddb-path->wireidx/decl.wire)
                               :use return-type-of-moddb-path->wireidx/decl.wire)))))
  :guard (< modidx (moddb->nmods moddb))
  :returns (wire (iff (wire-p wire) wire))
  (b* (((mv err wire & bitsel)
        (moddb-path->wireidx/decl path modidx moddb))
       ((when err) (raise "~@0" err))
       ((when bitsel) (raise "Didn't expect a bit select: ~x0" path)))
    wire)
  ///

  (defthm moddb-path->wiredecl-iff-wireidx
    (iff (moddb-path->wiredecl path modidx moddb)
         (moddb-path->wireidx path modidx moddb))
    :hints(("Goal" :in-theory (e/d (moddb-path->wireidx)))))

  (deffixequiv moddb-path->wiredecl))

(defsection modscope
  (fty::deftagsum modscope
    :short "A module context within a moddb."
    :long "<p>A :top modscope describes the top level of hierarchy within a moddb,
         giving its module index.  :Nested modscopes describe nested scopes within
         it, i.e. a descent down the hierarchy through module instantiation. These
         each give the index of the nested module and the wire and instance
         offsets.</p>"
    (:top
     ((modidx natp :rule-classes :type-prescription))
     :layout :tree)
    (:nested
     ((modidx natp :rule-classes :type-prescription)
      (wireoffset natp :rule-classes :type-prescription)
      (instoffset natp :rule-classes :type-prescription)
      (upper modscope))
     :layout :tree))


  (define modscope->modidx ((x modscope-p))
    :returns (modidx natp :rule-classes :type-prescription)
    (modscope-case x
      :top x.modidx
      :nested x.modidx))

  (define modscope->wireoffset ((x modscope-p))
    :returns (wireoffset natp :rule-classes :type-prescription)
    (modscope-case x
      :top 0
      :nested x.wireoffset))

  (define modscope->instoffset ((x modscope-p))
    :returns (instoffset natp :rule-classes :type-prescription)
    (modscope-case x
      :top 0
      :nested x.instoffset))

  (def-b*-binder modscope
    :body
    (std::da-patbind-fn
     'modscope
     '((modidx . modscope->modidx)
       (wireoffset . modscope->wireoffset)
       (instoffset . modscope->instoffset))
     args acl2::forms acl2::rest-expr))

  ;; (deflist modscope :elt-type modframe
  ;;   :short "A list of modframe objects representing nested scopes in a moddb.")


  (define modscope-okp ((x modscope-p)
                        (moddb moddb-ok))
    :parents (moddb)
    :short "Checks whether a modscope is well-formed, in that the module indices
          make sense and each nested module's wire/instance indices are completely
          contained within those of the outer module."
    :prepwork ((local (in-theory (disable acl2::nth-when-too-large-cheap))))
    :hooks ((:fix :hints (("goal" :induct (modscope-okp x moddb)
                           :expand ((:free (moddb) (modscope-okp x moddb))
                                    (:free (moddb)
                                     (modscope-okp (modscope-fix x) moddb)))))))
    :measure (modscope-count x)
    :verify-guards nil
    (modscope-case x
      :top (< x.modidx (moddb->nmods moddb))
      :nested
      (b* (((unless (< x.modidx (moddb->nmods moddb))) nil)
           ((unless (modscope-okp x.upper moddb)) nil)
           ((modscope f2) x.upper)
           (f2-totalwires (moddb-mod-totalwires f2.modidx moddb))
           (f2-totalinsts (moddb-mod-totalinsts f2.modidx moddb))
           (f1-totalwires (moddb-mod-totalwires x.modidx moddb))
           (f1-totalinsts (moddb-mod-totalinsts x.modidx moddb)))

        (and (<= f2.wireoffset x.wireoffset)
             (<= (+ f1-totalwires x.wireoffset)
                 (+ f2-totalwires f2.wireoffset))
             (<= f2.instoffset x.instoffset)
             (<= (+ f1-totalinsts x.instoffset)
                 (+ f2-totalinsts f2.instoffset)))))
    ///
    (local (in-theory (enable modscope->modidx modscope->wireoffset modscope->instoffset)))

    (defthm modscope-okp-implies-top-modidx-in-bounds
      (implies (modscope-okp x moddb)
               (and (< (modscope->modidx x) (nth *moddb->nmods* moddb))
                    (< (modscope->modidx x) (nfix (nth *moddb->nmods* moddb)))))
      :rule-classes (:rewrite :linear))

    (verify-guards modscope-okp)

    (local (in-theory (disable (:d modscope-okp)))))

  (define modscope-push-frame ((instidx natp)
                               (x modscope-p)
                               (moddb moddb-ok))
    :short "Push an instantiation onto a modscope, given by the instance index within
          the current module."
    :guard (and (modscope-okp x moddb)
                (< instidx
                   (b* ((modidx (modscope->modidx x))
                        ((stobj-get ninsts)
                         ((elab-mod (moddb->modsi modidx moddb)))
                         (elab-mod-ninsts elab-mod)))
                     ninsts)))
    :returns (new-x modscope-p)
    :prepwork ((local (in-theory (disable acl2::nth-when-too-large-cheap))))
    (b* (((modscope x))
         ((stobj-get modidx wireoffset instoffset)
          ((elab-mod (moddb->modsi x.modidx moddb)))
          (mv (elab-mod->inst-modidx instidx elab-mod)
              (elab-mod->inst-wireoffset instidx elab-mod)
              (elab-mod->inst-instoffset instidx elab-mod))))
      (make-modscope-nested :modidx modidx
                            :wireoffset (+ wireoffset x.wireoffset)
                            :instoffset (+ instoffset x.instoffset)
                            :upper x))
    ///
    (more-returns
     (new-x :name modscope-okp-of-modscope-push-frame
            (implies (and (modscope-okp x moddb)
                          (moddb-ok moddb)
                          (< (nfix instidx)
                             (b* ((modidx (modscope->modidx x))
                                  ((stobj-get ninsts)
                                   ((elab-mod (moddb->modsi modidx moddb)))
                                   (elab-mod-ninsts elab-mod)))
                               ninsts)))
                     (modscope-okp new-x moddb))
            :hints (("goal" :expand ((:free (a b c d)
                                      (modscope-okp (modscope-nested a b c d) moddb))
                                     (:with moddb-mod-totalinsts-in-terms-of-instoffset
                                      (moddb-mod-totalinsts (modscope->modidx x) moddb)))
                     :use ((:instance moddb-mod-inst-instoffset-monotonic
                            (n (+ 1 (nfix instidx)))
                            (m (elab-mod-ninsts (moddb->modsi (modscope->modidx x) moddb)))
                            (modidx (modscope->modidx x)))
                           (:instance moddb-mod-inst-wireoffset-monotonic
                            (n (+ 1 (nfix instidx)))
                            (m (elab-mod-ninsts (moddb->modsi (modscope->modidx x) moddb)))
                            (modidx (modscope->modidx x))))
                     :in-theory (e/d (moddb-mod-ninsts)
                                     (moddb-mod-inst-instoffset-monotonic
                                      moddb-mod-inst-wireoffset-monotonic)))))
     (new-x :name modidx-bound-of-modscope-push-frame
            (implies (and (modscope-okp x moddb)
                          (moddb-ok moddb)
                          (< (nfix instidx)
                             (b* ((modidx (modscope->modidx x))
                                  ((stobj-get ninsts)
                                   ((elab-mod (moddb->modsi modidx moddb)))
                                   (elab-mod-ninsts elab-mod)))
                               ninsts)))
                     (< (modscope->modidx new-x)
                        (modscope->modidx x)))
            :hints(("Goal" :in-theory (enable modscope->modidx))))))


  (define modscope->top ((x modscope-p))
    :short "Given some modscope, pop all the way out to the top level."
    :returns (top modscope-p)
    :measure (modscope-count x)
    (modscope-case x
      :top (modscope-fix x)
      :nested (modscope->top x.upper))
    ///
    (defthm modscope-okp-of-modscope->top
      (implies (modscope-okp x moddb)
               (modscope-okp (modscope->top x) moddb))
      :hints(("Goal" :in-theory (enable modscope-okp))))

    (local (in-theory (disable acl2::nth-when-too-large-cheap
                               moddb-mod-inst-wireoffset-recursive
                               moddb-mod-inst-instoffset-recursive
                               moddb-path->wireidx-bound)))

    (defthm modscope-okp-wireoffset-lower-bound
      (implies (modscope-okp x moddb)
               (<= (modscope->wireoffset (modscope->top x))
                   (modscope->wireoffset x)))
      :hints(("Goal" :in-theory (enable modscope-okp modscope->wireoffset)))
      :rule-classes (:rewrite :linear))


    (defthm modscope-okp-wireidx-bound
      ;; This says that the maximum wire index of the current module can never be
      ;; greater than the maximum wire index of the top module.
      (implies (and (modscope-okp x moddb)
                    (moddb-ok moddb))
               (<= (+ (modscope->wireoffset x)
                      (moddb-mod-totalwires (modscope->modidx x) moddb))
                   (moddb-mod-totalwires
                    (modscope->modidx (modscope->top x))
                    moddb)))
      :hints (("goal" :induct (modscope->top x)
               :expand ((modscope-okp x moddb)))
              (and stable-under-simplificationp
                   '(:in-theory (enable modscope->wireoffset
                                        modscope->modidx))))
      :rule-classes (:rewrite :linear))

    (defthm modscope->offsets-of-modscope->top
      (and (equal (modscope->wireoffset (modscope->top x)) 0)
           (equal (modscope->instoffset (modscope->top x)) 0))
      :hints(("Goal" :in-theory (enable modscope->wireoffset
                                        modscope->instoffset))))

    (defthm modscope->top-of-modscope-push-frame
      (equal (modscope->top (modscope-push-frame idx scope moddb))
             (modscope->top scope))
      :hints(("Goal" :in-theory (enable modscope-push-frame)))))



  (define modscope->nth ((n natp) (x modscope-p))
    :short "Given some modscope, pop out n frames."
    :returns (top modscope-p)
    :measure (modscope-count x)
    (if (zp n)
        (modscope-fix x)
      (modscope-case x
        :top (modscope-fix x)
        :nested (modscope->nth (1- n) x.upper)))
    ///
    (defthm modscope-okp-of-modscope->nth
      (implies (modscope-okp x moddb)
               (modscope-okp (modscope->nth n x) moddb))
      :hints(("Goal" :in-theory (enable modscope-okp))))

    (defthm modscope->top-of-nth
      (equal (modscope->top (modscope->nth n x))
             (modscope->top x))
      :hints(("Goal" :in-theory (enable modscope->top))))

    (defthm modscope-okp-nth-wireoffset-lower-bound
      (implies (modscope-okp x moddb)
               (<= (modscope->wireoffset (modscope->top x))
                   (modscope->wireoffset (modscope->nth n x))))
      :hints(("Goal" :use ((:instance modscope-okp-wireoffset-lower-bound
                            (x (modscope->nth n x))))))
      :rule-classes (:rewrite :linear))

    (defthm modscope-okp-nth-wireidx-bound
      ;; This says that the maximum wire index of the current module can never be
      ;; greater than the maximum wire index of the top module.
      (implies (and (modscope-okp x moddb)
                    (moddb-ok moddb))
               (<= (+ (modscope->wireoffset (modscope->nth n x))
                      (moddb-mod-totalwires
                       (modscope->modidx (modscope->nth n x)) moddb))
                   (moddb-mod-totalwires
                    (modscope->modidx (modscope->top x))
                    moddb)))
      :hints (("goal" :use ((:instance modscope-okp-wireidx-bound
                             (x (modscope->nth n x))))))
      :rule-classes (:rewrite :linear))))

(define moddb-address->wireidx ((addr  address-p)
                                (scope (modscope-p scope))
                                (moddb moddb-ok))
  :guard (modscope-okp scope moddb)
  :parents (moddb)
  :short "Convert a wire address into a wire index, given the scope from which
          the address is relative."
  :returns (idx (iff (natp idx) idx))
  (b* (((address addr))
       ((modscope scope1)
        (if (eq addr.scope :root)
            (modscope->top scope)
          (modscope->nth addr.scope scope)))
       (local-idx (moddb-path->wireidx addr.path scope1.modidx moddb)))
    (and local-idx
         (+ local-idx scope1.wireoffset)))
  ///
  (defthm moddb-address->wireidx-bound
    (let ((res (moddb-address->wireidx addr scope moddb)))
      (implies (and (moddb-ok moddb)
                    (modscope-okp scope moddb)
                    res)
               (< res (moddb-mod-totalwires
                       (modscope->modidx (modscope->top scope)) moddb))))
    :hints (("goal" :do-not-induct t)
            (and stable-under-simplificationp
                 '(:use ((:instance moddb-path->wireidx-bound
                          (path (address-root->path addr))
                          (modidx (modscope->modidx (modscope->top scope)))))
                   :in-theory (disable moddb-path->wireidx-bound))))
    :otf-flg t
    :rule-classes :linear))

(define moddb-address->wiredecl ((addr  address-p)
                                (scope (modscope-p scope))
                                (moddb moddb-ok))
  :guard (modscope-okp scope moddb)
  :parents (moddb)
  :short "Given a wire address, find the corresponding wire declaration."
  :returns (wire (iff (wire-p wire) wire))
  (b* (((address addr))
       ((modscope scope1)
        (if (eq addr.scope :root)
            (modscope->top scope)
          (modscope->nth addr.scope scope)))
       (wire (moddb-path->wiredecl addr.path scope1.modidx moddb)))
    wire)
  ///
  (defthm moddb-address->wiredecl-iff-wireidx
    (iff (moddb-address->wiredecl addr scope moddb)
         (moddb-address->wireidx addr scope moddb))
    :hints(("Goal" :in-theory (enable moddb-address->wireidx)))))



(define nat-list-max ((x nat-listp))
  ;; BOZO this is the same as max-nats from vl/util/sum-nats.lisp
  :returns (max natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (max (lnfix (car x))
         (nat-list-max (cdr x)))))

(deflist pathlist :elt-type path :true-listp t)

(define moddb-wireidx->paths ((wires nat-listp)
                              (modidx natp)
                              (moddb moddb-ok))
  :guard (and (< modidx (moddb->nmods moddb))
              (< (nat-list-max wires) (moddb-mod-totalwires modidx moddb)))
  :guard-hints (("goal" :expand ((nat-list-max wires))
                 :in-theory (disable MODDB-MOD-OK-IMPLIES-TOTALWIRES)))
  :returns (paths pathlist-p)
  (if (atom wires)
      nil
    (cons (moddb-wireidx->path (car wires) modidx moddb)
          (moddb-wireidx->paths (cdr wires) modidx moddb))))





(defsection modalist-idxaddr-okp
  (define svar-idxaddr-okp ((x svar-p) (bound natp))
    (and (svar-addr-p x)
         (b* ((addr (svar->address x))
              ((address addr)))
           (or (not addr.index)
               (< addr.index (lnfix bound)))))
    ///
    (deffixequiv svar-idxaddr-okp)

    (defthm svar-idxaddr-okp-of-greater
      (implies (and (svar-idxaddr-okp x bound1)
                    (<= (nfix bound1) (nfix bound2)))
               (svar-idxaddr-okp x bound2)))

    (defthm svar-addr-p-when-svar-idxadrr-okp
      (implies (svar-idxaddr-okp x bound)
               (svar-addr-p x))
      :hints(("Goal" :in-theory (enable svar-addr-p)))
      :rule-classes (:rewrite :forward-chaining)))

  (local (include-book "std/osets/element-list" :dir :system))
  (local (include-book "std/lists/sets" :dir :system))

  (std::deflist svarlist-idxaddr-okp (x bound)
    :guard (and (svarlist-p x)
                (natp bound))
    (svar-idxaddr-okp x bound)
    ///
    (deffixequiv svarlist-idxaddr-okp :args ((x svarlist) (bound natp)))
    (defthm svarlist-idxaddr-okp-of-greater
      (implies (and (svarlist-idxaddr-okp x bound1)
                    (<= (nfix bound1) (nfix bound2)))
               (svarlist-idxaddr-okp x bound2))))

  ;; (define svar-map-idxaddr-okp ((x svar-map-p) (bound natp))
  ;;   :guard (svar-map-addr-p x)
  ;;   :guard-hints (("goal" :in-theory (enable svar-map-addr-p)))
  ;;   :measure (len (svar-map-fix x))
  ;;   (b* ((x (svar-map-fix x))
  ;;        ((when (atom x)) t)
  ;;        ((cons lhs rhs) (car x)))
  ;;     (and (svar-idxaddr-okp lhs bound)
  ;;          (svar-idxaddr-okp rhs bound)
  ;;          (svar-map-idxaddr-okp (cdr x) bound)))
  ;;   ///
  ;;   (deffixequiv svar-map-idxaddr-okp)

  ;;   (defthm svar-map-idxaddr-okp-of-greater
  ;;     (implies (and (svar-map-idxaddr-okp x bound1)
  ;;                   (<= (nfix bound1) (nfix bound2)))
  ;;              (svar-map-idxaddr-okp x bound2))))

  ;; (defines svex-idxaddr-okp
  ;;   :verify-guards nil
  ;;   (define svex-idxaddr-okp ((x addr-svex-p) (bound natp))
  ;;     :measure (svex-count x)
  ;;     (svex-case x
  ;;       :var (svar-idxaddr-okp x.name bound)
  ;;       :quote t
  ;;       :call (svexlist-idxaddr-okp x.args bound)))
  ;;   (define svexlist-idxaddr-okp ((x addr-svexlist-p) (bound natp))
  ;;     :measure (svexlist-count x)
  ;;     (if (atom x)
  ;;         t
  ;;       (and (svex-idxaddr-okp (car x) bound)
  ;;            (svexlist-idxaddr-okp (cdr x) bound))))
  ;;   ///
  ;;   (deffixequiv-mutual svex-idxaddr-okp)
  ;;   (verify-guards svex-idxaddr-okp)

  ;;   (defthm-svex-idxaddr-okp-flag
  ;;     (defthm svex-idxaddr-okp-of-greater
  ;;       (implies (and (svex-idxaddr-okp x bound1)
  ;;                     (<= (nfix bound1) (nfix bound)))
  ;;                (svex-idxaddr-okp x bound))
  ;;       :flag svex-idxaddr-okp)
  ;;     (defthm svexlist-idxaddr-okp-of-greater
  ;;       (implies (and (svexlist-idxaddr-okp x bound1)
  ;;                     (<= (nfix bound1) (nfix bound)))
  ;;                (svexlist-idxaddr-okp x bound))
  ;;       :flag svexlist-idxaddr-okp)))

  ;; (define lhs-idxaddr-okp ((x lhs-p) (bound natp))
  ;;   :guard (lhs-addr-p x)
  ;;   :guard-hints(("Goal" :in-theory (enable lhs-addr-p lhatom-addr-p)))
  ;;   (b* (((when (atom x)) t)
  ;;        ((lhrange xf) (car x))
  ;;        (rest (lhs-idxaddr-okp (cdr x) bound)))
  ;;     (lhatom-case xf.atom
  ;;       :z rest
  ;;       :var (and (svar-idxaddr-okp xf.atom.name bound)
  ;;                 rest)))
  ;;   ///
  ;;   (deffixequiv lhs-idxaddr-okp)

  ;;   (defthm lhs-idxaddr-okp-of-greater
  ;;     (implies (and (lhs-idxaddr-okp x bound1)
  ;;                   (<= (nfix bound1) (nfix bound2)))
  ;;              (lhs-idxaddr-okp x bound2)))

  ;;   (defthm lhs-idxaddr-okp-of-lhs-rest
  ;;     (implies (lhs-idxaddr-okp x bound)
  ;;              (lhs-idxaddr-okp (lhs-rest x) bound))
  ;;     :hints(("Goal" :in-theory (enable lhs-rest)))))

  ;; (define assigns-idxaddr-okp ((x assigns-p) (bound natp))
  ;;   :guard (assigns-addr-p x)
  ;;   :guard-hints (("goal" :in-theory (enable assigns-addr-p)))
  ;;   :measure (len (assigns-fix x))
  ;;   (b* ((x (assigns-fix x))
  ;;        ((when (atom x)) t)
  ;;        ((cons lhs rhs) (car x)))
  ;;     (and (lhs-idxaddr-okp lhs bound)
  ;;          (svex-idxaddr-okp rhs bound)
  ;;          (assigns-idxaddr-okp (cdr x) bound)))
  ;;   ///
  ;;   (deffixequiv assigns-idxaddr-okp)

  ;;   (defthm assigns-idxaddr-okp-of-greater
  ;;     (implies (and (assigns-idxaddr-okp x bound1)
  ;;                   (<= (nfix bound1) (nfix bound2)))
  ;;              (assigns-idxaddr-okp x bound2))))

  ;; (define svex-alist-idxaddr-okp ((x svex-alist-p) (bound natp))
  ;;   :guard (svex-alist-addr-p x)
  ;;   :guard-hints (("goal" :in-theory (enable svex-alist-addr-p)))
  ;;   :measure (len (svex-alist-fix x))
  ;;   (b* ((x (svex-alist-fix x))
  ;;        ((when (atom x)) t)
  ;;        ((cons lhs rhs) (car x)))
  ;;     (and (svar-idxaddr-okp lhs bound)
  ;;          (svex-idxaddr-okp rhs bound)
  ;;          (svex-alist-idxaddr-okp (cdr x) bound)))
  ;;   ///
  ;;   (local (in-theory (enable svex-alist-fix)))
  ;;   (fty::deffixcong svex-alist-equiv svex-alist-equiv (append a b) a)
  ;;   (fty::deffixcong svex-alist-equiv svex-alist-equiv (append a b) b)
  ;;   (local (defthm svex-alist-idxaddr-okp-of-cons
  ;;            (equal (svex-alist-idxaddr-okp (cons a b) bound)
  ;;                   (and (svex-alist-idxaddr-okp b bound)
  ;;                        (or (atom a)
  ;;                            (and (svar-idxaddr-okp (car a) bound)
  ;;                                 (svex-idxaddr-okp (cdr a) bound)))))
  ;;            :hints (("goal" :expand ((svex-alist-idxaddr-okp (cons a b) bound))))))
  ;;   ;; (defthm svex-alist-fix-of-append
  ;;   ;;   (equal (svex-alist-fix (append x y))
  ;;   ;;          (append (svex-alist-fix x)
  ;;   ;;                  (svex-alist-fix y)))
  ;;   ;;   :hints(("Goal" :in-theory (enable svex-alist-fix))))

  ;;   (deffixequiv svex-alist-idxaddr-okp)

  ;;   (defthm svex-alist-idxaddr-okp-of-append
  ;;     (implies (and (svex-alist-idxaddr-okp x bound)
  ;;                   (svex-alist-idxaddr-okp y bound))
  ;;              (svex-alist-idxaddr-okp (append x y) bound))
  ;;     :hints(("Goal" :in-theory (enable append svex-alist-fix)
  ;;             :induct (append x y)
  ;;             :expand ((svex-alist-idxaddr-okp x bound)))))

  ;;   (defthm svex-alist-idxaddr-okp-of-assign->netassigns
  ;;     (implies (and (lhs-idxaddr-okp lhs bound)
  ;;                   (svex-idxaddr-okp rhs bound))
  ;;              (svex-alist-idxaddr-okp (assign->netassigns lhs rhs n) bound))
  ;;     :hints(("Goal" :in-theory (enable assign->netassigns
  ;;                                       lhs-idxaddr-okp svex-idxaddr-okp
  ;;                                       svexlist-idxaddr-okp
  ;;                                       svex-concat svex-rsh)
  ;;             :expand ((:free (f a) (svex-idxaddr-okp (svex-call f a) bound))))))

  ;;   (defthm svex-alist-idxaddr-okp-of-assigns->netassigns
  ;;     (implies (assigns-idxaddr-okp x bound)
  ;;              (svex-alist-idxaddr-okp (assigns->netassigns x) bound))
  ;;     :hints(("Goal" :in-theory (enable assigns->netassigns
  ;;                                       assigns-idxaddr-okp))))

  ;;   (defthm svex-alist-idxaddr-okp-of-hohs-shrink-alist
  ;;     (implies (and (svex-alist-idxaddr-okp x bound)
  ;;                   (svex-alist-idxaddr-okp y bound))
  ;;              (svex-alist-idxaddr-okp (hons-shrink-alist x y) bound))
  ;;     :hints(("Goal" :in-theory (enable hons-shrink-alist
  ;;                                       svex-alist-fix)
  ;;             :induct (hons-shrink-alist x y)
  ;;             :expand ((svex-alist-idxaddr-okp x bound)))))

  ;;   (defthm svex-idxaddr-okp-of-hons-assoc-equal-when-svex-alist-idxaddr-okp
  ;;     (implies (and (svex-alist-idxaddr-okp x bound)
  ;;                   (hons-assoc-equal k x))
  ;;              (svex-idxaddr-okp (cdr (hons-assoc-equal k x)) bound))
  ;;     :hints (("goal" :induct (hons-assoc-equal k x)
  ;;              :in-theory (enable svex-alist-fix)
  ;;              :expand ((svex-alist-idxaddr-okp x bound)))))

  ;;   (defthm svex-alist-idxaddr-okp-of-netassigns-collect-resolves
  ;;     (implies (and (svex-alist-idxaddr-okp x bound)
  ;;                   (svex-alist-idxaddr-okp acc bound))
  ;;              (svex-alist-idxaddr-okp (netassigns-collect-resolves x acc) bound))
  ;;     :hints(("Goal" :in-theory (enable netassigns-collect-resolves
  ;;                                       svexlist-idxaddr-okp)
  ;;             :induct (netassigns-collect-resolves x acc)
  ;;             :expand ((:free (f a) (svex-idxaddr-okp (svex-call f a) bound)))))))


  ;; (define lhspairs-idxaddr-okp ((x lhspairs-p) (bound natp))
  ;;   :measure (len (lhspairs-fix x))
  ;;   (b* ((x (lhspairs-fix x))
  ;;        ((when (atom x)) t)
  ;;        ((cons lhs rhs) (car x)))
  ;;     (and (lhs-idxaddr-okp lhs bound)
  ;;          (lhs-idxaddr-okp rhs bound)
  ;;          (lhspairs-idxaddr-okp (cdr x) bound)))
  ;;   ///
  ;;   (deffixequiv lhspairs-idxaddr-okp)

  ;;   (defthm lhspairs-idxaddr-okp-of-greater
  ;;     (implies (and (lhspairs-idxaddr-okp x bound1)
  ;;                   (<= (nfix bound1) (nfix bound2)))
  ;;              (lhspairs-idxaddr-okp x bound2))))

  ;; (define module-idxaddr-okp ((x module-p) (bound natp))
  ;;   (b* (((module x) x))
  ;;     (and (assigns-idxaddr-okp x.assigns bound)
  ;;          (svar-map-idxaddr-okp x.delays bound)
  ;;          (lhspairs-idxaddr-okp x.aliaspairs bound)
  ;;          ;; (wirelist-idxaddr-okp x.wires bound)p
  ;;          ))
  ;;   ///
  ;;   (deffixequiv module-idxaddr-okp)

  ;;   (defthm module-idxaddr-okp-of-greater
  ;;     (implies (and (module-idxaddr-okp x bound1)
  ;;                   (<= (nfix bound1) (nfix bound2)))
  ;;              (module-idxaddr-okp x bound2))))

  (define modalist-all-idxaddr-okp ((x modalist-p) (moddb moddb-ok))
    :measure (len (modalist-fix x))
    (b* ((x (modalist-fix x))
         ((when (atom x)) t)
         ((cons name mod) (car x))
         (modidx (moddb-modname-get-index name moddb))
         ((unless modidx)
          (and (svarlist-idxaddr-okp (module-vars mod) 0)
               (modalist-all-idxaddr-okp (cdr x) moddb)))
         ((stobj-get totalwires)
          ((elab-mod (moddb->modsi modidx moddb)))
          (elab-mod->totalwires elab-mod)))
      (and (svarlist-idxaddr-okp (module-vars (cdar x)) totalwires)
           (modalist-all-idxaddr-okp (cdr x) moddb)))
    ///
    (deffixequiv modalist-all-idxaddr-okp)))


(defsection modalist-named->indexed
  (define svar-named->indexed ((x svar-p) (modidx natp) (moddb moddb-ok))
    :guard (and (< modidx (moddb->nmods moddb))
                (svar-addr-p x))
    :returns (mv errmsg (xx svar-p))
    (b* ((addr (svar->address x))
         ((address addr))
         ((unless (eql 0 addr.scope))
          (mv nil (change-svar x :name (change-address addr :index nil)
                               :override-test nil :override-val nil)))
         (idx (moddb-path->wireidx addr.path modidx moddb))
         ((unless idx)
          (mv (msg "Did not find wire: ~x0 in module ~s1~%"
                   addr.path
                   (stobj-let ((elab-mod (moddb->modsi modidx moddb)))
                              (name)
                              (elab-mod->name elab-mod)
                              name))
              (change-svar x :name (change-address addr :index nil)
                           :override-test nil :override-val nil))))
      (mv nil (change-svar x  :name (change-address addr :index idx)
                           :override-test nil :override-val nil)))
    ///
    (deffixequiv svar-named->indexed)

    (defthm svar-named->indexed-idxaddr-ok
      (b* (((mv ?err newx) (svar-named->indexed x modidx moddb)))
        (implies (and (moddb-ok moddb)
                      (< (nfix modidx) (nfix (nth *moddb->nmods* moddb))))
                 (svar-idxaddr-okp newx
                                   (moddb-mod-totalwires
                                    modidx moddb))))
      :hints(("Goal" :in-theory (enable svar-idxaddr-okp svar-index svar->address
                                        svar-addr-p)))))


  (defines svex-named->indexed
    :verify-guards nil
    (define svex-named->indexed ((x svex-p) (modidx natp) (moddb moddb-ok))
      :guard (and (svarlist-addr-p (svex-vars x))
                  (< modidx (moddb->nmods moddb)))
      :measure (svex-count x)
      :returns (mv (errmsg) (xx svex-p))
      (svex-case x
        :var (b* (((mv err name) (svar-named->indexed x.name modidx moddb)))
               (mv err (svex-var name)))
        :quote (mv nil (svex-fix x))
        :call (b* (((mv err args) (svexlist-named->indexed x.args modidx moddb)))
                (mv err (svex-call x.fn args)))))
    (define svexlist-named->indexed ((x svexlist-p) (modidx natp) (moddb moddb-ok))
      :guard (and (svarlist-addr-p (svexlist-vars x))
                  (< modidx (moddb->nmods moddb)))
      :measure (svexlist-count x)
      :returns (mv errmsg (xx svexlist-p))
      (if (atom x)
          (mv nil nil)
        (b* (((mv err1 first) (svex-named->indexed (car x) modidx moddb))
             ((mv err2 rest) (svexlist-named->indexed (cdr x) modidx moddb)))
          (mv (or err1 err2) (cons first rest)))))
    ///
    (deffixequiv-mutual svex-named->indexed)
    (verify-guards svex-named->indexed)

    (defthm-svex-named->indexed-flag
      (defthm svex-named->indexed-idxaddr-ok
        (b* (((mv err ans) (svex-named->indexed x modidx moddb)))
          (implies (and (moddb-ok moddb)
                        (< (nfix modidx) (nfix (nth *moddb->nmods* moddb)))
                        (not err))
                   (svarlist-idxaddr-okp (svex-vars ans)
                                         (moddb-mod-totalwires
                                          modidx moddb))))
        ;; :hints ('(:in-theory (enable svex-idxaddr-okp)))
        :flag svex-named->indexed)
      (defthm svexlist-named->indexed-idxaddr-ok
        (b* (((mv err ans) (svexlist-named->indexed x modidx moddb)))
          (implies (and (moddb-ok moddb)
                        (< (nfix modidx) (nfix (nth *moddb->nmods* moddb)))
                        (not err))
                   (svarlist-idxaddr-okp (svexlist-vars
                                          ans)
                                         (moddb-mod-totalwires
                                          modidx moddb))))
        ;; :hints ('(:in-theory (enable svexlist-)))
        :flag svexlist-named->indexed))

    (define svex-named->indexed-memo-ok ((x svex-p) (modidx natp) (moddb moddb-ok))
      :guard (and (svarlist-addr-p (svex-vars x))
                  (< modidx (moddb->nmods moddb)))
      :ignore-ok t
      :inline t
      (eq (svex-kind x) :call))

    ;; BOZO memoizing this likely makes all moddb operations slow
    (memoize 'svex-named->indexed :condition-fn 'svex-named->indexed-memo-ok$inline))

  (define lhs-named->indexed ((x lhs-p) (modidx natp) (moddb moddb-ok))
    :guard (and (svarlist-addr-p (lhs-vars x))
                (< modidx (moddb->nmods moddb)))
    :guard-hints (("goal" :in-theory (enable lhatom-vars)))
    :returns (mv errmsg (xx lhs-p))
    (b* (((when (atom x)) (mv nil nil))
         ((lhrange xf) (car x))
         ((mv err2 rest) (lhs-named->indexed (cdr x) modidx moddb)))
      (lhatom-case xf.atom
        :z (mv err2 (cons (lhrange-fix (car x)) rest))
        :var (b* (((mv err1 name) (svar-named->indexed xf.atom.name modidx moddb)))
               (mv (or err1 err2)
                   (cons (lhrange xf.w (lhatom-var name xf.atom.rsh))
                         rest)))))
    ///
    (deffixequiv lhs-named->indexed)

    (defthm lhs-idxaddr-okp-of-lhs-named->indexed
      (b* (((mv err ans) (lhs-named->indexed x modidx moddb)))
        (implies (and (moddb-ok moddb)
                      (< (nfix modidx) (nfix (nth *moddb->nmods* moddb)))
                      (not err))
                 (svarlist-idxaddr-okp (lhs-vars
                                        ans)
                                       (moddb-mod-totalwires
                                        modidx moddb))))
      :hints(("Goal" :in-theory (enable lhatom-vars)))))

  (define assigns-named->indexed ((x assigns-p) (modidx natp) (moddb moddb-ok))
    :guard (and (svarlist-addr-p (assigns-vars x))
                (< modidx (moddb->nmods moddb)))
    :measure (len (assigns-fix x))
    :returns (mv errmsg (xx assigns-p))
    :prepwork ((local (in-theory (enable assigns-vars))))
    (b* ((x (assigns-fix x))
         ((when (atom x)) (mv nil nil))
         ((cons lhs (driver rhs)) (car x))
         ((mv err1 lhs) (lhs-named->indexed lhs modidx moddb))
         ((mv err2 val) (svex-named->indexed rhs.value modidx moddb))
         ((mv err3 rest) (assigns-named->indexed (cdr x) modidx moddb)))
      (mv (or err1 err2 err3)
          (cons (cons lhs (change-driver rhs :value val))
                rest)))
    ///
    (deffixequiv assigns-named->indexed)

    (defthm assigns-idxaddr-okp-of-assigns-named->indexed
      (b* (((mv err ans) (assigns-named->indexed x modidx moddb)))
        (implies (and (moddb-ok moddb)
                      (< (nfix modidx) (nfix (nth *moddb->nmods* moddb)))
                      (not err))
                 (svarlist-idxaddr-okp (assigns-vars
                                        ans)
                                       (moddb-mod-totalwires
                                        modidx moddb))))))

  (define constraintlist-named->indexed ((x constraintlist-p)
                                         (modidx natp)
                                         (moddb moddb-ok))
    :guard (and (svarlist-addr-p (constraintlist-vars x))
                (< modidx (moddb->nmods moddb)))
    :returns (mv errmsg (xx constraintlist-p))
    :prepwork ((local (in-theory (enable constraintlist-vars))))
    (b* (((when (atom x)) (mv nil nil))
         ((constraint x1) (car x))
         ((mv err1 new-cond) (svex-named->indexed x1.cond modidx moddb))
         ((mv err2 rest)
          (constraintlist-named->indexed (cdr x) modidx moddb)))
      (mv (or err1 err2)
          (cons (change-constraint x1 :cond new-cond) rest)))
    ///
    (defthm constraintlist-idxaddr-okp-of-constraintlist-named->indexed
      (b* (((mv err ans) (constraintlist-named->indexed x modidx moddb)))
        (implies (and (moddb-ok moddb)
                      (< (nfix modidx) (nfix (nth *moddb->nmods* moddb)))
                      (not err))
                 (svarlist-idxaddr-okp (constraintlist-vars ans)
                                       (moddb-mod-totalwires
                                        modidx moddb))))))

  (define svar-map-named->indexed ((x svar-map-p) (modidx natp) (moddb moddb-ok))
    :guard (and (svarlist-addr-p (svar-map-vars x))
                (< modidx (moddb->nmods moddb)))
    :measure (len (svar-map-fix x))
    :returns (mv errmsg (xx svar-map-p))
    :prepwork ((local (in-theory (enable svar-map-vars))))
    (b* ((x (svar-map-fix x))
         ((when (atom x)) (mv nil nil))
         ((cons lhs rhs) (car x))
         ((mv err1 lhs) (svar-named->indexed lhs modidx moddb))
         ((mv err2 rhs) (svar-named->indexed rhs modidx moddb))
         ((mv err3 rest) (svar-map-named->indexed (cdr x) modidx moddb)))
      (mv (or err1 err2 err3)
          (cons (cons lhs rhs)
                rest)))
    ///
    (deffixequiv svar-map-named->indexed)

    (defthm svar-map-idxaddr-okp-of-svar-map-named->indexed
      (b* (((mv err ans) (svar-map-named->indexed x modidx moddb)))
        (implies (and (moddb-ok moddb)
                      (< (nfix modidx) (nfix (nth *moddb->nmods* moddb)))
                      (not err))
                 (svarlist-idxaddr-okp (svar-map-vars
                                        ans)
                                       (moddb-mod-totalwires
                                        modidx moddb))))))

  (define lhspairs-named->indexed-aux-nrev ((x lhspairs-p) (modidx natp) (moddb moddb-ok) (acl2::nrev) (err))
    :guard (and (svarlist-addr-p (lhspairs-vars x))
                (< modidx (moddb->nmods moddb)))
    :measure (len (lhspairs-fix x))
    :prepwork ((local (in-theory (enable lhspairs-vars))))
    (b* ((x (lhspairs-fix x))
         ((when (atom x))
          (b* ((acl2::nrev (acl2::nrev-fix acl2::nrev)))
            (mv err acl2::nrev)))
         ((cons lhs rhs) (car x))
         ((mv err1 lhs) (lhs-named->indexed lhs modidx moddb))
         ((mv err2 rhs) (lhs-named->indexed rhs modidx moddb))
         (err (or err err1 err2))
         (acl2::nrev (acl2::nrev-push (cons lhs rhs) acl2::nrev)))
      (lhspairs-named->indexed-aux-nrev (cdr x) modidx moddb acl2::nrev err)))

  (define lhspairs-named->indexed ((x lhspairs-p) (modidx natp) (moddb moddb-ok))
    :guard (and (svarlist-addr-p (lhspairs-vars x))
                (< modidx (moddb->nmods moddb)))
    :verify-guards nil
    :measure (len (lhspairs-fix x))
    :returns (mv errmsg (xx lhspairs-p))
    :prepwork ((local (in-theory (enable lhspairs-vars))))
    (mbe :logic
         (b* ((x (lhspairs-fix x))
              ((when (atom x)) (mv nil nil))
              ((cons lhs rhs) (car x))
              ((mv err1 lhs) (lhs-named->indexed lhs modidx moddb))
              ((mv err2 rhs) (lhs-named->indexed rhs modidx moddb))
              ((mv err3 rest) (lhspairs-named->indexed (cdr x) modidx moddb)))
           (mv (or err1 err2 err3)
               (cons (cons lhs rhs)
                     rest)))
         :exec (if (atom x)
                   (mv nil nil)
                 (with-local-stobj acl2::nrev
                   (mv-let (err ans acl2::nrev)
                     (b* (((mv err acl2::nrev) (lhspairs-named->indexed-aux-nrev
                                                x modidx moddb acl2::nrev nil))
                          ((mv ans acl2::nrev) (acl2::nrev-finish acl2::nrev)))
                       (mv err ans acl2::nrev))
                     (mv err ans)))))

    ///
    (local (defthm lhspairs-named->index-aux-nrev-elim
             (b* (((mv nrev-err nrev-ans)
                   (lhspairs-named->indexed-aux-nrev x modidx moddb acl2::nrev err))
                  ((mv regular-err regular-ans)
                   (lhspairs-named->indexed x modidx moddb)))
               (and (equal nrev-err (or err regular-err))
                    (equal nrev-ans (append acl2::nrev regular-ans))))
             :hints(("Goal" :in-theory (enable lhspairs-named->indexed-aux-nrev)))))

    (defret lhspairs-named->indexed-true-listp
      (true-listp xx)
      :rule-classes :type-prescription)

    (verify-guards lhspairs-named->indexed)

    (deffixequiv lhspairs-named->indexed)

    (defthm lhspairs-idxaddr-okp-of-lhspairs-named->indexed
      (b* (((mv err ans) (lhspairs-named->indexed x modidx moddb)))
        (implies (and (moddb-ok moddb)
                      (< (nfix modidx) (nfix (nth *moddb->nmods* moddb)))
                      (not err))
                 (svarlist-idxaddr-okp (lhspairs-vars
                                        ans)
                                       (moddb-mod-totalwires
                                        modidx moddb))))))

  (local (in-theory (disable acl2::member-equal-append
                             sv::svarlist-addr-p-by-badguy)))

  (define module-named->indexed ((x module-p) (modidx natp) (moddb moddb-ok))
    :guard (and (svarlist-addr-p (module-vars x))
                (< modidx (moddb->nmods moddb)))
    :returns (mv errmsg (xx module-p))
    :prepwork ((local (in-theory (enable module-vars))))
    (b* (((module x) x)
         ((mv err1 assigns) (assigns-named->indexed x.assigns modidx moddb))
         ((mv err2 constraints)  (constraintlist-named->indexed x.constraints modidx moddb))
         ((mv err3 fixups) (assigns-named->indexed x.fixups modidx moddb))
         ((mv err4 aliaspairs) (lhspairs-named->indexed x.aliaspairs modidx moddb))
         ;; ((mv err3 wires)   (wirelist-named->indexed x.wires modidx moddb))
         )
      (mv (or err1 err2 err3 err4)
          (change-module x
                         :assigns assigns
                         :constraints constraints
                         :fixups fixups
                         ;; :delays delays
                         :aliaspairs aliaspairs)))
    ///
    (deffixequiv module-named->indexed)

    (defthm module-idxaddr-okp-of-module-named->indexed
      (b* (((mv err mod) (module-named->indexed x modidx moddb)))
        (implies (and (moddb-ok moddb)
                      (< (nfix modidx) (nfix (nth *moddb->nmods* moddb)))
                      (not err))
                 (svarlist-idxaddr-okp
                  (module-vars mod)
                  (moddb-mod-totalwires
                   modidx moddb))))))

  (define modalist-named->indexed ((x modalist-p) (moddb moddb-ok)
                                   &key (quiet 'nil))
    :guard (svarlist-addr-p (modalist-vars x))
    :measure (len (modalist-fix x))
    :returns (mv errmsg (xx modalist-p))
    :prepwork ((local (in-theory (enable modalist-vars))))
    (b* ((x (modalist-fix x))
         ((when (atom x)) (mv nil nil))
         ((cons name mod) (car x))
         (modidx (moddb-modname-get-index name moddb))
         ((unless modidx)
          (and (not quiet) (cw "Warning! Module ~x0 not found in moddb.~%" name))
          (modalist-named->indexed (cdr x) moddb :quiet quiet))
         ((mv err1 first) (module-named->indexed mod modidx moddb))
         (- (clear-memoize-table 'svex-named->indexed))
         ((mv err2 rest) (modalist-named->indexed (cdr x) moddb :quiet quiet)))
      (mv (or err1 err2) (cons (cons name first) rest)))
    ///
    (deffixequiv modalist-named->indexed)

    (defthm modalist-all-idxaddr-okp-of-modalist-named->indexed
      (b* (((mv err res) (modalist-named->indexed x moddb :quiet quiet)))
        (implies (and (moddb-ok moddb) (not err))
                 (modalist-all-idxaddr-okp res moddb)))
      :hints(("Goal" :in-theory (enable modalist-all-idxaddr-okp))))))

(define modscope-local-bound ((scope modscope-p) (moddb moddb-ok))
  :guard (modscope-okp scope moddb)
  (moddb-mod-totalwires (modscope->modidx scope) moddb))

(define modscope-top-bound ((scope modscope-p) (moddb moddb-ok))
  :guard (modscope-okp scope moddb)
  :guard-hints (("goal" :use ((:instance modscope-okp-implies-top-modidx-in-bounds
                               (x (modscope->top scope))))
                 :in-theory (disable modscope-okp-implies-top-modidx-in-bounds)))
  (moddb-mod-totalwires (modscope->modidx (modscope->top scope)) moddb))

;; (encapsulate nil
;;   (local (include-book "std/lists/list-fix" :dir :system))
;;   (std::deflist svarlist (x) (svar-p x) :true-listp t :elementp-of-nil nil))

(defsection svex->absindexed
  (define svar->absindexed ((x svar-p)
                            (scope modscope-p)
                            (moddb moddb-ok))
    :guard (and (modscope-okp scope moddb)
                (svar-idxaddr-okp x (modscope-local-bound scope moddb)))
    :returns (mv ok
                 (xx svar-p))
    (b* ((i (svar->address x))
         ((address i))
         (index (if i.index
                    (+ (modscope->wireoffset scope) i.index)
                  (moddb-address->wireidx i scope moddb)))
         ((unless index) (mv nil (svar-fix x))))
      (mv t (svar-set-index x index)))
    ///
    (deffixequiv svar->absindexed)

    (defthm svar-boundedp-of-svar->absindexed
      (b* (((mv ok var) (svar->absindexed x scope moddb)))
        (implies (and (svar-idxaddr-okp x (modscope-local-bound scope moddb))
                      (modscope-okp scope moddb)
                      (moddb-ok moddb)
                      ok)
                 (svar-boundedp var (modscope-top-bound scope moddb))))
      :hints(("Goal" :in-theory (enable svar-boundedp svar-idxaddr-okp ;svar-index
                                        modscope->wireoffset
                                        modscope-local-bound modscope-top-bound)))))

  (defines svex->absindexed
    :verify-guards nil
    (define svex->absindexed ((x svex-p) (scope modscope-p) (moddb moddb-ok))
      :guard (and (modscope-okp scope moddb)
                  (svarlist-idxaddr-okp
                   (svex-vars x) (modscope-local-bound scope moddb)))
      :measure (svex-count x)
      :returns (mv (fails svarlist-p)
                   (xx svex-p))
      (svex-case x
        :var (b* (((mv ok newvar) (svar->absindexed x.name scope moddb))
                  ((unless ok) (mv (list x.name) (svex-x))))
               (mv nil (svex-var newvar)))
        :quote (mv nil (svex-fix x))
        :call (b* (((mv fails args) (svexlist->absindexed x.args scope moddb)))
                (mv fails (svex-call x.fn args)))))
    (define svexlist->absindexed ((x svexlist-p) (scope modscope-p) (moddb moddb-ok))
      :guard (and (modscope-okp scope moddb)
                  (svarlist-idxaddr-okp
                   (svexlist-vars x) (modscope-local-bound scope moddb)))
      :measure (svexlist-count x)
      :returns (mv (fails svarlist-p)
                   (xx svexlist-p))
      (if (atom x)
          (mv nil nil)
        (b* (((mv fails1 arg1) (svex->absindexed (car x) scope moddb))
             ((mv fails2 args2) (svexlist->absindexed (cdr x) scope moddb)))
          (mv (append-without-guard fails1 fails2) (cons arg1 args2)))))
    ///
    (deffixequiv-mutual svex->absindexed)
    (verify-guards svex->absindexed)


    (defthm-svex->absindexed-flag
      (defthm svex-boundedp-of-svex->absindexed
        (b* (((mv ?fails res) (svex->absindexed x scope moddb)))
          (implies (and (svarlist-idxaddr-okp (svex-vars x) (modscope-local-bound scope moddb))
                        (modscope-okp scope moddb)
                        (moddb-ok moddb))
                   (svarlist-boundedp (svex-vars res) (modscope-top-bound scope moddb))))
        :flag svex->absindexed)
      (defthm svexlist-boundedp-of-svexlist->absindexed
        (b* (((mv ?fails res) (svexlist->absindexed x scope moddb)))
          (implies (and (svarlist-idxaddr-okp (svexlist-vars x) (modscope-local-bound scope moddb))
                        (modscope-okp scope moddb)
                        (moddb-ok moddb))
                   (svarlist-boundedp (svexlist-vars res) (modscope-top-bound scope moddb))))
        :flag svexlist->absindexed))

    (define svex->absindexed-memo-ok ((x svex-p) (scope modscope-p) (moddb moddb-ok))
      :guard (and (modscope-okp scope moddb)
                  (svarlist-idxaddr-okp
                   (svex-vars x) (modscope-local-bound scope moddb)))
      :ignore-ok t
      :inline t
      (eq (svex-kind x) :call))

    ;; BOZO memoizing this likely makes all moddb operations slow
    (memoize 'svex->absindexed :condition-fn 'svex->absindexed-memo-ok$inline))

  (define lhs->absindexed ((x lhs-p) (scope modscope-p) (moddb moddb-ok))
    :guard (and (modscope-okp scope moddb)
                (svarlist-idxaddr-okp (lhs-vars x) (modscope-local-bound scope moddb)))
    :guard-hints (("goal" :in-theory (enable lhatom-vars)))
    :returns (mv (fails svarlist-p)
                 (xx lhs-p))
    (b* (((when (atom x)) (mv nil nil))
         ((lhrange xf) (car x))
         ((mv rest-fails rest) (lhs->absindexed (cdr x) scope moddb)))
      (lhatom-case xf.atom
        :z (mv rest-fails (cons (lhrange-fix (car x)) rest))
        :var (b* (((mv ok var) (svar->absindexed xf.atom.name scope moddb)))
               (if ok
                   (mv rest-fails
                       (cons (lhrange xf.w (lhatom-var var xf.atom.rsh))
                             rest))
                 (mv (cons xf.atom.name rest-fails)
                     (cons (make-lhrange :w xf.w :atom (lhatom-z)) rest))))))
    ///
    (deffixequiv lhs->absindexed)

    (defthm lhs-boundedp-of-lhs->absindexed
      (b* (((mv ?fails res) (lhs->absindexed x scope moddb)))
        (implies (and (svarlist-idxaddr-okp (lhs-vars x) (modscope-local-bound scope moddb))
                      (modscope-okp scope moddb)
                      (moddb-ok moddb))
                 (svarlist-boundedp (lhs-vars res) (modscope-top-bound scope moddb))))
      :hints(("Goal" :in-theory (enable lhatom-vars)))))

  (define assigns->absindexed ((x assigns-p) (scope modscope-p) (moddb moddb-ok))
    :guard (and (modscope-okp scope moddb)
                (svarlist-idxaddr-okp (assigns-vars x) (modscope-local-bound scope moddb)))
    :measure (len (assigns-fix x))
    :returns (mv (fails svarlist-p)
                 (xx assigns-p))
    :prepwork ((local (in-theory (enable assigns-vars))))
    (b* ((x (assigns-fix x))
         ((when (atom x)) (mv nil nil))
         ((cons lhs (driver rhs)) (car x))
         ((mv fails1 lhs) (lhs->absindexed lhs scope moddb))
         ((mv fails2 val) (svex->absindexed rhs.value scope moddb))
         ((mv fails3 rest) (assigns->absindexed (cdr x) scope moddb)))
      (mv (append-without-guard fails1 fails2 fails3)
          (cons (cons lhs (change-driver rhs :value val)) rest)))
    ///
    (deffixequiv assigns->absindexed)

    (defthm assigns-boundedp-of-assigns->absindexed
      (b* (((mv ?fails res) (assigns->absindexed x scope moddb)))
        (implies (and (svarlist-idxaddr-okp (assigns-vars x) (modscope-local-bound scope moddb))
                      (modscope-okp scope moddb)
                      (moddb-ok moddb))
                 (svarlist-boundedp (assigns-vars res) (modscope-top-bound scope moddb))))))

  (define svex-alist->absindexed ((x svex-alist-p)
                                     (scope modscope-p)
                                     (moddb moddb-ok))
    :guard (and (modscope-okp scope moddb)
                (svarlist-idxaddr-okp (svex-alist-vars x) (modscope-local-bound scope moddb))
                (svarlist-idxaddr-okp (svex-alist-keys x) (modscope-local-bound scope moddb)))
    ;; :measure (len (svex-alist-fix x))
    :returns (mv (fails svarlist-p) (xx svex-alist-p))
    :prepwork ((local (in-theory (enable svex-alist-vars svex-alist-keys svex-alist-fix))))
    (b* (((when (atom x)) (mv nil nil))
         ((unless (mbt (and (consp (car x))
                            (svar-p (caar x)))))
          (svex-alist->absindexed (cdr x) scope moddb))
         ((cons key val) (car x))
         ((mv ok new-key) (svar->absindexed key scope moddb))
         ((unless ok)
          (b* (((mv fails1 rest) (svex-alist->absindexed (cdr x) scope moddb)))
            (mv (cons (svar-fix key) fails1) rest)))
         ((mv fails2 new-val) (svex->absindexed val scope moddb))
         ((mv fails3 rest)
          (svex-alist->absindexed (cdr x) scope moddb)))
      (mv (append-without-guard fails2 fails3)
          (cons (cons new-key new-val) rest)))
    ///
    (defthm svex-alist-boundedp-of-svex-alist->absindexed
      (b* (((mv ?fails res) (svex-alist->absindexed x scope moddb)))
        (implies (and (svarlist-idxaddr-okp (svex-alist-vars x) (modscope-local-bound scope moddb))
                      (svarlist-idxaddr-okp (svex-alist-keys x) (modscope-local-bound scope moddb))
                      (modscope-okp scope moddb)
                      (moddb-ok moddb))
                 (and (svarlist-boundedp (svex-alist-vars res) (modscope-top-bound scope moddb))
                      (svarlist-boundedp (svex-alist-keys res) (modscope-top-bound scope moddb)))))
      :hints (("goal" :induct (svex-alist->absindexed x scope moddb)
               :expand ((svex-alist-fix x))))))


  (define constraintlist->absindexed ((x constraintlist-p)
                                     (scope modscope-p)
                                     (moddb moddb-ok))
    :guard (and (modscope-okp scope moddb)
                (svarlist-idxaddr-okp (constraintlist-vars x) (modscope-local-bound scope moddb)))
    :returns (mv (fails svarlist-p) (xx constraintlist-p))
    :prepwork ((local (in-theory (enable constraintlist-vars))))
    (b* (((when (atom x)) (mv nil nil))
         ((constraint x1) (car x))
         ((mv fails1 new-cond) (svex->absindexed x1.cond scope moddb))
         ((mv fails2 rest)
          (constraintlist->absindexed (cdr x) scope moddb)))
      (mv (append-without-guard fails1 fails2)
          (cons (change-constraint x1 :cond new-cond) rest)))
    ///
    (defthm constraintlist-boundedp-of-constraintlist->absindexed
      (b* (((mv ?fails res) (constraintlist->absindexed x scope moddb)))
        (implies (and (svarlist-idxaddr-okp (constraintlist-vars x) (modscope-local-bound scope moddb))
                      (modscope-okp scope moddb)
                      (moddb-ok moddb))
                 (svarlist-boundedp (constraintlist-vars res) (modscope-top-bound scope moddb))))))

  (define svar-map->absindexed ((x svar-map-p) (scope modscope-p) (moddb moddb-ok))
    :guard (and (modscope-okp scope moddb)
                (svarlist-idxaddr-okp (svar-map-vars x) (modscope-local-bound scope moddb)))
    :prepwork ((local (in-theory (enable svar-map-vars))))
    :measure (len (svar-map-fix x))
    :returns (mv (fails svarlist-p)
                 (xx svar-map-p))
    (b* ((x (svar-map-fix x))
         ((when (atom x)) (mv nil nil))
         ((cons lhs rhs) (car x))
         ((mv ok1 lhs) (svar->absindexed lhs scope moddb))
         ((mv ok2 rhs) (svar->absindexed rhs scope moddb))
         ((mv fails3 rest) (svar-map->absindexed (cdr x) scope moddb)))
      (mv (append-without-guard
           (and (not ok1) (list lhs))
           (and (not ok2) (list rhs)) fails3)
          (if (and ok1 ok2)
              (cons (cons lhs rhs) rest)
            rest)))
    ///
    (deffixequiv svar-map->absindexed)

    (defthm svar-map-boundedp-of-svar-map->absindexed
      (b* (((mv ?fails res) (svar-map->absindexed x scope moddb)))
        (implies (and (svarlist-idxaddr-okp (svar-map-vars x) (modscope-local-bound scope moddb))
                      (modscope-okp scope moddb)
                      (moddb-ok moddb))
                 (svarlist-boundedp (svar-map-vars res) (modscope-top-bound scope moddb))))))

  (acl2::defstobj-clone nrev acl2::nrev :suffix "0")
  (acl2::defstobj-clone nrev1 acl2::nrev :suffix "1")

  (define lhspairs->absindexed-nrev ((x lhspairs-p) (scope modscope-p) (moddb moddb-ok)
                                     (nrev)   ;; fails
                                     (nrev1)) ;; ans
    :guard (and (modscope-okp scope moddb)
                (svarlist-idxaddr-okp (lhspairs-vars x) (modscope-local-bound scope moddb)))
    :prepwork ((local (in-theory (enable lhspairs-vars))))
    :measure (len (lhspairs-fix x))
    (b* ((x (lhspairs-fix x))
         ((when (atom x))
          (b* ((nrev (acl2::nrev-fix nrev))
               (nrev1 (acl2::nrev-fix nrev1)))
            (mv nrev nrev1)))
         ((cons lhs rhs) (car x))
         ((mv fails1 lhs) (lhs->absindexed lhs scope moddb))
         ((mv fails2 rhs) (lhs->absindexed rhs scope moddb))
         (nrev (acl2::nrev-append fails1 nrev))
         (nrev (acl2::nrev-append fails2 nrev))
         (nrev1 (acl2::nrev-push (cons lhs rhs) nrev1)))
      (lhspairs->absindexed-nrev (cdr x) scope moddb nrev nrev1)))


  (define lhspairs->absindexed ((x lhspairs-p) (scope modscope-p) (moddb moddb-ok))
    :guard (and (modscope-okp scope moddb)
                (svarlist-idxaddr-okp (lhspairs-vars x) (modscope-local-bound scope moddb)))
    :prepwork ((local (in-theory (enable lhspairs-vars))))
    :measure (len (lhspairs-fix x))
    :returns (mv (fails svarlist-p)
                 (xx lhspairs-p))
    :verify-guards nil
    (mbe :logic (b* ((x (lhspairs-fix x))
                     ((when (atom x)) (mv nil nil))
                     ((cons lhs rhs) (car x))
                     ((mv fails1 lhs) (lhs->absindexed lhs scope moddb))
                     ((mv fails2 rhs) (lhs->absindexed rhs scope moddb))
                     ((mv fails3 rest) (lhspairs->absindexed (cdr x) scope moddb)))
                  (mv (append-without-guard fails1 fails2 fails3)
                      (cons (cons lhs rhs) rest)))
         :exec (if (atom x)
                   (mv nil nil)
                 (b* (((acl2::local-stobjs nrev nrev1)
                       (mv fails ans nrev nrev1))
                      ((mv nrev nrev1) (lhspairs->absindexed-nrev x scope moddb nrev nrev1))
                      ((mv fails nrev) (acl2::nrev-finish nrev))
                      ((mv ans nrev1) (acl2::nrev-finish nrev1)))
                   (mv fails ans nrev nrev1))))
    ///
    (local (defthm lhspairs->absindexed-nrev-elim
             (b* (((mv nrev-fails nrev-ans)
                   (lhspairs->absindexed-nrev x modidx moddb nrev nrev1))
                  ((mv regular-fails regular-ans)
                   (lhspairs->absindexed x modidx moddb)))
               (and (equal nrev-fails (append nrev regular-fails))
                    (equal nrev-ans (append nrev1 regular-ans))))
             :hints(("Goal" :in-theory (enable lhspairs->absindexed-nrev)))))

    (defret lhspairs->absindexed-true-listp
      (true-listp xx)
      :rule-classes :type-prescription)

    (verify-guards lhspairs->absindexed)
    (deffixequiv lhspairs->absindexed)

    (defthm lhspairs-boundedp-of-lhspairs->absindexed
      (b* (((mv ?fails res) (lhspairs->absindexed x scope moddb)))
        (implies (and (svarlist-idxaddr-okp (lhspairs-vars x) (modscope-local-bound scope moddb))
                      (modscope-okp scope moddb)
                      (moddb-ok moddb))
                 (svarlist-boundedp (lhspairs-vars res) (modscope-top-bound scope moddb)))))))

;; (define wirelist->absindexed ((x wirelist-p) (scope modscope-p) (moddb moddb-ok))
;;   :measure (len (wirelist-fix x))
;;   :returns (xx wirelist-p)
;;   (b* (((when (atom x)) nil)
;;        (xf (car x))
;;        ((wire xf) xf))
;;     (cons (change-wire xf :expr (lhs->absindexed xf.expr offset))
;;           (wirelist->absindexed (cdr x) offset)))
;;   ///
;;   (deffixequiv wirelist->absindexed)

;;   (defthm wirelist-boundedp-of-wirelist->absindexed
;;     (implies (and (svarlist-boundedp (wirelist-vars x) (- (nfix bound) (nfix offset)))
;;                   (<= (nfix offset) (nfix bound)))
;;              (svarlist-boundedp (wirelist-vars (wirelist->absindexed x offset)) bound))
;;     :hints(("Goal" :in-theory (enable wirelist-boundedp)))))

;; (define wirelist-initialize-aliases ((x wirelist-p) (offset natp) lhsarr)
;;   :verify-guards nil
;;   :guard (<= (+ offset (len x)) (lhss-length lhsarr))
;;   :prepwork ((local (in-theory (enable svar-p))))
;;   :returns (lhsarr1 lhslist-p)
;;   (b* (((when (atom x)) (lhsarr-fix lhsarr))
;;        ((wire xf) (car x))
;;        (offset (lnfix offset))
;;        (lhs (if (eql 0 xf.lsb)
;;                 (list (lhrange xf.width (lhatom-var `(:var ,offset) 0)))
;;               (list (lhrange xf.lsb (lhatom-z))
;;                     (lhrange xf.width (lhatom-var `(:var ,offset) xf.lsb)))))
;;        (lhsarr (set-lhs offset lhs lhsarr)))
;;     (wirelist-initialize-aliases (cdr x) (+ 1 offset) lhsarr))
;;   ///
;;   (verify-guards wirelist-initialize-aliases)
;;   (deffixequiv wirelist-initialize-aliases))

(define elab-mod-initialize-aliases ((idx natp) elab-mod (offset natp) lhsarr)
  :verify-guards nil
  :guard (and (<= (+ offset (elab-mod-nwires elab-mod)) (lhss-length lhsarr))
              (<= idx (elab-mod-nwires elab-mod)))
  :measure (nfix (- (elab-mod-nwires elab-mod) (nfix idx)))
  :returns (lhsarr1 lhslist-p)
  ;; ==Backward Range Convention==
  (b* (((when (mbe :logic (or (zp (- (elab-mod-nwires elab-mod) (nfix idx)))
                              (zp (- (lhss-length lhsarr) (+ (nfix offset) (nfix idx)))))
                   :exec (eql (elab-mod-nwires elab-mod) idx)))
        (lhsarr-fix lhsarr))
       ((wire xf) (elab-mod-wiretablei idx elab-mod))
       (widx (+ (lnfix idx) (lnfix offset)))
       (lhs (list (lhrange xf.width (lhatom-var
                                     (make-svar :name widx)
                                     ;; (address->svar
                                     ;;  (make-address :path (make-path-wire :name xf.name)
                                     ;;                :index widx))
                                     0))))
       (lhsarr (set-lhs widx lhs lhsarr)))
    ;; (cw "set ~x0 to ~x1~%" widx lhs)
    (elab-mod-initialize-aliases (1+ (lnfix idx)) elab-mod offset lhsarr))
  ///
  (verify-guards elab-mod-initialize-aliases)
  (deffixequiv elab-mod-initialize-aliases)

  (defthm len-of-elab-mod-initialize-aliases
    (equal (len (elab-mod-initialize-aliases idx elab-mod offset lhsarR))
           (len lhsarr)))

  (defthmd lookup-in-elab-mod-initialize-aliases
    (equal (nth n (elab-mod-initialize-aliases idx elab-mod offset lhsarr))
           (if (and (<= (+ (nfix idx) (nfix offset)) (nfix n))
                    (< (nfix n) (+ (nfix offset) (elab-mod-nwires elab-mod)))
                    (< (nfix n) (len lhsarr)))
               (b* (((wire xf) (elab-mod-wiretablei (- (nfix n) (nfix offset)) elab-mod)))
                 (list (lhrange xf.width (lhatom-var
                                          (make-svar :name (nfix n))
                                          ;; (address->svar
                                          ;;  (make-address :path (make-path-wire :name xf.name)
                                          ;;                :index (nfix n)))
                                          0))))
             (lhs-fix (nth n lhsarr))))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:cases ((nat-equiv idx (- (nfix n) (nfix offset))))
                   :in-theory (disable nat-equiv)))
            (and stable-under-simplificationp
                 '(:in-theory (enable nat-equiv)))))

  (defthm aliases-normorderedp-of-elab-mod-initialize-aliases
    (implies (aliases-normorderedp aliases)
             (aliases-normorderedp (elab-mod-initialize-aliases idx elab-mod offset aliases)))
    :hints (("goal" :use ((:instance aliases-not-normorderedp-implies-unnormorderedp-idx
                           (aliases (elab-mod-initialize-aliases idx elab-mod offset aliases))))
             :in-theory (enable lookup-in-elab-mod-initialize-aliases
                                lhs-vars-normorderedp
                                lhatom-normorderedp
                                svar-index
                                svar-indexedp)
             :do-not-induct t))))


(defines svex-mod->initial-aliases
  :verify-guards nil
  :prepwork ((local (in-theory (disable acl2::nth-when-too-large-cheap))))
  (define svex-mod->initial-aliases ((modidx natp)
                                     (offset natp)
                                     (moddb moddb-ok)
                                     lhsarr)
    :guard (and (< modidx (moddb->nmods moddb))
                (<= (+ offset (moddb-mod-totalwires modidx moddb))
                    (lhss-length lhsarr)))
    :measure (nat-list-measure (list modidx 2 0))
    :returns (aliases (equal (len aliases)
                             (len lhsarr)))
    (b* (((stobj-get ;; name
           ninsts lhsarr)
          ((elab-mod (moddb->modsi modidx moddb)))
          (b* ((lhsarr (elab-mod-initialize-aliases 0 elab-mod offset lhsarr)))
            (mv ;; (elab-mod->name elab-mod)
             (elab-mod-ninsts elab-mod)
             lhsarr))))
      (svex-modinsts->initial-aliases
       0 ninsts modidx offset moddb lhsarr)))

  (define svex-modinsts->initial-aliases ((n natp)
                                          (ninsts)
                                          (modidx natp)
                                          (offset natp)
                                          (moddb moddb-ok)
                                          lhsarr)
    :guard (and (< modidx (moddb->nmods moddb))
                (equal ninsts (moddb-mod-ninsts modidx moddb))
                (<= n ninsts)
                (<= (+ offset (moddb-mod-totalwires modidx moddb))
                    (lhss-length lhsarr)))
    :measure (nat-list-measure
              (list modidx 1 (- (stobj-let ((elab-mod (moddb->modsi modidx moddb)))
                                           (ninsts)
                                           (elab-mod-ninsts elab-mod)
                                           ninsts)
                                (nfix n))))
    :returns (aliases (equal (len aliases)
                             (len lhsarr)))
    (b* ((ninsts (mbe :logic (stobj-let ((elab-mod (moddb->modsi modidx moddb)))
                                        (ninsts)
                                        (elab-mod-ninsts elab-mod)
                                        ninsts)
                      :exec ninsts))
         ((when (mbe :logic (zp (- ninsts (nfix n)))
                     :exec (eql n ninsts)))
          (lhsarr-fix lhsarr))
         (lhsarr (svex-modinst->initial-aliases (lnfix n) modidx offset moddb lhsarr)))
      (svex-modinsts->initial-aliases (1+ (lnfix n)) ninsts modidx offset moddb lhsarr)))

  (define svex-modinst->initial-aliases ((n natp)
                                         (modidx natp)
                                         (offset natp)
                                         (moddb moddb-ok)
                                         lhsarr)
    :guard (and (< modidx (moddb->nmods moddb))
                (< n (moddb-mod-ninsts modidx moddb))
                (<= (+ offset (moddb-mod-totalwires modidx moddb))
                    (lhss-length lhsarr)))
    :measure (nat-list-measure (list modidx 0 0))
    :returns (aliases (equal (len aliases)
                             (len lhsarr)))
    (b* (((stobj-get wireoffset submod)
          ((elab-mod (moddb->modsi modidx moddb)))
          (mv (elab-mod->inst-wireoffset n elab-mod)
              (elab-mod->inst-modidx n elab-mod)))
         ((unless (mbt (< submod (lnfix modidx))))
          (lhsarr-fix lhsarr)))
      (svex-mod->initial-aliases submod (+ (lnfix offset) wireoffset) moddb lhsarr)))
  ///

  (defthm moddb-mod-inst-wireoffset-gte-nwires
    (implies (and (moddb-ok moddb)
                  (< (nfix modidx) (nfix (nth *moddb->nmods* moddb))))
             (<= (elab-mod$a-nwires (nth modidx (nth *moddb->modsi* moddb)))
                 (moddb-mod-inst-wireoffset n modidx moddb)))
    :hints(("Goal" :in-theory (disable moddb-mod-inst-wireoffset-monotonic)
            :use ((:instance moddb-mod-inst-wireoffset-monotonic
                   (m n) (n 0)))))
    :rule-classes :linear)

  (verify-guards svex-mod->initial-aliases
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (moddb-mod-ninsts)
                                   (moddb-mod-inst-wireoffset-monotonic))
                   :use ((:instance moddb-mod-inst-wireoffset-monotonic
                          (n (+ 1 n)) (m (elab-mod$a-ninsts
                                          (nth modidx (nth *moddb->modsi* moddb))))))
                   :expand ((moddb-mod-inst-wireoffset (+ 1 n) modidx moddb))))))

  (deffixequiv-mutual svex-mod->initial-aliases
    :hints ((and stable-under-simplificationp
                 '(:expand
                   ((:free (modidx) (svex-modinsts->initial-aliases n ninsts modidx offset moddb lhsarr))
                    (:free (moddb) (svex-modinsts->initial-aliases n ninsts modidx offset moddb lhsarr))
                    (:free (moddb) (svex-mod->initial-aliases modidx offset moddb lhsarr))
                    (:free (moddb) (svex-modinst->initial-aliases n modidx offset moddb lhsarr)))))))

  (defthm svex-modinsts->initial-aliases-norm
    (implies (syntaxp (not (equal ninsts ''nil)))
             (equal (svex-modinsts->initial-aliases n ninsts modidx offset moddb lhsarr)
                    (svex-modinsts->initial-aliases n nil modidx offset moddb lhsarr)))
    :hints (("goal" :expand
             ((:free (ninsts) (svex-modinsts->initial-aliases n ninsts modidx offset moddb lhsarr))))))

  (local (defthm aliases-normorderedp-implies-lhslist-p
           (implies (aliases-normorderedp lhsarr)
                    (lhslist-p lhsarr))
           :hints(("Goal" :in-theory (enable aliases-normorderedp)))))

  (defthm-svex-mod->initial-aliases-flag
    (defthm aliases-normorderedp-of-svex-mod->initial-aliases
      (implies (aliases-normorderedp lhsarr)
               (aliases-normorderedp (svex-mod->initial-aliases modidx offset moddb lhsarr)))
      :hints ('(:expand ((svex-mod->initial-aliases modidx offset moddb lhsarr))))
      :flag svex-mod->initial-aliases)
    (defthm aliases-normorderedp-of-svex-modinsts->initial-aliases
      (implies (aliases-normorderedp lhsarr)
               (aliases-normorderedp (svex-modinsts->initial-aliases n ninsts modidx offset moddb lhsarr)))
      :hints ('(:expand ((svex-modinsts->initial-aliases n ninsts modidx offset moddb lhsarr))))
      :flag svex-modinsts->initial-aliases)
    (defthm aliases-normorderedp-of-svex-modinst->initial-aliases
      (implies (aliases-normorderedp lhsarr)
               (aliases-normorderedp (svex-modinst->initial-aliases n modidx offset moddb lhsarr)))
      :hints ('(:expand ((svex-modinst->initial-aliases n modidx offset moddb lhsarr))))
      :flag svex-modinst->initial-aliases)))








;; (local (defthm module-p-of-lookup-in-modalist
;;          (implies (and (modalist-p x)
;;                        (cdr (hons-assoc-equal k x)))
;;                   (module-p (cdr (hons-assoc-equal k x))))))


;; (define module-boundedp ((x module-p) (bound natp))
;;   (b* (((module x) x))
;;     (and (svarlist-boundedp (assigns-vars x.assigns) bound)
;;          (svarlist-boundedp (svar-map-vars x.delays) bound)
;;          (svarlist-boundedp (lhspairs-vars x.aliaspairs) bound)
;;          ;; (svarlist-boundedp (wirelist-vars x.wires) bound)p
;;          ))
;;   ///
;;   (deffixequiv module-boundedp)

;;   (defthm module-boundedp-of-greater
;;     (implies (and (svarlist-boundedp (module-vars x) bound1)
;;                   (<= (nfix bound1) (nfix bound2)))
;;              (svarlist-boundedp (module-vars x) bound2))))

;; (define modalist-all-boundedp ((x modalist-p) (moddb moddb-ok))
;;   :measure (len (modalist-fix x))
;;   (b* ((x (modalist-fix x))
;;        ((when (atom x)) t)
;;        ((cons name mod) (car x))
;;        (modidx (moddb-modname-get-index name moddb))
;;        ((unless modidx)
;;         (and (svarlist-boundedp (module-vars mod) 0)
;;              (modalist-all-boundedp (cdr x) moddb)))
;;        ((stobj-get totalwires)
;;         ((elab-mod (moddb->modsi modidx moddb)))
;;         (elab-mod->totalwires elab-mod)))
;;     (and (svarlist-boundedp (module-vars (cdar x)) totalwires)
;;          (modalist-all-boundedp (cdr x) moddb)))
;;   ///
;;   (deffixequiv modalist-all-boundedp))


(defthm exprs-bounded-of-modalist-lookup
  (implies (and (modalist-all-idxaddr-okp modalist moddb)
                (modalist-lookup name modalist)
                (moddb-modname-get-index name moddb)
                (moddb-ok moddb)
                (equal (modscope->modidx modscope) (moddb-modname-get-index name moddb)))
           (b* (((module mod) (modalist-lookup name modalist))
                (bound (modscope-local-bound modscope moddb)))
             (and (svarlist-idxaddr-okp (lhspairs-vars mod.aliaspairs) bound)
                  (svarlist-idxaddr-okp (assigns-vars mod.assigns) bound)
                  (svarlist-idxaddr-okp (assigns-vars mod.fixups) bound)
                  (svarlist-idxaddr-okp (constraintlist-vars mod.constraints) bound)
                  ;; (svarlist-idxaddr-okp
                  ;;  (svar-map-vars
                  ;;   (module->delays (modalist-lookup name modalist)))
                  ;;  bound)
                  )))
  :hints(("Goal" :in-theory (e/d (modalist-all-idxaddr-okp
                                  module-vars
                                  modscope-local-bound
                                  modalist-lookup)
                                 (moddb-mod-inst-wireoffset-recursive
                                  acl2::nth-when-too-large-cheap
                                  acl2::hons-assoc-equal-of-cons))
          :induct (len modalist)
          :expand ((hons-assoc-equal name modalist)
                   (modalist-all-idxaddr-okp modalist moddb)
                   (modalist-fix modalist)))))

(defthm moddb-modname-get-index-of-get-name
  (implies (and (moddb-ok moddb)
                (< (nfix modidx) (nfix (nth *moddb->nmods* moddb))))
           (equal (moddb-modname-get-index
                   (g :name (nth modidx (nth *moddb->modsi* moddb)))
                   moddb)
                  (nfix modidx)))
  :hints(("Goal" :in-theory (enable moddb-modname-get-index))))




(define constraintlist-add-scope (scope (x constraintlist-p))
  :returns (new-x constraintlist-p)
  (if (atom x)
      nil
    (cons (change-constraint (car x)
                             :name (cons scope (constraint->name (car x))))
          (constraintlist-add-scope scope (cdr x))))
  ///
  (defret constraintlist-vars-of-constraintlist-add-scope
    (equal (constraintlist-vars new-x)
           (constraintlist-vars x))
    :hints(("Goal" :in-theory (enable constraintlist-vars)))))


(defines svex-mod->flatten
  :prepwork ((local (in-theory (disable append))))
  :verify-guards nil
  ;; Input modalist has already been converted to indexed form.
  (define svex-mod->flatten ((scope modscope-p)
                             (modalist modalist-p)
                             (moddb moddb-ok))
    :guard (and (modscope-okp scope moddb)
                (modalist-all-idxaddr-okp modalist moddb))
    :measure (nat-list-measure (list (modscope->modidx scope) 2 0))
    :returns (mv (var-fails svarlist-p)
                 (mod-fails modnamelist-p)
                 (aliases lhspairs-p)
                 (assigns assigns-p)
                 (fixups assigns-p)
                 (constraints constraintlist-p)
                 ;; (delays svar-map-p
                 ;;         :hints ('(:in-theory (disable svex-mod->flatten
                 ;;                                       svex-modinst->flatten
                 ;;                                       svex-modinsts->flatten)
                 ;;                   :expand ((svex-mod->flatten scope modalist moddb)))))
                 )
    :short "Flatten an SV module into a list of assignments and aliases."
    (b* (((modscope scope))
         ((stobj-get name ninsts)
          ((elab-mod (moddb->modsi scope.modidx moddb)))
          (mv (elab-mod->name elab-mod)
              (elab-mod-ninsts elab-mod)))
         (mod (modalist-lookup name modalist))
         ((unless mod)
          (mv nil (list name) nil nil nil nil))
         (local-aliases (module->aliaspairs mod))
         (local-assigns (module->assigns mod))
         (local-fixups (module->fixups mod))
         (local-constraints (constraintlist-add-scope (modscope-fix scope) (module->constraints mod))))

      (time$
       (b* (;; (local-delays  (and mod (module->delays mod)))
            ((mv varfails1 abs-aliases) (lhspairs->absindexed local-aliases scope moddb))
            ((mv varfails2 abs-assigns) (assigns->absindexed local-assigns scope moddb))
            ((mv varfails3 abs-fixups) (assigns->absindexed local-fixups scope moddb))
            ((mv varfails4 abs-constraints) (constraintlist->absindexed local-constraints scope moddb))
            ;; We're never going to come back to this particular place in the
            ;; instantiation hierarchy -- i.e. we'll never call
            ;; svex->absindexed again with the same scope argument, so these
            ;; memoization tables aren't worth anything once we're done here.
            (- (clear-memoize-table 'svex->absindexed))
            ;; ((mv varfails3 abs-delays)  (svar-map->absindexed local-delays scope moddb))
            ((mv varfails5 modfails rest-aliases rest-assigns rest-fixups rest-constraints)
             (svex-modinsts->flatten 0 ninsts scope modalist moddb)))
         (mv (append-tr varfails1 varfails2 varfails3 varfails4 varfails5)
             modfails
             (append-tr abs-aliases rest-aliases)
             (append-tr abs-assigns rest-assigns)
             (append-tr abs-fixups rest-fixups)
             (append-tr abs-constraints rest-constraints)
             ;; (append-tr abs-delays rest-delays)
             ))
       :msg "; svex-mod->flatten ~x0: ~st sec, ~sa bytes, ~x1 instances, ~x2 aliases, ~x3 assigns~%"
       :args (list name ninsts (len local-aliases) (len local-assigns))
       :mintime 1)))

  (define svex-modinsts->flatten ((n natp)
                                  (ninsts)
                                  (scope modscope-p)
                                  (modalist modalist-p)
                                  (moddb moddb-ok))
    :guard (and (modscope-okp scope moddb)
                (modalist-all-idxaddr-okp modalist moddb)
                (equal ninsts
                       (b* (((modscope scope)))
                         (stobj-let ((elab-mod (moddb->modsi scope.modidx moddb)))
                                    (ninsts)
                                    (elab-mod-ninsts elab-mod)
                                    ninsts)))
                (<= n ninsts))
    :measure (nat-list-measure
              (list (modscope->modidx scope)
                    1 (- (b* (((modscope scope)))
                           (stobj-let ((elab-mod (moddb->modsi scope.modidx moddb)))
                                      (ninsts)
                                      (elab-mod-ninsts elab-mod)
                                      ninsts))
                         (nfix n))))
    :returns (mv (var-fails svarlist-p)
                 (mod-fails modnamelist-p)
                 (aliases lhspairs-p)
                 (assigns assigns-p
                         :hints ('(:in-theory (disable svex-mod->flatten
                                                       svex-modinst->flatten
                                                       svex-modinsts->flatten)
                                   :expand ((:free (ninsts)
                                             (svex-modinsts->flatten
                                              n ninsts scope modalist moddb))))))
                 (fixups assigns-p)
                 (constraints constraintlist-p))
    (b* ((ninsts (mbe :logic (b* (((modscope scope)))
                               (stobj-let ((elab-mod (moddb->modsi scope.modidx moddb)))
                                          (ninsts)
                                          (elab-mod-ninsts elab-mod)
                                          ninsts))
                      :exec ninsts))
         ((when (mbe :logic (zp (- ninsts (nfix n)))
                     :exec (eql n ninsts)))
          (mv nil nil nil nil nil nil))
         ((mv var-fails1 mod-fails1 aliases1 assigns1 fixups1 constraints1)
          (svex-modinst->flatten (lnfix n) scope modalist moddb))
         ((mv var-fails2 mod-fails2 aliases2 assigns2 fixups2 constraints2)
          (svex-modinsts->flatten (1+ (lnfix n)) ninsts scope modalist moddb)))
      (mv (append-tr var-fails1 var-fails2)
          (append-tr mod-fails1 mod-fails2)
          (append-tr aliases1 aliases2)
          (append-tr assigns1 assigns2)
          (append-tr fixups1 fixups2)
          (append-tr constraints1 constraints2))))

  (define svex-modinst->flatten ((n natp)
                                 (scope modscope-p)
                                 (modalist modalist-p)
                                 (moddb moddb-ok))
    :guard (and (modscope-okp scope moddb)
                (modalist-all-idxaddr-okp modalist moddb)
                (< n (b* (((modscope scope)))
                       (stobj-let ((elab-mod (moddb->modsi scope.modidx moddb)))
                                  (ninsts)
                                  (elab-mod-ninsts elab-mod)
                                  ninsts))))
    :measure (nat-list-measure (list (modscope->modidx scope) 0 0))
    :returns (mv (var-fails svarlist-p)
                 (mod-fails modnamelist-p)
                 (aliases lhspairs-p)
                 (assigns assigns-p
                         :hints ('(:in-theory (disable svex-mod->flatten
                                                       svex-modinst->flatten
                                                       svex-modinsts->flatten)
                                   :expand ((svex-modinst->flatten n scope modalist moddb)))))
                 (fixups assigns-p)
                 (constraints constraintlist-p))
    (b* ((newscope (modscope-push-frame n scope moddb))
         ((unless (mbt (< (modscope->modidx newscope)
                          (modscope->modidx scope))))
          (mv nil nil nil nil nil nil)))
      (svex-mod->flatten newscope modalist moddb)))
  ///

  (in-theory (disable svex-mod->flatten
                      svex-modinsts->flatten
                      svex-modinst->flatten))

  (verify-guards svex-mod->flatten)

  (deffixequiv-mutual svex-mod->flatten
    :hints ((and stable-under-simplificationp
                 (flag::expand-calls-computed-hint
                  clause '(svex-mod->flatten
                           svex-modinsts->flatten
                           svex-modinst->flatten)))))

  (defthm svex-modinsts->flatten-norm
    (implies (syntaxp (not (equal ninsts ''nil)))
             (equal (svex-modinsts->flatten n ninsts scope modalist moddb)
                    (svex-modinsts->flatten n nil scope modalist moddb)))
    :hints (("goal" :expand
             ((:free (ninsts) (svex-modinsts->flatten n ninsts scope modalist moddb))))))

  (defthm svarlist-boundedp-nil
    (svarlist-boundedp nil bound))





  ;; (defthm lhspairs-boundedp-append
  ;;   (iff (svarlist-boundedp (lhspairs-vars (append a b)) bound)
  ;;        (and (svarlist-boundedp (lhspairs-vars a) bound)
  ;;             (svarlist-boundedp (lhspairs-vars b) bound)))
  ;;   :hints(("Goal" :in-theory (e/d (lhspairs-vars)
  ;;                                  (lhspairs-fix-of-append))
  ;;           :induct (len a)
  ;;           :expand ((:free (a b c) (lhspairs-vars (cons a b)))
  ;;                    (:free (a b) (lhspairs-fix (cons a b)))
  ;;                    (lhspairs-vars a)
  ;;                    (lhspairs-fix a)
  ;;                    (append a b)))))

  ;; (defthm assigns-boundedp-append
  ;;   (iff (svarlist-boundedp (assigns-vars (append a b)) bound)
  ;;        (and (svarlist-boundedp (assigns-vars a) bound)
  ;;             (svarlist-boundedp (assigns-vars b) bound)))
  ;;   :hints(("Goal" :in-theory (e/d (assigns-vars)
  ;;                                  (assigns-fix-of-append))
  ;;           :induct (len a)
  ;;           :expand ((:free (a b c) (assigns-vars (cons a b)))
  ;;                    (:free (a b) (assigns-fix (cons a b)))
  ;;                    (assigns-vars a)
  ;;                    (assigns-fix a)
  ;;                    (append a b)))))

  (local (defthm svex-alist-keys-of-append
           (equal (svex-alist-keys (append a b))
                  (append (Svex-alist-keys a) (svex-alist-keys b)))
           :hints(("Goal" :in-theory (enable svex-alist-keys)))))


  (defthm modscope-top-bound-of-modscope-push-frame
    (equal (modscope-top-bound (modscope-push-frame n scope moddb) moddb)
           (modscope-top-bound scope moddb))
    :hints(("Goal" :in-theory (enable modscope-top-bound))))

  (defthm-svex-mod->flatten-flag
    (defthm svex-mod->flatten-bounded
      (b* (((mv & & aliases assigns fixups constraints)
            (svex-mod->flatten scope modalist moddb))
           (bound (modscope-top-bound scope moddb)))
        (implies (and (moddb-ok moddb)
                      (modscope-okp scope moddb)
                      (modalist-all-idxaddr-okp modalist moddb))
                 (and (svarlist-boundedp (lhspairs-vars aliases) bound)
                      (svarlist-boundedp (assigns-vars assigns) bound)
                      (svarlist-boundedp (constraintlist-vars constraints) bound)
                      (svarlist-boundedp (assigns-vars fixups) bound)
                      ;; (svarlist-boundedp (svar-map-vars delays) bound)
                      )))
      :hints ('(:expand ((svex-mod->flatten scope modalist moddb))))
      :flag svex-mod->flatten)

    (defthm svex-modinsts->flatten-bounded
      (b* (((mv & & aliases assigns fixups constraints)
            (svex-modinsts->flatten n ninsts scope modalist moddb))
           (bound (modscope-top-bound scope moddb)))
        (implies (and (moddb-ok moddb)
                      (modscope-okp scope moddb)
                      (modalist-all-idxaddr-okp modalist moddb))
                 (and (svarlist-boundedp (lhspairs-vars aliases) bound)
                      (svarlist-boundedp (assigns-vars assigns) bound)
                      (svarlist-boundedp (constraintlist-vars constraints) bound)
                      (svarlist-boundedp (assigns-vars fixups) bound)
                      ;; (svarlist-boundedp (svar-map-vars delays) bound)
                      )))

      :hints ('(:expand ((:free (ninsts)
                          (svex-modinsts->flatten n ninsts scope modalist moddb)))))
      :flag svex-modinsts->flatten)

    (defthm svex-modinst->flatten-bounded
      (b* (((mv & & aliases assigns fixups constraints)
            (svex-modinst->flatten n scope modalist moddb))
           (bound (modscope-top-bound scope moddb)))
        (implies (and (moddb-ok moddb)
                      (modscope-okp scope moddb)
                      (modalist-all-idxaddr-okp modalist moddb)
                      (< (nfix n)
                         (elab-mod$a-ninsts (nth (modscope->modidx scope)
                                                 (nth *moddb->modsi* moddb)))))
                 (and (svarlist-boundedp (lhspairs-vars aliases) bound)
                      (svarlist-boundedp (assigns-vars assigns) bound)
                      (svarlist-boundedp (constraintlist-vars constraints) bound)
                      (svarlist-boundedp (assigns-vars fixups) bound)
                      ;; (svarlist-boundedp (svar-map-vars delays) bound)
                      )))
      :hints ('(:expand ((svex-modinst->flatten
                          n scope modalist moddb))))
      :flag svex-modinst->flatten))

    (defthm svex-mod->flatten-bounded-top
      (b* (((mv & & aliases assigns fixups constraints)
            (svex-mod->flatten scope modalist moddb))
           (bound1 (modscope-top-bound scope moddb)))
        (implies (and (moddb-ok moddb)
                      (modscope-okp scope moddb)
                      (modalist-all-idxaddr-okp modalist moddb)
                      (equal (nfix bound) bound1))
                 (and (svarlist-boundedp (lhspairs-vars aliases) bound)
                      (svarlist-boundedp (assigns-vars assigns) bound)
                      (svarlist-boundedp (constraintlist-vars constraints) bound)
                      (svarlist-boundedp (assigns-vars fixups) bound)
                      ;; (svarlist-boundedp (svar-map-vars delays) bound)
                      )))
      :hints (("goal" :use svex-mod->flatten-bounded
               :in-theory (disable svex-mod->flatten-bounded)))))



(define paths-add-scope ((scope name-p) (paths pathlist-p))
  :returns (new-paths pathlist-p)
  (if (atom paths)
      nil
    (cons (make-path-scope :namespace scope :subpath (car paths))
          (paths-add-scope scope (cdr paths)))))

(define names->paths ((names namelist-p))
  :returns (new-paths pathlist-p)
  (if (atom names)
      nil
    (cons (make-path-wire :name (car names))
          (names->paths (cdr names)))))

(defines svex-mod->flat-names
  :verify-guards nil
  ;; Input modalist has already been converted to indexed form.
  (define svex-mod->flat-names ((modidx natp)
                                (modalist modalist-p)
                                (moddb moddb-ok))
    :guard (< modidx (moddb->nmods moddb))
    :measure (nat-list-measure (list modidx 2 0))
    :returns (names pathlist-p)
    (b* (((stobj-get name ninsts)
          ((elab-mod (moddb->modsi modidx moddb)))
          (mv (elab-mod->name elab-mod)
              (elab-mod-ninsts elab-mod)))
         (mod (modalist-lookup name modalist))
         (local-names (and mod (wirelist->names (module->wires mod)))))
      (append (names->paths local-names)
              (svex-modinsts->flat-names
               0 ninsts modidx modalist moddb))))

  (define svex-modinsts->flat-names ((n natp)
                                     (ninsts)
                                     (modidx natp)
                                     (modalist modalist-p)
                                     (moddb moddb-ok))
    :guard (and (< modidx (moddb->nmods moddb))
                (equal ninsts (stobj-let ((elab-mod (moddb->modsi modidx moddb)))
                                         (ninsts)
                                         (elab-mod-ninsts elab-mod)
                                         ninsts))
                (<= n ninsts))
    :measure (nat-list-measure
              (list modidx 1 (- (stobj-let ((elab-mod (moddb->modsi modidx moddb)))
                                           (ninsts)
                                           (elab-mod-ninsts elab-mod)
                                           ninsts)
                                (nfix n))))
    :returns (names pathlist-p)
    (b* ((ninsts (mbe :logic (stobj-let ((elab-mod (moddb->modsi modidx moddb)))
                                        (ninsts)
                                        (elab-mod-ninsts elab-mod)
                                        ninsts)
                      :exec ninsts))
         ((when (mbe :logic (zp (- ninsts (nfix n)))
                     :exec (eql n ninsts)))
          nil)
         (first (svex-modinst->flat-names (lnfix n) modidx modalist moddb)))
      (append first
              (svex-modinsts->flat-names (1+ (lnfix n)) ninsts modidx modalist moddb))))

  (define svex-modinst->flat-names ((n natp)
                                      (modidx natp)
                                      (modalist modalist-p)
                                      (moddb moddb-ok))
    :guard (and (< modidx (moddb->nmods moddb))
                (< n (stobj-let ((elab-mod (moddb->modsi modidx moddb)))
                                (ninsts)
                                (elab-mod-ninsts elab-mod)
                                ninsts)))
    :measure (nat-list-measure (list modidx 0 0))
    :returns (paths pathlist-p)
    (b* (((stobj-get submod name)
          ((elab-mod (moddb->modsi modidx moddb)))
          (mv (elab-mod->inst-modidx n elab-mod)
              (elab-mod->instname n elab-mod)))
         ((unless (mbt (< submod (lnfix modidx))))
          nil))
      (paths-add-scope name (svex-mod->flat-names submod modalist moddb))))
  ///
  (verify-guards svex-mod->flat-names))
