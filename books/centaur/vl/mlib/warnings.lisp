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
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))


(defsection vl-modulelist-clean-warnings
  :parents (warnings)
  :short "Clean the warnings of every module in a module list."
  :long "<p><b>Signature:</b> @(call vl-modulelist-clean-warnings) returns
@('X-PRIME').</p>

<p>We change every module in @('X') by applying @(see vl-clean-warnings) to its
warnings, and return the updated list of modules.  It may occasionally be
useful to run this transformation to clean up any redundant warnings that have
crept into the module list.</p>"

  (defund vl-modulelist-clean-warnings (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (b* (((when (atom x))
          nil)
         (old-warnings (vl-module->warnings (car x)))
         (new-warnings (vl-clean-warnings old-warnings)))
      (cons (change-vl-module (car x) :warnings new-warnings)
            (vl-modulelist-clean-warnings (cdr x)))))

  (local (in-theory (enable vl-modulelist-clean-warnings)))

  (defthm vl-modulelist-p-of-vl-modulelist-clean-warnings
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-clean-warnings x))))

  (defthm vl-modulelist->names-of-vl-modulelist-clean-warnings
    (equal (vl-modulelist->names (vl-modulelist-clean-warnings x))
           (vl-modulelist->names x))))



(defmapappend vl-modulelist-flat-warnings (x)
  (vl-module->warnings x)
  :guard (vl-modulelist-p x)
  :transform-true-list-p nil
  :parents (warnings)
  :short "Gather all warnings from a @(see vl-modulelist-p) into a single @(see
vl-warninglist-p)."

  :long "<p>This function appends together the warnings from all modules in a
module list.</p>

<p><b>Note</b>: if you want to summarize or print warnings, a @(see
vl-modwarningalist-p) is typically more useful than a flat list of
warnings.</p>

<p><b>Note</b>: this function does not clean the warnings in any way, and so
you may end up with many redundant warnings.  Because of this, it is probably a
good idea to call @(see vl-modulelist-clean-warnings) first, which cleans the
warnings of each module individually, before appending them all together.</p>"

  :rest
  ((defthm vl-warninglist-p-of-vl-modulelist-flat-warnings
     (implies (force (vl-modulelist-p x))
              (vl-warninglist-p (vl-modulelist-flat-warnings x))))))



(defsection vl-modwarningalist-p
  :parents (warnings)
  :short "A (fast) alist associating names to warnings."

  :long "<p>A modwarningalist associates strings to lists of warnings, and are
typically fast alists.</p>

<p>There are two common uses for modwarningalists.</p>

<p>First, we may generate such an alist when we want to associate some warnings
with a variety of modules.  That is, imagine a transformation that wants to add
warnings to five distinct modules.  It would be somewhat awkward to iteratively
update the @(see vl-modulelist-p), so instead we might create a modwarningalist
that associates target module names with the new warnings we want to add to
them.  The function @(see vl-apply-modwarningalist) can then be used to add
these warnings to a module list.</p>

<p>Second, modwarningalists can be useful when we want to print the warnings
for a bunch of modules.  Depending on the context, we might want to associate
either the orignames or names of the modules to their related warnings.</p>"

;; BOZO switch to defalist?

  (defund vl-modwarningalist-p (x)
    (declare (xargs :guard t))
    (if (atom x)
        t
      (and (consp (car x))
           (stringp (caar x))
           (vl-warninglist-p (cdar x))
           (vl-modwarningalist-p (cdr x)))))

  (local (in-theory (enable vl-modwarningalist-p)))

  (defthm vl-modwarningalist-p-when-not-consp
    (implies (not (consp x))
             (equal (vl-modwarningalist-p x)
                    t)))

  (defthm vl-modwarningalist-p-of-cons
    (equal (vl-modwarningalist-p (cons a x))
           (and (consp a)
                (stringp (car a))
                (vl-warninglist-p (cdr a))
                (vl-modwarningalist-p x))))

  (defthm vl-warninglist-p-of-cdr-of-hons-assoc-equal-when-vl-modwarningalist-p
    (implies (vl-modwarningalist-p x)
             (vl-warninglist-p (cdr (hons-assoc-equal a x)))))

  (defthm vl-modwarningalist-p-of-append
    (implies (and (vl-modwarningalist-p x)
                  (vl-modwarningalist-p y))
             (vl-modwarningalist-p (append x y))))

  (defthm vl-modwarningalist-p-of-hons-shrink-alist
    (implies (and (vl-modwarningalist-p x)
                  (vl-modwarningalist-p acc))
             (vl-modwarningalist-p (hons-shrink-alist x acc)))
    :hints(("Goal" :in-theory (enable (:induction hons-shrink-alist)))))

  (defthm vl-modwarningalist-p-of-insert
    (implies (and (consp a)
                  (stringp (car a))
                  (vl-warninglist-p (cdr a))
                  (vl-modwarningalist-p x))
             (vl-modwarningalist-p (insert a x)))
    :hints(("Goal" :in-theory (enable (:ruleset set::primitive-rules)))))

  (defthm vl-modwarningalist-p-of-mergesort
    (implies (force (vl-modwarningalist-p x))
             (vl-modwarningalist-p (mergesort x))))

  (defthm string-listp-of-alist-keys-when-vl-modwarningalist-p
    (implies (vl-modwarningalist-p x)
             (string-listp (alist-keys x)))
    :hints(("Goal" :induct (len x)))))




(defsection vl-extend-modwarningalist
  :parents (warnings)
  :short "Add a single warning to a @(see vl-modwarningalist-p)."

  :long "<p><b>Signature:</b> @(call vl-extend-modwarningalist) produces a new
warning alist.</p>

<p>This function is useful in the incremental construction of warning alists;
it adds a particular @('warning') to the existing warnings for @('modname') in
@('walist').</p>"

  (defund vl-extend-modwarningalist (modname warning walist)
    (declare (xargs :guard (and (stringp modname)
                                (vl-warning-p warning)
                                (vl-modwarningalist-p walist))))
    (b* ((old-warnings (cdr (hons-get modname walist)))
         (new-warnings (cons warning old-warnings)))
      (hons-acons modname new-warnings walist)))

  (local (in-theory (enable vl-extend-modwarningalist)))

  (defthm vl-modwarningalist-p-of-vl-extend-modwarningalist
    (implies (and (force (stringp modname))
                  (force (vl-warning-p warning))
                  (force (vl-modwarningalist-p walist)))
             (vl-modwarningalist-p (vl-extend-modwarningalist modname warning walist)))))



(defsection vl-extend-modwarningalist-list
  :parents (warnings)
  :short "Add a list of warnings to a @(see vl-modwarningalist-p)."

  :long "<p><b>Signature:</b> @(call vl-extend-modwarningalist-list) produces a new
warning alist.</p>

<p>This function is useful in the incremental construction of warning alists;
it adds the list of @('warnings') to the existing warnings for @('modname') in
@('walist').</p>"

  (defund vl-extend-modwarningalist-list (modname warnings walist)
    (declare (xargs :guard (and (stringp modname)
                                (vl-warninglist-p warnings)
                                (vl-modwarningalist-p walist))))
    (b* ((old-warnings (cdr (hons-get modname walist)))
         (new-warnings (append-without-guard warnings old-warnings)))
      (hons-acons modname new-warnings walist)))

  (local (in-theory (enable vl-extend-modwarningalist-list)))

  (defthm vl-modwarningalist-p-of-vl-extend-modwarningalist-list
    (implies (and (force (stringp modname))
                  (force (vl-warninglist-p warnings))
                  (force (vl-modwarningalist-p walist)))
             (vl-modwarningalist-p (vl-extend-modwarningalist-list modname warnings walist)))))



(defsection vl-apply-modwarningalist-aux
  :parents (vl-apply-modwarningalist)

  (defund vl-apply-modwarningalist-aux (x alist)
    (declare (xargs :guard (and (vl-module-p x)
                                (vl-modwarningalist-p alist))))
    (b* ((entry (hons-get (vl-module->name x) alist))
         ((unless entry)
          x)
         (warnings (vl-module->warnings x))
         (warnings (revappend-without-guard (cdr entry) warnings)))
      (change-vl-module x :warnings warnings)))

  (local (in-theory (enable vl-apply-modwarningalist-aux)))

  (defthm vl-module-p-of-vl-apply-modwarningalist-aux
    (implies (and (force (vl-module-p x))
                  (force (vl-modwarningalist-p alist)))
             (vl-module-p (vl-apply-modwarningalist-aux x alist))))

  (defthm vl-module->name-of-vl-apply-modwarningalist-aux
    (equal (vl-module->name (vl-apply-modwarningalist-aux x alist))
           (vl-module->name x))))


(defprojection vl-apply-modwarningalist (x alist)
  (vl-apply-modwarningalist-aux x alist)
  :guard (and (vl-modulelist-p x)
              (vl-modwarningalist-p alist))
  :result-type vl-modulelist-p
  :parents (warnings)
  :short "Annotate modules with the warnings named in a @(see
vl-modwarningalist-p)."

  :long "<p><b>Signature:</b> @(call vl-apply-modwarningalist) returns
@('mods-prime').</p>

<p>We are given @('x'), a @(see vl-modulelist-p), and @('alist'), a @(see
vl-modwarningalist-p), which should be a fast alist.  We change @('x') by
adding any warnings that are associated with each module's name in
@('alist').</p>"

    :rest
    ((defthm vl-modulelist->names-of-vl-apply-modwarningalist
       (equal (vl-modulelist->names (vl-apply-modwarningalist x alist))
              (vl-modulelist->names x)))))


(defsection vl-clean-modwarningalist
  :parents (warnings)
  :short "@(call vl-clean-modwarningalist) shrinks a @(see
vl-modwarningalist-p) and cleans all of its warning lists with @(see
vl-clean-warnings)."

  :long "<p>We return a new fast-alist that is independent of @('x').  Any
modules which have no warnings are eliminated.</p>"

  (defund vl-clean-modwarningalist-aux (x acc)
    "Assumes X has already been shrunk, so we may safely recur down it."
    (declare (xargs :guard (and (vl-modwarningalist-p x)
                                (vl-modwarningalist-p acc))))
    (b* (((when (atom x))
          acc)
         (name     (caar x))
         (warnings (vl-clean-warnings (cdar x)))
         (acc      (if (atom warnings)
                       acc
                     (hons-acons name warnings acc))))
      (vl-clean-modwarningalist-aux (cdr x) acc)))

  (defund vl-clean-modwarningalist (x)
    (declare (xargs :guard (vl-modwarningalist-p x)))
    (b* ((x-shrink (hons-shrink-alist x nil))
         (ret      (vl-clean-modwarningalist-aux x-shrink nil))
         (-        (fast-alist-free x-shrink)))
        ret))

  (local (in-theory (enable vl-clean-modwarningalist
                            vl-clean-modwarningalist-aux)))

  (defthm vl-modwarningalist-p-of-vl-clean-modwarningalist-aux
    (implies (and (vl-modwarningalist-p x)
                  (vl-modwarningalist-p acc))
             (vl-modwarningalist-p (vl-clean-modwarningalist-aux x acc))))

  (defthm vl-modwarningalist-p-of-vl-clean-modwarningalist
    (implies (force (vl-modwarningalist-p x))
             (vl-modwarningalist-p (vl-clean-modwarningalist x)))))




(defsection vl-origname-modwarningalist
  :parents (warnings)
  :short "@(call vl-origname-modwarningalist) constructs a @(see
vl-modwarningalist-p) from a module list, using @('orignames') as the keys."

  :long "<p>Unparameterization causes problems for printing warnings about each
module, because, e.g., instead of having warnings about @('adder'), we actually
have warnings about @('adder$width=5') and @('adder$width=13'), etc.  Yet the
end-user typically shouldn't be bothered with looking at the warnings for each
specialized version of @('adder'); he just wants to see all of the
warnings.</p>

<p>This function gathers up all warnings associated with each module, and
builds a @(see vl-modwarningalist-p) that maps @('orignames') to warnings.  We
take care to ensure that all of the warnings associated with each name are
properly cleaned up and merged.</p>"

  (defund vl-origname-modwarningalist-aux (x acc)
    (declare (xargs :guard (and (vl-modulelist-p x)
                                (vl-modwarningalist-p acc))))
    (b* (((when (atom x))
          acc)
         (origname      (vl-module->origname (car x)))
         (my-warnings   (vl-module->warnings (car x)))
         (prev-warnings (cdr (hons-get origname acc)))
         (new-warnings  (revappend-without-guard my-warnings prev-warnings))
         (acc           (hons-acons origname new-warnings acc)))
      (vl-origname-modwarningalist-aux (cdr x) acc)))

  (defund vl-origname-modwarningalist (x)
    (declare (xargs :guard (vl-modulelist-p x)
                    :verify-guards nil))
    (b* ((unclean (vl-origname-modwarningalist-aux x nil))
         (ret     (vl-clean-modwarningalist unclean))
         (-       (fast-alist-free unclean)))
        ret))

  (local (in-theory (enable vl-origname-modwarningalist-aux
                            vl-origname-modwarningalist)))

  (defthm vl-modwarningalist-p-of-vl-origname-modwarningalist-aux
    (implies (and (force (vl-modulelist-p x))
                  (force (vl-modwarningalist-p acc)))
             (vl-modwarningalist-p (vl-origname-modwarningalist-aux x acc))))

  (verify-guards vl-origname-modwarningalist)

  (defthm vl-modwarningalist-p-of-vl-origname-modwarningalist
    (implies (force (vl-modulelist-p x))
             (vl-modwarningalist-p (vl-origname-modwarningalist x)))))

