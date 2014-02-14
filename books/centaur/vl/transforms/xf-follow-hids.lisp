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
(include-book "xf-resolve-ranges")
(include-book "../mlib/hierarchy")
(include-book "../mlib/find-item")
(include-book "../mlib/expr-tools")
(include-book "../mlib/hid-tools")
(include-book "../wf-ranges-resolved-p")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))


;; BOZO hid-elim stuff is sort of deprecated and has been split off into another
;; file, need to clean this up, and clean up its documentation

(local (defthm crock3
         (implies (and (force (stringp name))
                       (force (vl-module-p x)))
                  (symbolp (tag (vl-find-moduleitem name x))))
         :hints(("Goal"
                 :in-theory (disable vl-find-moduleitem-type-when-nothing-else)
                 :use ((:instance vl-find-moduleitem-type-when-nothing-else))))))


(defconst *vl-unresolved-hid-msg*

; I want a standardized format for :VL-UNRESOLVED-HID warnings so that I can
; gather them up and generate a chip-wide report on any unresolved hids.  Each
; such warning should have the following arguments:
;
;   ~a0   The full HID we were following
;         (i.e., foo.bar.baz-inst.boop)
;
;   ~m1   The module name that ~a0 was encountered in
;         ("mymod")
;
;   ~m2   The name of the module we arrived at when we had the problem
;         ("baz")
;
;   ~s3   The part of the name that we could not find or had a problem with
;         ("boop")
;
;   ~s4   Any additional information
;         ("boop is an event, we expected a reg or net")

  "While attempting to resolve ~a0 in module ~m1, we arrived at module ~m2, ~
   where we were unable to resolve ~s3.  (~s4)")


(define vl-find-hid-module-aux
  :parents (hid-elim)
  :short "Main function for following hierarchical identifiers."

  ((x "Some hierarchical identifier expression that we want to resolve; we're
       recurring down @('x').  Our goal is to follow this HID and see where it
       leads."
      (and (vl-expr-p x)
           (vl-hidexpr-p x)))

   (curr "A module.  We assume that @('X') is relative to module
          @('CURR'). That is, @('CURR') typically begins as @('top') for global
          hierarchical identifiers, or is set to the current module when
          resolving local hierarchical names."
         vl-module-p)

   (mods "All modules (so we can look up other modules."
         vl-modulelist-p)

   (modalist "For fast lookups."
             (equal modalist (vl-modalist mods)))

   (warnings "An ordinary @(see warnings) accumulator."
             vl-warninglist-p)

   (ctx-hid "For better error messages.  The full, original hierarchical
             identifier we were trying to resolve."
            vl-expr-p)

   (ctx-modname "For better error messages.   The name of the module wherein
                 @('CTX-HID') was found."))

  :returns
  (mv (warnings vl-warninglist-p
                "May be extended with fatal warnings if we can't follow
                @('x')."
                :hints(("Goal" :in-theory (disable (force)))))

      (x-prime vl-expr-p
               :hyp (and (force (vl-expr-p x))
                         (force (vl-hidexpr-p x))
                         (force (vl-module-p curr))
                         (force (vl-modulelist-p mods))
                         (force (equal modalist (vl-modalist mods))))
               "A changed version of @('x'), where every HID expression within
                @('X') has been annotated with @('VL_HID_CURRENT_MOD')
                attributes that say, e.g., for @('foo.bar'), what module is
                \"foo\" in?")

      (modname maybe-stringp :rule-classes :type-prescription
               "@('nil') if we can't follow @('x').  Otherwise, the name of
                the ultimate target module."
               :hints(("Goal" :in-theory (disable (force)))))

      (range-resolvedp booleanp :rule-classes :type-prescription
                       "On success, says whether the ultimate target wire
                        had a resolved range like @('[3:0]') instead of an
                        unresolved range like @('[width-1:0]')."
                       :hints(("Goal" :in-theory (disable (force)))))

      (range (vl-maybe-range-p range)
             "On success, the actual range of the target wire.  We only produce
              a range and say it is resolved if (1) the wire is unsigned,
              and (2) there are no arrdims.  These are important for soundness;
              see @(see vl-hidexpr-hid-elim).  It would probably not be too
              hard to relax the unsigned restriction, but arrdims might be more
              difficult."
             :hyp (and (force (vl-expr-p x))
                       (force (vl-hidexpr-p x))
                       (force (vl-module-p curr))
                       (force (vl-modulelist-p mods))
                       (force (equal modalist (vl-modalist mods))))))

  :long "<p>This is our main function for following hierarchical identifiers
and annotating them with @('VL_HID_RESOLVED_MODULE_NAME'),
@('VL_HID_RESOLVED_RANGE_P'), etc., as described in @(see hid-elim).</p>

<p>Our goal is to follow X and see what module it leads to.  That is, given an
identifier like @('foo.bar.baz.wire'), we try to find out what kind of module
@('baz') is.  Furthermore, if we can tell how wide @('wire') is, we would like
to report this information as well.</p>"

  :verify-guards nil

  (b* (((when (vl-fast-atom-p x))
        (b* ((name (vl-hidpiece->name (vl-atom->guts x)))
             (item (vl-find-moduleitem name curr))

             ((unless item)
              (mv (fatal :type :vl-unresolved-hid
                         :msg *vl-unresolved-hid-msg*
                         :args (list ctx-hid
                                     ctx-modname
                                     (vl-module->name curr)
                                     name
                                     (cat name " not found")))
                  x nil nil nil))

             ((unless (or (eq (tag item) :vl-netdecl)
                          (eq (tag item) :vl-regdecl)))
              (mv (fatal :type :vl-unresolved-hid
                         :msg *vl-unresolved-hid-msg*
                         :args (list ctx-hid
                                     ctx-modname
                                     (vl-module->name curr)
                                     name
                                     (cat "Expected " name " to be a net or reg, but found "
                                          (symbol-name (tag item)))))
                  x nil nil nil))

             ((mv range signedp arrdims)
              (if (eq (tag item) :vl-netdecl)
                  (mv (vl-netdecl->range item)
                      (vl-netdecl->signedp item)
                      (vl-netdecl->arrdims item))
                (mv (vl-regdecl->range item)
                    (vl-regdecl->signedp item)
                    (vl-regdecl->arrdims item))))

             (range
              ;; Try to simplify the range.  We didn't originally do this, but
              ;; I later found that we weren't fully resolving some HIDs
              ;; because their declared ranges were things like [`foo-1:0].  So
              ;; we can do a bit better by trying to resolve the ranges.
              (b* (((when (vl-maybe-range-resolved-p range))
                          range)
                         ((mv ?warnings new-range)
                          (vl-rangeresolve range nil)))
                      new-range))

             (range-resolvedp
              ;; See vl-hid-expr-elim, don't say it's resolved unless it's also
              ;; unsigned and has no arrdims.
              (and (not signedp)
                   (not arrdims)
                   (vl-maybe-range-resolved-p range)))

             (modname (string-fix (vl-module->name curr))))

          (mv (ok) x modname range-resolvedp range)))

       ((unless (mbt (consp x)))
        (impossible)
        (mv (ok) x nil nil nil))

       ((vl-nonatom x) x)

       ((unless (and (eq x.op :vl-hid-dot)
                     (vl-fast-atom-p (first x.args))))
        (mv (fatal :type :vl-unresolved-hid
                   :msg *vl-unresolved-hid-msg*
                   :args (list ctx-hid
                               ctx-modname
                               (vl-module->name curr)
                               "the hid, due to array indexing"
                               "Hids with indexes are not yet supported."))
            x nil nil nil))

       ;; As above, find out what module item the first part of the ID is
       ;; talking about.
       (name1 (vl-hidpiece->name (vl-atom->guts (first x.args))))
       (item  (vl-find-moduleitem name1 curr))
       ((unless item)
        (mv (fatal :type :vl-unresolved-hid
                   :msg *vl-unresolved-hid-msg*
                   :args (list ctx-hid
                               ctx-modname
                               (vl-module->name curr)
                               name1
                               (cat name1 " not found")))
            x nil nil nil))

       ((unless (mbe :logic (vl-modinst-p item)
                     :exec (eq (tag item) :vl-modinst)))
        (mv (fatal :type :vl-unresolved-hid
                   :msg *vl-unresolved-hid-msg*
                   :args (list ctx-hid
                               ctx-modname
                               (vl-module->name curr)
                               name1
                               (cat "Expected " name1
                                    " to be a module instance, but found "
                                    (symbol-name (tag item)))))
            x nil nil nil))

       (submod-name (vl-modinst->modname item))
       (submod      (vl-fast-find-module submod-name mods modalist))
       ((unless submod)
        (mv (fatal :type :vl-unresolved-hid
                   :msg *vl-unresolved-hid-msg*
                   :args (list ctx-hid
                               ctx-modname
                               (vl-module->name curr)
                               name1
                               (cat name1 " is an instance of " submod-name
                                    ", which is not a defined module.")))
            x nil nil nil))

       ;; Historically, I once caused a warning if we ran into a parameterized
       ;; module.  Now I don't worry about this during the following stage; it
       ;; only matters in the elimination stage.
       ;; At this point everything is working out.  Ready to recur.
       ((mv warnings tail-prime ?modname range-resolvedp range)
        (vl-find-hid-module-aux (second x.args)
                                submod mods modalist warnings
                                ctx-hid ctx-modname))

       (atts (acons "VL_HID_CURRENT_MOD"
                    (make-vl-atom :guts (vl-string (vl-module->name curr)))
                    x.atts))

       (args-prime (list (first x.args) tail-prime))

       (x-prime (change-vl-nonatom x
                                   :args args-prime
                                   :atts atts)))

    (mv (ok) x-prime
        (string-fix (vl-module->name curr))
        range-resolvedp range))
  ///

  (verify-guards vl-find-hid-module-aux)

  (defthm vl-atom-p-of-vl-find-hid-module-aux
    (implies (and (force (vl-expr-p x))
                  (force (vl-hidexpr-p x))
                  (force (vl-module-p curr))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods))))
             (iff (vl-atom-p (mv-nth 1 (vl-find-hid-module-aux x curr mods modalist warnings
                                                               ctx-hid ctx-modname)))
                  (vl-atom-p x))))

  (defthm vl-nonatom->op-of-vl-find-hid-module-aux
    (implies (and (force (vl-expr-p x))
                  (force (vl-hidexpr-p x))
                  (force (vl-module-p curr))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods)))
                  (force (vl-nonatom-p x)))
             (equal (vl-nonatom->op
                     (mv-nth 1 (vl-find-hid-module-aux x curr mods modalist warnings
                                                       ctx-hid ctx-modname)))
                    (vl-nonatom->op x))))

  (defthm len-of-vl-nonatom->args-of-vl-find-hid-module-aux
    (implies (and (force (vl-expr-p x))
                  (force (vl-hidexpr-p x))
                  (force (vl-module-p curr))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods)))
                  (force (vl-nonatom-p x)))
             (equal (len (vl-nonatom->args
                          (mv-nth 1 (vl-find-hid-module-aux x curr mods modalist warnings
                                                            ctx-hid ctx-modname))))
                    (len (vl-nonatom->args x)))))

  (defthm vl-range-p-of-vl-find-hid-module-aux
    (implies (and (force (vl-expr-p x))
                  (force (vl-hidexpr-p x))
                  (force (vl-module-p curr))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods))))
             (equal (vl-range-p (mv-nth 4 (vl-find-hid-module-aux x curr mods modalist warnings
                                                                  ctx-hid ctx-modname)))
                    (if (mv-nth 4 (vl-find-hid-module-aux x curr mods modalist warnings
                                                          ctx-hid ctx-modname))
                        t
                      nil))))

  (defthm vl-range-resolved-p-of-vl-find-hid-module-aux
    (implies (and (mv-nth 3 (vl-find-hid-module-aux x curr mods modalist warnings
                                                    ctx-hid ctx-modname))
                  (mv-nth 4 (vl-find-hid-module-aux x curr mods modalist warnings
                                                    ctx-hid ctx-modname))
                  (force (vl-expr-p x))
                  (force (vl-hidexpr-p x))
                  (force (vl-module-p curr))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods))))
             (vl-range-resolved-p
              (mv-nth 4 (vl-find-hid-module-aux x curr mods modalist warnings
                                                ctx-hid ctx-modname)))))
  )


(define vl-find-hid-module
  :parents (hid-elim)
  :short "Top-level function for following hierarchical identifiers."

  ((x        (and (vl-expr-p x)
                  (vl-hidexpr-p x))
             "A hierarchical identifier that occurs somewhere in @('mod').")
   (mod      vl-module-p)
   (mods     vl-modulelist-p
             "List of all modules, so we can look up submodules.")
   (modalist (equal modalist (vl-modalist mods))
             "For fast lookups.")
   (toplev   (equal toplev (vl-modulelist-toplevel mods))
             "Names of all top level modules, so we can tell which HIDs are
              local versus global.")
   (warnings vl-warninglist-p
             "Typically the warnings accumulator for @('mod')."))

  :returns (mv warnings x-prime modname range-resolvedp range localp)

  :long "<p>Hierarchical identifiers can be either local (i.e., beginning with
the name of a submodule), or global (i.e., beginning with the name of some
top-level module).  The main task of this function is to determine whether
@('X') is local or global, then call upon @(see vl-find-hid-module-aux) to do
the real work of following @('X').</p>

<p>Our goal is to follow X and see what module it leads to.  That is, given an
identifier like @('foo.bar.baz.wire'), we try to find out what kind of module
@('baz') is.  Furthermore, if we can tell how wide @('wire') is, we would like
to report this information as well.</p>

<p>Except for @('LOCALP'), the outputs are as in @(see vl-find-hid-module-aux).
On success, @('LOCALP') says whether this is a local hierarchical
identifier.</p>"

  (b* (((when (vl-atom-p x))
        (mv (fatal :type :vl-bad-hid
                   :msg "Trying to follow the hierarchical identifier ~a0, but ~
                           it's only got one component?  What the heck??"
                   :args (list x))
            x nil nil nil nil))

       ((vl-nonatom x) x)

       ((unless (and (eq x.op :vl-hid-dot)
                     (vl-fast-atom-p (first x.args))))
        (mv (fatal :type :vl-bad-hid
                   :msg "~a0: hids with indexes aren't supported yet."
                   :args (list x))
            x nil nil nil nil))

       ;; Now, the only question is whether or not this is a local or global
       ;; hid.  If it's local, it should correspond to the name of some
       ;; submodule.

       (name1 (vl-hidpiece->name (vl-atom->guts (first x.args))))
       (item  (vl-find-moduleitem name1 mod))

       ((when item)
        ;; Okay, this seems like a local hierarchical identifier.  Lets try
        ;; to get it using our aux function.  Note that we just pass in X
        ;; itself, so we'll redundantly look at it and do our extra checks to
        ;; make sure it's a valid module instance, etc.
        (b* (((mv warnings x-prime modname range-resolvedp range)
              (vl-find-hid-module-aux x mod mods modalist warnings x
                                      (vl-module->name mod))))
          (mv warnings x-prime modname range-resolvedp range t)))

       ;; Otherwise, maybe this is a global hierarchical identifier.  Lets
       ;; see if the first name matches the name of any module.
       (ref-mod (vl-fast-find-module name1 mods modalist))

       ((unless (and ref-mod
                     (member-equal name1 toplev)))
        (mv (fatal :type :vl-bad-hid
                   :msg "Trying to follow the hierarchical identifier ~a0, ~
                         but ~s1 is not a locally defined name and is not ~
                         among the top-level module names, ~&2.~%"
                   :args (list x name1 toplev))
            x nil nil nil nil))

       ;; Historically I caused a fatal warning if ref-mod had paramdecls, but now
       ;; we don't care about that until the elimination stage.

       ;; In this case we have to add the VL_HID_CURRENT_MOD attribute ourselves,
       ;; since we're only giving the tail to the aux function.
       (atts (vl-nonatom->atts x))
       (atts (acons "VL_HID_CURRENT_MOD"
                    (make-vl-atom :guts
                                  (vl-string (vl-module->name ref-mod)))
                    atts))

       ;; Okay, this seems like a global hierarchical identifier.  Try to get
       ;; it using our aux function.  In this case, we only chase the tail
       ;; because the head just got us to ref-mod.
       ((mv warnings tail-prime modname range-resolvedp range)
        (vl-find-hid-module-aux (second x.args) ref-mod mods modalist warnings x
                                (vl-module->name mod)))

       (args-prime (list (first x.args) tail-prime))
       (x-prime (change-vl-nonatom x :args args-prime :atts atts)))

    (mv warnings x-prime modname range-resolvedp range nil))

    ///

  (defthm vl-warninglist-p-of-vl-find-hid-module
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 0 (vl-find-hid-module x mod mods modalist toplev warnings)))))

  (defthm vl-expr-p-of-vl-find-hid-module
    (implies (and (force (vl-expr-p x))
                  (force (vl-hidexpr-p x))
                  (force (vl-module-p mod))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods))))
             (vl-expr-p
              (mv-nth 1 (vl-find-hid-module x mod mods modalist toplev warnings)))))

  (defthm vl-atom-p-of-vl-find-hid-module
    (implies (and (force (vl-expr-p x))
                  (force (vl-hidexpr-p x))
                  (force (vl-module-p mod))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods))))
             (iff (vl-atom-p (mv-nth 1 (vl-find-hid-module x mod mods modalist toplev warnings)))
                  (vl-atom-p x))))

  (defthm vl-nonatom->op-of-vl-find-hid-module
    (implies (and (force (vl-nonatom-p x))
                  (force (vl-expr-p x))
                  (force (vl-hidexpr-p x))
                  (force (vl-module-p mod))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods))))
             (equal (vl-nonatom->op
                     (mv-nth 1 (vl-find-hid-module x mod mods modalist toplev warnings)))
                    (vl-nonatom->op x))))

  (defthm len-of-vl-nonatom->args-of-vl-find-hid-module
    (implies (and (force (vl-nonatom-p x))
                  (force (vl-expr-p x))
                  (force (vl-hidexpr-p x))
                  (force (vl-module-p mod))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods))))
             (equal (len (vl-nonatom->args
                          (mv-nth 1 (vl-find-hid-module x mod mods modalist toplev warnings))))
                    (len (vl-nonatom->args x)))))

  (defthm stringp-of-vl-find-hid-module
    (implies (and (force (vl-expr-p x))
                  (force (vl-hidexpr-p x))
                  (force (vl-module-p mod))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods))))
             (equal (stringp (mv-nth 2 (vl-find-hid-module x mod mods modalist toplev warnings)))
                    (if (mv-nth 2 (vl-find-hid-module x mod mods modalist toplev warnings))
                        t
                      nil))))

  (defthm booleanp-of-vl-find-hid-module
    (booleanp (mv-nth 3 (vl-find-hid-module x mod mods modalist toplev warnings))))

  (defthm vl-range-p-of-vl-find-hid-module
    (implies (and (force (vl-expr-p x))
                  (force (vl-hidexpr-p x))
                  (force (vl-module-p mod))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods))))
             (equal (vl-range-p (mv-nth 4 (vl-find-hid-module x mod mods modalist toplev warnings)))
                    (if (mv-nth 4 (vl-find-hid-module x mod mods modalist toplev warnings))
                        t
                      nil))))

  (defthm vl-range-resolved-p-of-vl-find-hid-module
    (implies (and (mv-nth 3 (vl-find-hid-module x mod mods modalist toplev warnings))
                  (mv-nth 4 (vl-find-hid-module x mod mods modalist toplev warnings))
                  (force (vl-expr-p x))
                  (force (vl-hidexpr-p x))
                  (force (vl-module-p mod))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods))))
             (vl-range-resolved-p
              (mv-nth 4 (vl-find-hid-module x mod mods modalist toplev warnings))))))




(defsection vl-expr-follow-hids
  :parents (hid-elim)

  :short "Annotate hierarchical identifiers throughout an expression with
attributes such as @('VL_HID_RESOLVED_MODULE_NAME'), as described in @(see
hid-elim)."

  :long "<p><b>Signature</b>: @(call vl-expr-follow-hids) returns @('(mv
warnings x-prime)').</p>

<h5>Inputs</h5>

<ul>

<li>@('X') is any expression, which we are recurring over.</li>

<li>@('MOD') is the module that @('X') comes from.</li>

<li>@('MODS') is the list of all modules, and @('MODALIST') is the @(see
vl-modalist) for @('MODS') (for fast lookups).</li>

<li>@('TOPLEV') is the list of all top-level modules; see @(see
vl-modulelist-toplevel).</li>

<li>@('WARNINGS') is the @(see warnings) accumulator for @('MOD').</li>

</ul>

<p>We try to annotate every hierarchical identifier throughout @('X') with the
attributes described in @(see hid-elim) and return the updated expression.
Fatal warnings will be added if we have problems following any hierarchical
identifier.</p>"

  (mutual-recursion

   (defund vl-expr-follow-hids (x mod mods modalist toplev warnings)
     "Returns (MV WARNINGS X-PRIME)"
     (declare (xargs :guard (and (vl-expr-p x)
                                 (vl-module-p mod)
                                 (vl-modulelist-p mods)
                                 (equal modalist (vl-modalist mods))
                                 (equal toplev (vl-modulelist-toplevel mods))
                                 (vl-warninglist-p warnings))
                     :hints(("Goal" :in-theory (disable (force))))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))

     (cond ((vl-hidexpr-p x)
            (b* (((when (vl-fast-atom-p x))
                  (prog2$ (er hard? 'vl-expr-follow-hids "Jared thinks this is impossible.")
                          (mv warnings x)))
                 ((when (assoc-equal "VL_HID_RESOLVED_MODULE_NAME" (vl-nonatom->atts x)))
                  ;; The following is an effort to be idempotent, and prevents
                  ;; us from following a HID that has already been explored.  I
                  ;; didn't originally care about this, but later when I added
                  ;; mp_verror support, I wanted to be able to trick the HID
                  ;; following code into leaving certain HIDs (namely those
                  ;; that include the $core hack) alone.  See xf-mpverror.lisp
                  ;; for more details.
                  (mv warnings x))
                 ((mv warnings x-prime modname range-resolvedp range localp)
                  (vl-find-hid-module x mod mods modalist toplev warnings))
                 ((unless modname)
                  ;; Any failure will result in a modname of nil.  Just don't
                  ;; change anything, then.
                  (mv warnings x-prime))

                 ((unless range-resolvedp)
                  (mv (cons (make-vl-warning
                             :type :vl-follow-hids-fail
                             :msg "Failed to resolve the range of HID ~a0 in module ~m1"
                             :args (list x (vl-module->name mod)))
                            warnings)
                      x-prime))
                 ;; Else we're ready to make our annotations.

                 (val     (make-vl-atom :guts (make-vl-string :value modname)))
                 (atts    (vl-nonatom->atts x-prime))
                 (atts    (acons "VL_HID_RESOLVED_MODULE_NAME" val atts))
                 (atts    (if localp
                              (acons "VL_HID_LOCAL_P" nil atts)
                            (acons "VL_HID_GLOBAL_P" nil atts)))
                 (atts    (if range-resolvedp
                              (acons "VL_HID_RESOLVED_RANGE_P" nil atts)
                            atts))
                 (atts    (if (and range-resolvedp range)
                              (let* ((atts (acons "VL_HID_RESOLVED_RANGE_LEFT"
                                                  (vl-range->msb range)
                                                  atts))
                                     (atts (acons "VL_HID_RESOLVED_RANGE_RIGHT"
                                                  (vl-range->lsb range)
                                                  atts)))
                                atts)
                            atts))
                 (x-prime (change-vl-nonatom x-prime :atts atts)))
                (mv warnings x-prime)))

           ((vl-fast-atom-p x)
            (mv warnings x))

           (t
            (b* ((args (vl-nonatom->args x))
                 ((mv warnings args-prime)
                  (vl-exprlist-follow-hids args mod mods modalist toplev warnings)))
                (mv warnings (change-vl-nonatom x :args args-prime))))))

   (defund vl-exprlist-follow-hids (x mod mods modalist toplev warnings)
     "Returns (MV WARNINGS X-PRIME)"
     (declare (xargs :guard (and (vl-exprlist-p x)
                                 (vl-module-p mod)
                                 (vl-modulelist-p mods)
                                 (equal modalist (vl-modalist mods))
                                 (equal toplev (vl-modulelist-toplevel mods))
                                 (vl-warninglist-p warnings))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         (mv warnings nil)
       (b* (((mv warnings car-prime) (vl-expr-follow-hids (car x) mod mods modalist
                                                          toplev warnings))
            ((mv warnings cdr-prime) (vl-exprlist-follow-hids (cdr x) mod mods modalist
                                                              toplev warnings)))
           (mv warnings (cons car-prime cdr-prime))))))


  (defthm vl-exprlist-follow-hids-when-not-consp
    (implies (not (consp x))
             (equal (vl-exprlist-follow-hids x mod mods modalist toplev warnings)
                    (mv warnings nil)))
    :hints(("Goal" :in-theory (enable vl-exprlist-follow-hids))))

  (defthm vl-exprlist-follow-hids-when-of-cons
    (equal (vl-exprlist-follow-hids (cons a x) mod mods modalist toplev warnings)
           (b* (((mv warnings car-prime) (vl-expr-follow-hids a mod mods modalist toplev warnings))
                ((mv warnings cdr-prime) (vl-exprlist-follow-hids x mod mods modalist toplev warnings)))
               (mv warnings (cons car-prime cdr-prime))))
    :hints(("Goal" :in-theory (enable vl-exprlist-follow-hids))))

  (local (defun my-induction (x mod mods modalist toplev warnings)
           (if (atom x)
               (mv warnings nil)
             (b* (((mv warnings &) (vl-expr-follow-hids (car x) mod mods modalist toplev warnings)))
                 (my-induction (cdr x) mod mods modalist toplev warnings)))))

  (defthm len-of-vl-exprlist-follow-hids
    (equal (len (mv-nth 1 (vl-exprlist-follow-hids x mod mods modalist toplev warnings)))
           (len x))
    :hints(("Goal" :induct (my-induction x mod mods modalist toplev warnings))))

  (defthm true-listp-of-vl-exprlist-follow-hids
    (true-listp (mv-nth 1 (vl-exprlist-follow-hids x mod mods modalist toplev warnings)))
    :rule-classes :type-prescription
    :hints(("Goal" :induct (my-induction x mod mods modalist toplev warnings))))

  (FLAG::make-flag vl-flag-expr-follow-hids
                   vl-expr-follow-hids
                   :flag-mapping ((vl-expr-follow-hids . expr)
                                  (vl-exprlist-follow-hids . list)))

  (defthm-vl-flag-expr-follow-hids lemma
    (expr (implies (force (vl-warninglist-p warnings))
                   (vl-warninglist-p (mv-nth 0 (vl-expr-follow-hids x mod mods modalist
                                                                    toplev warnings))))
          :name vl-warninglist-p-of-vl-expr-follow-hids)
    (list (implies (force (vl-warninglist-p warnings))
                   (vl-warninglist-p (mv-nth 0 (vl-exprlist-follow-hids x mod mods modalist
                                                                        toplev warnings))))
          :name vl-warninglist-p-of-vl-exprlist-follow-hids)
    :hints(("Goal"
            :induct (vl-flag-expr-follow-hids flag x mod mods modalist toplev warnings)
            :expand ((vl-expr-follow-hids x mod mods modalist toplev warnings)
                     (vl-exprlist-follow-hids x mod mods modalist toplev warnings)))))

  (defthm-vl-flag-expr-follow-hids lemma
    (expr (implies (and (force (vl-expr-p x))
                        (force (vl-module-p mod))
                        (force (vl-modulelist-p mods))
                        (force (equal modalist (vl-modalist mods))))
                   (vl-expr-p (mv-nth 1 (vl-expr-follow-hids x mod mods modalist
                                                             toplev warnings))))
          :name vl-expr-p-of-vl-expr-follow-hids)
    (list (implies (and (force (vl-exprlist-p x))
                        (force (vl-module-p mod))
                        (force (vl-modulelist-p mods))
                        (force (equal modalist (vl-modalist mods))))
                   (vl-exprlist-p (mv-nth 1 (vl-exprlist-follow-hids x mod mods modalist
                                                                     toplev warnings))))
          :name vl-exprlist-p-of-vl-exprlist-follow-hids)
    :hints(("Goal"
            :induct (vl-flag-expr-follow-hids flag x mod mods modalist toplev warnings)
            :expand ((vl-expr-follow-hids x mod mods modalist toplev warnings)
                     (vl-exprlist-follow-hids x mod mods modalist toplev warnings)))))

  (verify-guards vl-expr-follow-hids))


;; Now we extend this across the modules, stupid stupid.

(defmacro def-vl-follow-hids (name &key type body)
  (let* ((name-s     (symbol-name name))
         (type-s     (symbol-name type))
         (thm-warn-s (cat "VL-WARNINGLIST-P-" name-s))
         (thm-type-s (cat type-s "-OF-" name-s))
         (thm-warn   (intern-in-package-of-symbol thm-warn-s name))
         (thm-type   (intern-in-package-of-symbol thm-type-s name))
         (short (cat "Annotate hierarchical identifiers throughout a @(see " type-s
") with attributes such as @('VL_HID_RESOLVED_MODULE_NAME'), as described in
@(see hid-elim)."))
         (long  (cat "<p><b>Signature:</b> @(call " name-s ") returns
@('(mv warnings x-prime)').</p>")))

  `(defsection ,name
     :parents (hid-elim)
     :short ,short
     :long ,long

     (defund ,name (x mod mods modalist toplev warnings)
       (declare (xargs :guard (and (,type x)
                                   (vl-module-p mod)
                                   (vl-modulelist-p mods)
                                   (equal modalist (vl-modalist mods))
                                   (equal toplev (vl-modulelist-toplevel mods))
                                   (vl-warninglist-p warnings)))
                (ignorable mod mods modalist toplev))
       ,body)

     (local (in-theory (enable ,name)))

     (defthm ,thm-warn
       (implies (force (vl-warninglist-p warnings))
                (vl-warninglist-p (mv-nth 0 (,name x mod mods modalist toplev warnings)))))

     (defthm ,thm-type
       (implies (and (force (,type x))
                     (force (vl-module-p mod))
                     (force (vl-modulelist-p mods))
                     (force (equal modalist (vl-modalist mods))))
                (,type (mv-nth 1 (,name x mod mods modalist toplev warnings)))))
    )))


(defmacro def-vl-follow-hids-list (name &key type element)
  (let* ((name-s     (symbol-name name))
         (type-s     (symbol-name type))
         (thm-warn-s (cat "VL-WARNINGLIST-P-" name-s))
         (thm-type-s (cat type-s "-OF-" name-s))
         (thm-true-s (cat "TRUE-LISTP-OF-" name-s))
         (thm-warn   (intern-in-package-of-symbol thm-warn-s name))
         (thm-type   (intern-in-package-of-symbol thm-type-s name))
         (thm-true   (intern-in-package-of-symbol thm-true-s name))
         (short (cat "Annotate hierarchical identifiers throughout a @(see " type-s
") with attributes such as @('VL_HID_RESOLVED_MODULE_NAME'), as described in
@(see hid-elim)."))
         (long  (cat "<p><b>Signature:</b> @(call " name-s ") returns
@('(mv warnings x-prime)').</p>")))

  `(defsection ,name
     :parents (hid-elim)
     :short ,short
     :long ,long

     (defund ,name (x mod mods modalist toplev warnings)
       (declare (xargs :guard (and (,type x)
                                   (vl-module-p mod)
                                   (vl-modulelist-p mods)
                                   (equal modalist (vl-modalist mods))
                                   (equal toplev (vl-modulelist-toplevel mods))
                                   (vl-warninglist-p warnings))))
       (if (atom x)
           (mv warnings nil)
         (b* (((mv warnings car-prime) (,element (car x) mod mods modalist toplev warnings))
              ((mv warnings cdr-prime) (,name (cdr x) mod mods modalist toplev warnings)))
             (mv warnings (cons car-prime cdr-prime)))))

     (local (in-theory (enable ,name)))

     (defthm ,thm-warn
       (implies (force (vl-warninglist-p warnings))
                (vl-warninglist-p (mv-nth 0 (,name x mod mods modalist toplev warnings)))))

     (defthm ,thm-type
       (implies (and (force (,type x))
                     (force (vl-module-p mod))
                     (force (vl-modulelist-p mods))
                     (force (equal modalist (vl-modalist mods))))
                (,type (mv-nth 1 (,name x mod mods modalist toplev warnings)))))

     (defthm ,thm-true
       (true-listp (mv-nth 1 (,name x mod mods modalist toplev warnings)))
       :rule-classes :type-prescription)
     )))



(def-vl-follow-hids vl-maybe-expr-follow-hids
  :type vl-maybe-expr-p
  :body (if (not x)
            (mv warnings nil)
          (vl-expr-follow-hids x mod mods modalist toplev warnings)))

(def-vl-follow-hids vl-assign-follow-hids
  :type vl-assign-p
  :body (b* (((mv warnings lvalue-prime)
              (vl-expr-follow-hids (vl-assign->lvalue x) mod mods modalist toplev warnings))
             ((mv warnings expr-prime)
              (vl-expr-follow-hids (vl-assign->expr x) mod mods modalist toplev warnings)))
            (mv warnings
                (change-vl-assign x
                                  :lvalue lvalue-prime
                                  :expr expr-prime))))

(def-vl-follow-hids-list vl-assignlist-follow-hids
  :type vl-assignlist-p
  :element vl-assign-follow-hids)


(def-vl-follow-hids vl-plainarg-follow-hids
  :type vl-plainarg-p
  :body (b* ((expr (vl-plainarg->expr x))
             ((when (not expr))
              (mv warnings x))
             ((mv warnings expr-prime)
              (vl-expr-follow-hids expr mod mods modalist toplev warnings)))
            (mv warnings (change-vl-plainarg x :expr expr-prime))))

(def-vl-follow-hids-list vl-plainarglist-follow-hids
  :type vl-plainarglist-p
  :element vl-plainarg-follow-hids)


(def-vl-follow-hids vl-namedarg-follow-hids
  :type vl-namedarg-p
  :body (b* ((expr (vl-namedarg->expr x))
             ((when (not expr))
              (mv warnings x))
             ((mv warnings expr-prime)
              (vl-expr-follow-hids expr mod mods modalist toplev warnings)))
            (mv warnings (change-vl-namedarg x :expr expr-prime))))

(def-vl-follow-hids-list vl-namedarglist-follow-hids
  :type vl-namedarglist-p
  :element vl-namedarg-follow-hids)

(def-vl-follow-hids vl-arguments-follow-hids
  :type vl-arguments-p
  :body (b* ((namedp (vl-arguments->namedp x))
             (args   (vl-arguments->args x))
             ((mv warnings args-prime)
              (if (vl-arguments->namedp x)
                  (vl-namedarglist-follow-hids args mod mods modalist toplev warnings)
                (vl-plainarglist-follow-hids args mod mods modalist toplev warnings))))
            (mv warnings (vl-arguments namedp args-prime))))

(def-vl-follow-hids vl-modinst-follow-hids
  :type vl-modinst-p
  :body (b* (((mv warnings args-prime)
              (vl-arguments-follow-hids (vl-modinst->portargs x)
                                        mod mods modalist toplev warnings)))
            (mv warnings (change-vl-modinst x :portargs args-prime))))

(def-vl-follow-hids-list vl-modinstlist-follow-hids
  :type vl-modinstlist-p
  :element vl-modinst-follow-hids)

(def-vl-follow-hids vl-gateinst-follow-hids
  :type vl-gateinst-p
  :body (b* (((mv warnings args-prime)
              (vl-plainarglist-follow-hids (vl-gateinst->args x)
                                           mod mods modalist toplev warnings)))
            (mv warnings (change-vl-gateinst x :args args-prime))))

(def-vl-follow-hids-list vl-gateinstlist-follow-hids
  :type vl-gateinstlist-p
  :element vl-gateinst-follow-hids)

(def-vl-follow-hids vl-delaycontrol-follow-hids
  :type vl-delaycontrol-p
  :body (b* (((mv warnings value-prime)
              (vl-expr-follow-hids (vl-delaycontrol->value x)
                                   mod mods modalist toplev warnings)))
            (mv warnings (change-vl-delaycontrol x :value value-prime))))

(def-vl-follow-hids vl-evatom-follow-hids
  :type vl-evatom-p
  :body (b* (((mv warnings expr-prime)
              (vl-expr-follow-hids (vl-evatom->expr x)
                                   mod mods modalist toplev warnings)))
            (mv warnings (change-vl-evatom x :expr expr-prime))))

(def-vl-follow-hids-list vl-evatomlist-follow-hids
  :type vl-evatomlist-p
  :element vl-evatom-follow-hids)

(def-vl-follow-hids vl-eventcontrol-follow-hids
  :type vl-eventcontrol-p
  :body (b* (((mv warnings atoms-prime)
              (vl-evatomlist-follow-hids (vl-eventcontrol->atoms x)
                                         mod mods modalist toplev warnings)))
            (mv warnings (change-vl-eventcontrol x :atoms atoms-prime))))

(def-vl-follow-hids vl-repeateventcontrol-follow-hids
  :type vl-repeateventcontrol-p
  :body (b* (((mv warnings expr-prime)
              (vl-expr-follow-hids (vl-repeateventcontrol->expr x)
                                   mod mods modalist toplev warnings))
             ((mv warnings ctrl-prime)
              (vl-eventcontrol-follow-hids (vl-repeateventcontrol->ctrl x)
                                           mod mods modalist toplev warnings))
             (x-prime (change-vl-repeateventcontrol x
                                                    :expr expr-prime
                                                    :ctrl ctrl-prime)))
            (mv warnings x-prime)))

(encapsulate
 ()
 (local (in-theory (disable vl-delayoreventcontrol-p-when-vl-maybe-delayoreventcontrol-p)))
 (def-vl-follow-hids vl-delayoreventcontrol-follow-hids
   :type vl-delayoreventcontrol-p
   :body (case (tag x)
           (:vl-delaycontrol
            (vl-delaycontrol-follow-hids x mod mods modalist toplev warnings))
           (:vl-eventcontrol
            (vl-eventcontrol-follow-hids x mod mods modalist toplev warnings))
           (:vl-repeat-eventcontrol
            (vl-repeateventcontrol-follow-hids x mod mods modalist toplev warnings))
           (otherwise
            (mv (er hard 'vl-delayoreventcontrol-follow-hids
                    "Impossible case.  This is not really an error.  We are just ~
                     using the guard mechanism to prove that all cases have been ~
                     covered.")
                x)))))

(def-vl-follow-hids vl-maybe-delayoreventcontrol-follow-hids
  :type vl-maybe-delayoreventcontrol-p
  :body (if x
            (vl-delayoreventcontrol-follow-hids x mod mods modalist toplev warnings)
          (mv warnings nil)))

(defthm vl-maybe-delayoreventcontrol-follow-hids-under-iff
  (implies (and (force (vl-maybe-delayoreventcontrol-p x))
                (force (vl-module-p mod))
                (force (vl-modulelist-p mods))
                (force (equal modalist (vl-modalist mods))))
           (iff (mv-nth 1 (vl-maybe-delayoreventcontrol-follow-hids
                           x mod mods modalist toplev warnings))
                x))
  :hints(("Goal"
          :in-theory (e/d (vl-maybe-delayoreventcontrol-follow-hids
                           vl-maybe-delayoreventcontrol-p)
                          (vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-follow-hids))
          :use ((:instance vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-follow-hids)))))


(def-vl-follow-hids vl-nullstmt-follow-hids
  :type vl-nullstmt-p
  :body (mv warnings x))

(def-vl-follow-hids vl-assignstmt-follow-hids
  :type vl-assignstmt-p
  :body (b* (((mv warnings lvalue-prime)
              (vl-expr-follow-hids (vl-assignstmt->lvalue x)
                                   mod mods modalist toplev warnings))
             ((mv warnings expr-prime)
              (vl-expr-follow-hids (vl-assignstmt->expr x)
                                   mod mods modalist toplev warnings))
             ((mv warnings ctrl-prime)
              (vl-maybe-delayoreventcontrol-follow-hids (vl-assignstmt->ctrl x)
                                                        mod mods modalist toplev
                                                        warnings))
             (x-prime
              (change-vl-assignstmt x
                                    :lvalue lvalue-prime
                                    :expr expr-prime
                                    :ctrl ctrl-prime)))
            (mv warnings x-prime)))

(def-vl-follow-hids vl-deassignstmt-follow-hids
  :type vl-deassignstmt-p
  :body (b* (((mv warnings lvalue-prime)
              (vl-expr-follow-hids (vl-deassignstmt->lvalue x)
                                   mod mods modalist toplev warnings))
             (x-prime
              (change-vl-deassignstmt x :lvalue lvalue-prime)))
            (mv warnings x-prime)))

(def-vl-follow-hids vl-enablestmt-follow-hids
  :type vl-enablestmt-p
  :body (b* (((mv warnings id-prime)
              (vl-expr-follow-hids (vl-enablestmt->id x)
                                   mod mods modalist toplev warnings))
             ((mv warnings args-prime)
              (vl-exprlist-follow-hids (vl-enablestmt->args x)
                                       mod mods modalist toplev warnings))
             (x-prime
              (change-vl-enablestmt x
                                    :id id-prime
                                    :args args-prime)))
            (mv warnings x-prime)))

(def-vl-follow-hids vl-disablestmt-follow-hids
  :type vl-disablestmt-p
  :body (b* (((mv warnings id-prime)
              (vl-expr-follow-hids (vl-disablestmt->id x)
                                   mod mods modalist toplev warnings))
             (x-prime
              (change-vl-disablestmt x :id id-prime)))
            (mv warnings x-prime)))

(def-vl-follow-hids vl-eventtriggerstmt-follow-hids
  :type vl-eventtriggerstmt-p
  :body (b* (((mv warnings id-prime)
              (vl-expr-follow-hids (vl-eventtriggerstmt->id x)
                                   mod mods modalist toplev warnings))
             (x-prime
              (change-vl-eventtriggerstmt x :id id-prime)))
            (mv warnings x-prime)))

(def-vl-follow-hids vl-atomicstmt-follow-hids
  :type vl-atomicstmt-p
  :body (case (tag x)
          (:vl-nullstmt         (vl-nullstmt-follow-hids     x mod mods modalist toplev warnings))
          (:vl-assignstmt       (vl-assignstmt-follow-hids   x mod mods modalist toplev warnings))
          (:vl-deassignstmt     (vl-deassignstmt-follow-hids x mod mods modalist toplev warnings))
          (:vl-enablestmt       (vl-enablestmt-follow-hids   x mod mods modalist toplev warnings))
          (:vl-disablestmt      (vl-disablestmt-follow-hids  x mod mods modalist toplev warnings))
          (:vl-eventtriggerstmt (vl-eventtriggerstmt-follow-hids x mod mods modalist
                                                                 toplev warnings))
          (otherwise
           (mv (er hard 'vl-atomicstmt-follow-hids
                   "Impossible case.   This is not really an error.  We are just ~
                    using the guard mechanism to prove that all cases have been ~
                    covered.")
               x))))

(defsection vl-stmt-follow-hids

  (mutual-recursion

   (defund vl-stmt-follow-hids (x mod mods modalist toplev warnings)
     (declare (xargs :guard (and (vl-stmt-p x)
                                 (vl-module-p mod)
                                 (vl-modulelist-p mods)
                                 (equal modalist (vl-modalist mods))
                                 (equal toplev (vl-modulelist-toplevel mods))
                                 (vl-warninglist-p warnings))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (if (vl-fast-atomicstmt-p x)
         (vl-atomicstmt-follow-hids x mod mods modalist toplev warnings)
       (b* (((mv warnings exprs-prime)
             (vl-exprlist-follow-hids (vl-compoundstmt->exprs x)
                                      mod mods modalist toplev warnings))
            ((mv warnings stmts-prime)
             (vl-stmtlist-follow-hids (vl-compoundstmt->stmts x)
                                      mod mods modalist toplev warnings))
            ((mv warnings ctrl-prime)
             (vl-maybe-delayoreventcontrol-follow-hids (vl-compoundstmt->ctrl x)
                                                       mod mods modalist toplev warnings))
            (x-prime
             (change-vl-compoundstmt x
                                     :exprs exprs-prime
                                     :stmts stmts-prime
                                     :ctrl ctrl-prime)))
           (mv warnings x-prime))))

   (defund vl-stmtlist-follow-hids (x mod mods modalist toplev warnings)
     (declare (xargs :guard (and (vl-stmtlist-p x)
                                 (vl-module-p mod)
                                 (vl-modulelist-p mods)
                                 (equal modalist (vl-modalist mods))
                                 (equal toplev (vl-modulelist-toplevel mods))
                                 (vl-warninglist-p warnings))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         (mv warnings nil)
       (b* (((mv warnings car-prime) (vl-stmt-follow-hids (car x) mod mods modalist
                                                          toplev warnings))
            ((mv warnings cdr-prime) (vl-stmtlist-follow-hids (cdr x) mod mods modalist
                                                              toplev warnings)))
           (mv warnings (cons car-prime cdr-prime))))))

  (FLAG::make-flag vl-flag-stmt-follow-hids
                   vl-stmt-follow-hids
                   :flag-mapping ((vl-stmt-follow-hids . stmt)
                                  (vl-stmtlist-follow-hids . list)))

  (defthm-vl-flag-stmt-follow-hids lemma
    (stmt (implies (force (vl-warninglist-p warnings))
                   (vl-warninglist-p (mv-nth 0 (vl-stmt-follow-hids
                                                x mod mods modalist toplev warnings))))
          :name vl-warninglist-p-of-vl-stmt-follow-hids)
    (list (implies (force (vl-warninglist-p warnings))
                   (vl-warninglist-p (mv-nth 0 (vl-stmtlist-follow-hids
                                                x mod mods modalist toplev warnings))))
          :name vl-warninglist-p-of-vl-stmtlist-follow-hids)
    :hints(("Goal"
            :induct (vl-flag-stmt-follow-hids flag x mod mods modalist toplev warnings)
            :expand ((vl-stmt-follow-hids x mod mods modalist toplev warnings)
                     (vl-stmtlist-follow-hids x mod mods modalist toplev warnings)))))

  (defthm vl-stmtlist-follow-hids-when-not-consp
    (implies (not (consp x))
             (equal (vl-stmtlist-follow-hids x mod mods modalist toplev warnings)
                    (mv warnings nil)))
    :hints(("Goal" :in-theory (enable vl-stmtlist-follow-hids))))

  (defthm vl-stmtlist-follow-hids-of-cons
    (equal (vl-stmtlist-follow-hids (cons a x) mod mods modalist toplev warnings)
           (b* (((mv warnings car-prime) (vl-stmt-follow-hids a mod mods modalist toplev warnings))
                ((mv warnings cdr-prime) (vl-stmtlist-follow-hids x mod mods modalist toplev warnings)))
               (mv warnings (cons car-prime cdr-prime))))
    :hints(("Goal" :in-theory (enable vl-stmtlist-follow-hids))))

  (local (defun my-induction (x mod mods modalist toplev warnings)
           (if (atom x)
               (mv warnings x)
             (b* (((mv warnings car-prime)
                   (vl-stmt-follow-hids (car x) mod mods modalist toplev warnings))
                  ((mv warnings cdr-prime)
                   (my-induction (cdr x) mod mods modalist toplev warnings)))
                 (mv warnings (cons car-prime cdr-prime))))))

  (defthm len-of-vl-stmtlist-follow-hids
    (equal (len (mv-nth 1 (vl-stmtlist-follow-hids x mod mods modalist toplev warnings)))
           (len x))
    :hints(("Goal" :induct (my-induction x mod mods modalist toplev warnings))))

  (defthm-vl-flag-stmt-follow-hids lemma
    (stmt (implies (and (force (vl-stmt-p x))
                        (force (vl-module-p mod))
                        (force (vl-modulelist-p mods))
                        (force (equal modalist (vl-modalist mods))))
                   (vl-stmt-p (mv-nth 1 (vl-stmt-follow-hids x mod mods modalist
                                                             toplev warnings))))
          :name vl-stmt-p-of-vl-stmt-follow-hids)
    (list (implies (and (force (vl-stmtlist-p x))
                        (force (vl-module-p mod))
                        (force (vl-modulelist-p mods))
                        (force (equal modalist (vl-modalist mods))))
                   (vl-stmtlist-p (mv-nth 1 (vl-stmtlist-follow-hids x mod mods modalist
                                                                   toplev warnings))))
          :name vl-stmtlist-p-of-vl-stmtlist-follow-hids)
    :hints(("Goal"
            :induct (vl-flag-stmt-follow-hids flag x mod mods modalist toplev warnings)
            :expand ((vl-stmt-follow-hids x mod mods modalist toplev warnings)
                     (vl-stmtlist-follow-hids x mod mods modalist toplev warnings)))))

  (verify-guards vl-stmt-follow-hids))

(def-vl-follow-hids vl-always-follow-hids
  :type vl-always-p
  :body (b* (((mv warnings stmt-prime)
              (vl-stmt-follow-hids (vl-always->stmt x)
                                   mod mods modalist toplev warnings))
             (x-prime
              (change-vl-always x :stmt stmt-prime)))
            (mv warnings x-prime)))

(def-vl-follow-hids-list vl-alwayslist-follow-hids
  :type vl-alwayslist-p
  :element vl-always-follow-hids)

(def-vl-follow-hids vl-initial-follow-hids
  :type vl-initial-p
  :body (b* (((mv warnings stmt-prime)
              (vl-stmt-follow-hids (vl-initial->stmt x)
                                   mod mods modalist toplev warnings))
             (x-prime
              (change-vl-initial x :stmt stmt-prime)))
            (mv warnings x-prime)))

(def-vl-follow-hids-list vl-initiallist-follow-hids
  :type vl-initiallist-p
  :element vl-initial-follow-hids)



(defsection vl-module-follow-hids

  (defund vl-module-follow-hids (x mods modalist toplev)
    (declare (xargs :guard (and (vl-module-p x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods))
                                (equal toplev (vl-modulelist-toplevel mods)))))
    (b* (((when (vl-module->hands-offp x))
          x)
         (warnings (vl-module->warnings x))
         ((mv warnings assigns)
          (vl-assignlist-follow-hids (vl-module->assigns x) x mods modalist toplev warnings))
         ((mv warnings modinsts)
          (vl-modinstlist-follow-hids (vl-module->modinsts x) x mods modalist toplev warnings))
         ((mv warnings gateinsts)
          (vl-gateinstlist-follow-hids (vl-module->gateinsts x) x mods modalist toplev warnings))
         ((mv warnings alwayses)
          (vl-alwayslist-follow-hids (vl-module->alwayses x) x mods modalist toplev warnings))
         ((mv warnings initials)
          (vl-initiallist-follow-hids (vl-module->initials x) x mods modalist toplev warnings)))
        (change-vl-module x
                          :assigns assigns
                          :modinsts modinsts
                          :gateinsts gateinsts
                          :alwayses alwayses
                          :initials initials
                          :warnings warnings)))

  (local (in-theory (enable vl-module-follow-hids)))

  (defthm vl-module-p-of-vl-module-follow-hids
    (implies (and (force (vl-module-p x))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods)))
                  (force (equal toplev (vl-modulelist-toplevel mods))))
             (vl-module-p (vl-module-follow-hids x mods modalist toplev))))

  (defthm vl-module->name-of-vl-module-follow-hids
    (equal (vl-module->name (vl-module-follow-hids x mods modalist toplev))
           (vl-module->name x))))




(defprojection vl-modulelist-follow-hids-aux (x mods modalist toplev)
  (vl-module-follow-hids x mods modalist toplev)
  :guard (and (vl-modulelist-p x)
              (vl-modulelist-p mods)
              (equal modalist (vl-modalist mods))
              (equal toplev (vl-modulelist-toplevel mods)))
  :result-type vl-modulelist-p
  :rest
  ((defthm vl-modulelist->names-of-vl-modulelist-follow-hids-aux
     (let ((ret (vl-modulelist-follow-hids-aux x mods modalist toplev)))
       (equal (vl-modulelist->names ret)
              (vl-modulelist->names x))))))


(defsection vl-modulelist-follow-hids

  (defund vl-modulelist-follow-hids (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (b* ((modalist (vl-modalist x))
         (toplev   (vl-modulelist-toplevel x))
         (x-prime  (vl-modulelist-follow-hids-aux x x modalist toplev))
         (-        (flush-hons-get-hash-table-link modalist)))
        x-prime))

  (local (in-theory (enable vl-modulelist-follow-hids)))

  (defthm vl-modulelist-p-of-vl-modulelist-follow-hids
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-follow-hids x))))

  (defthm vl-modulelist->names-of-vl-modulelist-follow-hids
    (equal (vl-modulelist->names (vl-modulelist-follow-hids x))
           (vl-modulelist->names x))))

