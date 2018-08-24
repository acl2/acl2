; Basic Bind Support for VL
; Copyright (C) 2016 Apple, Inc.
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
; Original author: Jared Davis

(in-package "VL")
(include-book "../../mlib/scopestack")
(include-book "../../mlib/reportcard")
(include-book "../../mlib/filter")
(include-book "../../mlib/expr-tools")
(local (include-book "../../util/arithmetic"))
(local (include-book "../../util/osets"))
(local (std::add-default-post-define-hook :fix))

(defsection basic-bind-elim
  :parents (annotate)
  :short "Handling of basic SystemVerilog @('bind') constructs."

  :long "<p>See SystemVerilog-2012 23.11, <i>Binding auxiliary code to scopes
or instances</i>.  Bind constructs allow you to essentially inject module
instances into other modules at run-time.</p>

<p>This transform, as part of the initial @(see annotate) process, is meant to
handle ``global'' (our word) @('bind') statements&mdash;those that add code to
whole modules/interfaces&mdash;but not (most) ``local'' binds that tamper with
a particular module instance.  For instance:</p>

@({
     module wheelChecker (...); ... endmodule

     module beetle (...); ... endmodule
     module transAm (...); ... endmodule

     module top ;

        beetle herbie1(...);
        beetle herbie2(...);

        transAm kit();
        transAm kat();

        // This is a 'global' bind because it affects all beetles
        // We support this here.
        bind beetle wheelChecker frontWheelCheck(...);

        // This is a 'local' bind because it only affects kit and not kat.
        // We don't support these kinds of binds.
        bind transAm: kit wheelChecker frontWheelCheck(...);

     endmodule
})

<p>Global binds are easier (and perhaps more efficient) to support because we
can add them without having to ``fork'' the definitions of modules.  That is,
in the above example, adding the @('wheelChecker') to only @('kit') and not
@('kat') means that we need to fork @('transAm') into two separate modules: one
with the extra binding and one without.  It seems tricky to do this
efficiently.</p>

<p>We actually <i>do</i> support a very limited subset of local binds that may
as well have been global.  That is, if some particular module @('foo') is only
ever instantiated in a single place, then a local bind that adds submodules to
that single instance may as well have been a global bind that adds its
submodules to @('foo').  Note that this is a very limited facility, mainly
intended to support bind statements that are applied to very high-level
modules.</p>

<p>Ordering notes.</p>

<ul>

<li>We should run this after preliminaries like @(see make-implicit-wires) so
that scopes are correct.  We rely on scopes making sense in order to look up
which instances a non-global @('bind') is referring to.</li>

<li>We should run this before @(see argresolve) so that any bindings we
introduce will get resolved as per usual.  We should also run this before @(see
basicsanity) so that we check namespaces correctly and to report unhandled
@('bind') statements easily.</li>

</ul>")

(local (xdoc::set-default-parents basic-bind-elim))

; General Approach ------------------------------------------------------------
;
; Philosophy: It shouldn't our job to handle all bind statements here, just the
; ones that are simple enough (because handling them here will be way more
; efficient than doing it individually, per instance, at elaboration time).
; Some day, handling local binds could become part of elaboration.
;
; On the other hand, practically speaking, for now we're the only bind support
; in VL, so if we run into something we can't handle, we'll go ahead and add
; warnings.
;
; Pass 1: Figure out what we want to do.
;
; In this pass we're going to go through the design and identify which binds we
; support and which we don't.  The supported binds will be global binds, and
; also the limited subset of local binds that we think are safe to process.
;
;  - Supported binds will get removed in this pass.  We set them aside as "bind
;    intents" that basically say, "we want to add xxx to module yyy."  (They
;    have slightly more context than that, but that's the idea.)  We'll apply
;    these intents during the next pass.
;
;  - Unsupported binds will be left alone, unless they're so obviously wrong
;    somehow that we should just issue warnings about them.
;
; Pass 2: Do it.
;
; The result from pass 1 is a table of binds that we now need to apply.  So, we
; need to go through the design and add these to the right places.



; Bind Deltas -----------------------------------------------------------------
;
; The goal of Pass 1 will be to build a bind delta which captures what we
; intend to add to the design.

(deftranssum vl-bindcontext
  :short "Places where a bind statement may occur."
  :long "<p>This is only intended for error reporting / attribute creation.  In
  particular you should not use this to do scope lookups, because you need real
  scopestacks for that.</p>"
  (vl-interface
   vl-module
   vl-design))

(define vl-bindcontext->shortdescription ((x vl-bindcontext-p))
  :parents (vl-bindcontext)
  (b* ((x (vl-bindcontext-fix x)))
    (case (tag x)
      (:vl-interface (cat "interface " (vl-interface->name x)))
      (:vl-module    (cat "module " (vl-module->name x)))
      (:vl-design    "design (top level)")
      (otherwise     (progn$ (impossible) "")))))

(defprod vl-bindintent
  :parents (vl-binddelta)
  :short "An intent to bind additional submodules, and where it comes from."
  ((source  vl-bind-p        "Original @('bind') that led to this.")
   (ctx     vl-bindcontext-p "Where that @('bind') came from."))
  :long "<p>The module we're intending to add these to is not included because
  that will be put in the @(see vl-binddelta).  The module instances we're
  adding are found inside the @('source'), of course.</p>"
  :tag nil
  :layout :tree)

(fty::deflist vl-bindintentlist
  :elt-type vl-bindintent
  :parents (vl-binddelta))

(fty::defalist vl-binddelta
  :key-type stringp
  :val-type vl-bindintentlist-p
  :short "Table that summarizes our intended changes to the design in order to
          process all supported @('bind') statements.")



; Identifying singly instantiated modules -------------------------------------
;
; We want to support local binds that "may as well have been global," by which
; we mean things like:
;
;    bind myinst [insts to add];
;    bind mymod : myinst [insts to add];
;
; when myinst is the only instance of mymod in the entire design.  In that
; case, this may as well have been written as simply:
;
;    bind mymod [insts to add];
;
; Determining if myinst is the only instance of mymod throughout the design
; can be tricky.  One particular wrinkle is things like:
;
;     for(genvar i = 0; i < 10; ++i) begin : foo
;        mymod myinst ...;
;        if (i == 3)
;          bind mymod : myinst [insts to add];
;     endmodule
;
; During annotation (where we expect bindelim to run), we haven't elaborated
; generates, so the above "looks" like a single instance of mymod.  But
; obviously it would be wrong to add these instances to every instance of
; mymod: we should only add them to the instance for i==3.
;
; I think that handling generates correctly here seems so tricky that I don't
; want anything to do with it.  Instead, we'll just say that anything that is
; instantiated inside a generate is off limits.  This is overly restrictive,
; but at least it should be safe.
;
; We also need to be careful to gather up module instances that occur within
; bind statements as well as regular instances, but that's not too hard.
;
; At any rate: the following code allows us to gather up an INSTTABLE structure
; that binds module names to information about all of their instances.  By
; looking at this table, we'll be able to tell whether any particular module is
; only instantiated once, in a safe, generate-free context.

(defprod vl-bindelim-institem
  :tag nil
  :layout :tree
  ((inst  vl-modinst-p     "A module instance we found.")
   (genp  booleanp         "Does this instance occur inside some generate?")
   (bindp booleanp         "Is this an instance from within a bind statement?")
   (ctx   vl-bindcontext-p "Usually: the module where we found the instance.
                            But it could also be, e.g., the top level design,
                            if this instance is within a top-level bind.")))

(fty::deflist vl-bindelim-institemlist :elt-type vl-bindelim-institem)

(fty::defalist vl-bindelim-insttable
  :key-type stringp
  :val-type vl-bindelim-institemlist-p
  :short "Table associating module names to all the instances of that module
          and where they occur.")

(define vl-bindelim-extend-insttable ((x     vl-modinstlist-p)
                                      (ctx   vl-bindcontext-p)
                                      (genp  booleanp)
                                      (bindp booleanp)
                                      (itbl  vl-bindelim-insttable-p))
  :returns (new-itbl vl-bindelim-insttable-p)
  :measure (len x)
  :parents (vl-bindelim-insttable)
  :short "Straightforward extension of the @(see vl-bindelim-insttable) with
          a bunch of instances from some context."
  (b* ((x    (vl-modinstlist-fix x))
       (itbl (vl-bindelim-insttable-fix itbl))
       ((when (atom x))
        itbl)
       ((vl-modinst inst1) (first x))
       (item       (make-vl-bindelim-institem :ctx ctx
                                              :inst inst1
                                              :genp genp
                                              :bindp bindp))
       (prev-items (cdr (hons-get inst1.modname itbl)))
       (new-items  (cons item prev-items))
       (itbl       (hons-acons inst1.modname new-items itbl)))
    (vl-bindelim-extend-insttable (rest x) ctx genp bindp itbl)))

(def-genblob-transform vl-genblob-bindelim-insttable ((ctx   vl-bindcontext-p)
                                                      (genp  booleanp)
                                                      (itbl  vl-bindelim-insttable-p))
  :returns ((itbl vl-bindelim-insttable-p))
  :parents (vl-bindelim-insttable)
  :short "Main function to recursively collect up the @(see vl-bindelim-insttable)
          from a module/interface/generate block.  Recursively goes into generates."
  (b* (((vl-genblob x) (vl-genblob-fix x))
       ;; Add the plain old module instances.
       (itbl (vl-bindelim-extend-insttable x.modinsts ctx
                                           genp ;; Transitively in a generate?
                                           nil  ;; Not from bind statements
                                           itbl))
       ;; Add the module instances from bind statements
       (bind-insts (vl-bindlist->modinsts x.binds))
       (itbl (vl-bindelim-extend-insttable bind-insts ctx
                                           genp ;; Transitively in a generate?
                                           t    ;; Yes from bind statements
                                           itbl))
       ;; Recursively process any sub-generates
       (itbl (vl-generates-bindelim-insttable x.generates ctx
                                              t ;; Yes within generates
                                              itbl)))
    itbl)
  :apply-to-generates vl-generates-bindelim-insttable
  :no-new-x t)

(define vl-module-bindelim-insttable ((x    vl-module-p)
                                      (itbl vl-bindelim-insttable-p))
  :returns (itbl vl-bindelim-insttable-p)
  (b* ((x (vl-module-fix x)))
    (vl-genblob-bindelim-insttable (vl-module->genblob x)
                                   x   ;; These instances come from X
                                   nil ;; They are not in a generate yet
                                   itbl)))

(define vl-modulelist-bindelim-insttable ((x    vl-modulelist-p)
                                          (itbl vl-bindelim-insttable-p))
  :returns (itbl vl-bindelim-insttable-p)
  (b* ((itbl (vl-bindelim-insttable-fix itbl))
       ((when (atom x))
        itbl)
       (itbl (vl-module-bindelim-insttable (first x) itbl)))
    (vl-modulelist-bindelim-insttable (rest x) itbl)))

(define vl-interface-bindelim-insttable ((x    vl-interface-p)
                                         (itbl vl-bindelim-insttable-p))
  :returns (itbl vl-bindelim-insttable-p)
  (b* ((x (vl-interface-fix x)))
    (vl-genblob-bindelim-insttable (vl-interface->genblob x)
                                   x   ;; These instances come from X
                                   nil ;; They are not in a generate yet
                                   itbl)))

(define vl-interfacelist-bindelim-insttable ((x    vl-interfacelist-p)
                                             (itbl vl-bindelim-insttable-p))
  :returns (itbl vl-bindelim-insttable-p)
  (b* ((itbl (vl-bindelim-insttable-fix itbl))
       ((when (atom x))
        itbl)
       (itbl (vl-interface-bindelim-insttable (first x) itbl)))
    (vl-interfacelist-bindelim-insttable (rest x) itbl)))

(define vl-bindelim-create-insttable ((x vl-design-p))
  :returns (itbl vl-bindelim-insttable-p)
  :parents (vl-bindelim-insttable)
  :short "Create a @(see vl-bindelim-insttable) that summarizes the module
          instances throughout the entire design."
  (b* (((vl-design x) (vl-design-fix x))
       (itbl
        ;; Size hint.  We're binding, e.g., module names to these modules.
        ;; For typical designs this should be about right:
        (+ (len x.mods) (len x.interfaces)))
       (itbl (vl-modulelist-bindelim-insttable x.mods itbl))
       (itbl (vl-interfacelist-bindelim-insttable x.interfaces itbl))
       ;; Also grab instances from top level binds.
       (bind-insts (vl-bindlist->modinsts x.binds))
       (itbl (vl-bindelim-extend-insttable bind-insts x
                                          nil ;; Not from generates
                                          t   ;; Yes from bind statements
                                          itbl)))
    ;; We don't bother to fast-alist-clean the table, because we don't
    ;; intend to ever iterate down it.
    itbl))

(define vl-bindelim-find-global-target ((x        vl-bind-p)
                                        (itbl     vl-bindelim-insttable-p)
                                        (ss       vl-scopestack-p)
                                        (warnings vl-warninglist-p))
  ;; With our instance table in place, we can now recognize bind statements
  ;; that are local but may as well be global.  This is tricky and can fail in
  ;; a lot of ways, so generating warnings to be able to debug it seems like a
  ;; good idea.
  :returns (mv (name maybe-stringp :rule-classes :type-prescription)
               (warnings vl-warninglist-p))
  :guard-hints (("Goal" :in-theory (enable tag-reasoning)))
  (b* ((itbl (vl-bindelim-insttable-fix itbl))
       ((vl-bind x) (vl-bind-fix x))

       ((when (and x.scope (atom x.addto)))
        ;; This is just a perfectly good, syntactically global bind.  Note
        ;; that we don't bother to check whether the scope is defined: we'll
        ;; handle problems there when we actually try to add the instances.
        (mv x.scope (ok)))

       ((unless (consp x.addto))
        (mv (raise "Programming error -- scopeless bind should always have addto: ~x0" x)
            (ok)))

       ;; Not a global binding, but maybe simple enough to support.
       ((unless (atom (cdr x.addto)))
        ;; Something like bind mymod : foo, bar, baz  [..insts to add..]
        ;; This seems hard to support.
        (mv nil
            ;; Eventually this should not be fatal
            (fatal :type :vl-bindelim-fail
                   :msg "~a0: bind statement isn't supported (multiple instances, ~
                         not sure if it's global.)"
                   :args (list x))))
       (addto (first x.addto))

       ;; Looking good -- addto is a single expression.  We could do a lot to
       ;; try to support hierarchical paths, etc., but I think it's probably
       ;; best to try to keep this really simple, to avoid any possibility that
       ;; we're going through generates, etc.
       ((unless (vl-idexpr-p addto))
        (mv nil
            ;; Eventually this should not be fatal
            (fatal :type :vl-bindelim-fail
                  :msg "~a0: bind statement isn't supported because the ~
                        add-to expression, ~a1, isn't just an identifier."
                  :args (list x addto))))

       (target-inst (vl-scopestack-find-item (vl-idexpr->name addto) ss))
       ((unless (mbe :logic (vl-modinst-p target-inst)
                     :exec (eq (tag target-inst) :vl-modinst)))
        (mv nil
            (fatal :type :vl-bad-bind
                   :msg "~a0: trying to add instances to ~a1, which isn't ~
                         a module instance.  (~a2)"
                   :args (list x addto (tag target-inst)))))
       ((vl-modinst target-inst))
       ((when (and x.scope
                   (not (equal x.scope target-inst.modname))))
        (mv nil
            (fatal :type :vl-bad-bind
                   :msg "~a0: bind statement says that ~a1 is an ~
                         instance of ~a2, but actually it is an ~
                         instance of ~a3."
                   :args (list x addto x.scope target-inst.modname))))

       ;; OK -- found the desired instance and it's the right type.  Let's
       ;; see if it's really the only instance of this module.
       (inst-infos (cdr (hons-get target-inst.modname itbl)))
       ((unless (consp inst-infos))
        (mv (raise "Programming error -- the bindelim insttable says ~
                    there are no instance of ~x0, but we found one: ~x1. ~
                    How can this be?" target-inst.modname target-inst)
            (ok)))

       ((unless (atom (cdr inst-infos)))
        (mv nil
            ;; Eventually this should not be fatal
            (fatal :type :vl-bindelim-fail
                   :msg "~a0: bind statement isn't supported because there ~
                         are multiple instances of ~s1 in the design, ~
                         including at least at ~a2 and ~a3."
                   :args (list x target-inst.modname
                               (vl-modinst->loc (vl-bindelim-institem->inst (first inst-infos)))
                               (vl-modinst->loc (vl-bindelim-institem->inst (second inst-infos)))))))

       ((vl-bindelim-institem info1) (car inst-infos))
       ((unless (equal info1.inst target-inst))
        ;; Good sanity check
        (mv (raise "Programming error -- the bindelim insttable says ~
                    there's exactly one instance of ~x0, but we found ~x1 ~
                    and it's different than ~x2."
                   target-inst.modname target-inst info1)
            (ok)))
       ((when info1.genp)
        (mv nil
            ;; Eventually this should not be fatal
            (fatal :type :vl-bindelim-fail
                   :msg "~a0: bind statement isn't supported because it ~
                         refers to an instance that is inside a generate ~
                         block, so we aren't sure this is a globally unique ~
                         instance."
                   :args (list x)))))

    ;; Otherwise, after all of that, it looks like we've found a truly unique
    ;; global instance of this module, that doesn't occur within a generate
    ;; block, so treat it as global.  Whew, that was a lot harder than I
    ;; expected...
    (mv target-inst.modname (ok))))

; Pass 1: collect all the binds -----------------------------------------------
;
; Our vl-bindelim-find-global-target function above gives us a nice, simple way
; to determine if a bind is supported and targets a global module.  Now we need
; to go ahead and apply this to all the binds in the design.  Binds can occur
; in many places, but this is a pretty straightforward genblob transform.

(define vl-bindelim-main
  ((x        vl-bind-p               "A single @('bind') to process.")
   (ss       vl-scopestack-p         "Scopestack where @('x') occurs.")
   (ctx      vl-bindcontext-p        "Where @('x') occurs, for error messages.")
   (itbl     vl-bindelim-insttable-p "For identifying local binds that we can handle.")
   (delta    vl-binddelta-p          "The changes we're building.")
   (genp     booleanp                "Are we in a generate?")
   (warnings vl-warninglist-p        "For collecting warnings about unsupported binds."))
  :returns
  (mv (warnings vl-warninglist-p)
      (new-x    vl-bindlist-p
                "A list of binds to replace X.  This will be NIL when x is a
                 supported bind that has been converted into an intent and
                 added to the delta.  It will be @('(list x)') if it isn't
                 supported.")
      (delta    vl-binddelta-p "Extended delta to apply in Pass 2."))
  (b* ((x     (vl-bind-fix x))
       (delta (vl-binddelta-fix delta))
       ((mv modname warnings)
        (vl-bindelim-find-global-target x itbl ss warnings))
       ((unless modname)
        ;; We already added a warning explaining why this isn't supported, but
        ;; at any rate, leave it alone.
        (mv warnings (list x) delta))
       ((when genp)
        ;; Eventually this should not be fatal.
        (mv (fatal :type :vl-bindelim-fail
                   :msg "~a0: bind statements within generates are not yet supported."
                   :args (list x))
            (list x) delta))
       ;; This may as well be a global bind: turn it into a bindintent and
       ;; add it to the delta.
       (intent      (make-vl-bindintent :source x :ctx ctx))
       (old-intents (cdr (hons-get modname delta)))
       (new-intents (cons intent old-intents))
       (delta       (hons-acons modname new-intents delta)))
    (mv warnings nil delta)))

(define vl-bindelim-bindlist
  ((x        vl-bindlist-p           "List of binds to process.")
   (ss       vl-scopestack-p         "Scopestack where @('x') occurs.")
   (ctx      vl-bindcontext-p        "Where @('x') occurs, for error messages.")
   (itbl     vl-bindelim-insttable-p "For identifying local binds that we can handle.")
   (delta    vl-binddelta-p          "The changes we're building.")
   (genp     booleanp                "Are we inside a generate?")
   (warnings vl-warninglist-p        "For collecting warnings about unsupported binds."))
  :returns
  (mv (warnings vl-warninglist-p)
      (new-x    vl-bindlist-p
                "A list of binds to replace X.  Essentially this contains
                 any unsupported binds.")
      (delta    vl-binddelta-p "Extended delta to apply in Pass 2."))
  (b* (((when (atom x))
        (mv (ok) nil (vl-binddelta-fix delta)))
       ((mv warnings x1 delta)
        (vl-bindelim-main (car x) ss ctx itbl delta genp warnings))
       ((mv warnings xrest delta)
        (vl-bindelim-bindlist (cdr x) ss ctx itbl delta genp warnings)))
    (mv warnings (append-without-guard x1 xrest) delta)))

(def-genblob-transform vl-genblob-bindelim ((ss       vl-scopestack-p)
                                            (ctx      vl-bindcontext-p)
                                            (itbl     vl-bindelim-insttable-p)
                                            (delta    vl-binddelta-p)
                                            (genp     booleanp "Are we in a generate?")
                                            (warnings vl-warninglist-p))
  :returns ((warnings vl-warninglist-p)
            (delta    vl-binddelta-p))
  (b* (((vl-genblob x) (vl-genblob-fix x))
       (ss (vl-scopestack-push x ss))
       ((mv warnings new-binds delta)
        (vl-bindelim-bindlist x.binds ss ctx itbl delta genp warnings))
       ((mv warnings delta new-generates)
        (vl-generates-bindelim x.generates ss ctx itbl delta
                               t ;; Yes, these are in a generate
                               warnings)))
    (mv warnings delta
        (change-vl-genblob x
                           :binds new-binds
                           :generates new-generates)))
  :apply-to-generates vl-generates-bindelim)

(define vl-module-bindelim ((x     vl-module-p)
                            (ss    vl-scopestack-p)
                            (itbl  vl-bindelim-insttable-p)
                            (delta vl-binddelta-p))
  :returns (mv (new-x vl-module-p)
               (delta vl-binddelta-p))
  (b* (((vl-module x) (vl-module-fix x))
       (blob (vl-module->genblob x))
       ((mv warnings delta new-blob)
        (vl-genblob-bindelim blob ss x itbl delta
                             nil ;; Not yet in a generate
                             x.warnings))
       (new-x (change-vl-module (vl-genblob->module new-blob x)
                                :warnings warnings)))
    (mv new-x delta)))

(define vl-modulelist-bindelim ((x     vl-modulelist-p)
                                (ss    vl-scopestack-p)
                                (itbl  vl-bindelim-insttable-p)
                                (delta vl-binddelta-p))
  :returns (mv (new-x vl-modulelist-p)
               (delta vl-binddelta-p))
  (b* (((when (atom x))
        (mv nil (vl-binddelta-fix delta)))
       ((mv x1 delta) (vl-module-bindelim (car x) ss itbl delta))
       ((mv xrest delta) (vl-modulelist-bindelim (cdr x) ss itbl delta)))
    (mv (cons x1 xrest) delta)))

(define vl-interface-bindelim ((x     vl-interface-p)
                               (ss    vl-scopestack-p)
                               (itbl  vl-bindelim-insttable-p)
                               (delta vl-binddelta-p))
  :returns (mv (new-x vl-interface-p)
               (delta vl-binddelta-p))
  (b* (((vl-interface x) (vl-interface-fix x))
       (blob (vl-interface->genblob x))
       ((mv warnings delta new-blob)
        (vl-genblob-bindelim blob ss x itbl delta
                             nil ;; Not yet in a generate
                             x.warnings))
       (new-x (change-vl-interface (vl-genblob->interface new-blob x)
                                   :warnings warnings)))
    (mv new-x delta)))

(define vl-interfacelist-bindelim ((x     vl-interfacelist-p)
                                   (ss    vl-scopestack-p)
                                   (itbl  vl-bindelim-insttable-p)
                                   (delta vl-binddelta-p))
  :returns (mv (new-x vl-interfacelist-p)
               (delta vl-binddelta-p))
  (b* (((when (atom x))
        (mv nil (vl-binddelta-fix delta)))
       ((mv x1 delta) (vl-interface-bindelim (car x) ss itbl delta))
       ((mv xrest delta) (vl-interfacelist-bindelim (cdr x) ss itbl delta)))
    (mv (cons x1 xrest) delta)))

(define vl-design-bindelim-pass1 ((x vl-design-p))
  :returns (mv (new-x vl-design-p)
               (delta vl-binddelta-p))
  (b* (((vl-design x) (vl-design-fix x))
       (ss    (vl-scopestack-init x))
       (itbl  (vl-bindelim-create-insttable x))
       (delta nil)
       ((mv new-mods delta) (vl-modulelist-bindelim x.mods ss itbl delta))
       ((mv new-ifs  delta) (vl-interfacelist-bindelim x.interfaces ss itbl delta))
       ;; That handles most stuff, but there can also be top-level binds.
       (warnings x.warnings)
       ((mv warnings new-binds delta)
        (vl-bindelim-bindlist x.binds ss x itbl delta
                              nil ;; Not in a generate
                              warnings))
       (new-x (change-vl-design x
                                :mods new-mods
                                :interfaces new-ifs
                                :binds new-binds
                                :warnings warnings))
       (delta (fast-alist-clean delta)))
    (fast-alist-free itbl)
    (mv new-x delta)))


; Pass 2: Apply the binds -----------------------------------------------------

(define vl-bindelim-modinst-add-atts ((x      vl-modinst-p)
                                      (intent vl-bindintent-p))
  :returns (new-x vl-modinst-p)
  (b* (((vl-modinst x))
       ((vl-bindintent intent))
       (val (str::cat "Added by bind statement from "
                      (vl-bindcontext->shortdescription intent.ctx)
                      " at "
                      (vl-location-string (vl-bind->loc intent.source))))
       (atts (cons (cons "VL_FROM_BIND"
                         (make-vl-literal
                          :val (make-vl-string :value val)))
                   x.atts)))
    (change-vl-modinst x :atts atts)))

(define vl-bindelim-modinstlist-add-atts ((x      vl-modinstlist-p)
                                          (intent vl-bindintent-p))
  :returns (new-x vl-modinstlist-p)
  (if (atom x)
      nil
    (cons (vl-bindelim-modinst-add-atts (car x) intent)
          (vl-bindelim-modinstlist-add-atts (cdr x) intent))))

(define vl-bindintent->modinsts ((x vl-bindintent-p))
  :short "Get the modinsts to add to some module that arise from a @(see
          vl-bind), annotated with attributes that say where they came from."
  :returns (insts vl-modinstlist-p)
  (b* (((vl-bindintent x))
       ((vl-bind x.source)))
    (vl-bindelim-modinstlist-add-atts x.source.modinsts x)))

(define vl-bindintentlist->modinsts ((x vl-bindintentlist-p))
  :returns (insts vl-modinstlist-p)
  (if (atom x)
      nil
    (append (vl-bindintent->modinsts (car x))
            (vl-bindintentlist->modinsts (cdr x)))))

(define vl-module-apply-binddelta ((x     vl-module-p)
                                   (delta vl-binddelta-p))
  :returns (new-x vl-module-p)
  (b* (((vl-module x) (vl-module-fix x))
       (delta (vl-binddelta-fix delta))
       (intents (cdr (hons-get x.name delta)))
       ((unless intents)
        ;; No binds to add to this module, so no need to do anything.
        x)
       (new-insts (vl-bindintentlist->modinsts intents)))
    (change-vl-module x
                      :modinsts (append-without-guard x.modinsts new-insts))))

(defprojection vl-modulelist-apply-binddelta ((x vl-modulelist-p)
                                              (delta vl-binddelta-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-apply-binddelta x delta))

(define vl-interface-apply-binddelta ((x     vl-interface-p)
                                   (delta vl-binddelta-p))
  :returns (new-x vl-interface-p)
  (b* (((vl-interface x) (vl-interface-fix x))
       (delta (vl-binddelta-fix delta))
       (intents (cdr (hons-get x.name delta)))
       ((unless intents)
        ;; No binds to add to this interface, so no need to do anything.
        x)
       (new-insts (vl-bindintentlist->modinsts intents)))
    (change-vl-interface x
                      :modinsts (append-without-guard x.modinsts new-insts))))

(defprojection vl-interfacelist-apply-binddelta ((x vl-interfacelist-p)
                                              (delta vl-binddelta-p))
  :returns (new-x vl-interfacelist-p)
  (vl-interface-apply-binddelta x delta))


(define vl-warn-bindintent-undefined ((modname  stringp)
                                      (intent   vl-bindintent-p)
                                      (warnings vl-warninglist-p))
  :returns (warnings vl-warninglist-p)
  (b* (((vl-bindintent intent)))
    (fatal :type :vl-warn-bind-undefined
           :msg "~a0: bind statement targets module ~s1, but this modules ~
                 isn't defined."
           :args (list intent.source (string-fix modname)))))

(define vl-warn-bindintentlist-undefined ((modname  stringp)
                                          (intents  vl-bindintentlist-p)
                                          (warnings vl-warninglist-p))
  :returns (warnings vl-warninglist-p)
  (b* (((when (atom intents))
        (ok))
       (warnings (vl-warn-bindintent-undefined modname (car intents) warnings)))
    (vl-warn-bindintentlist-undefined modname (cdr intents) warnings)))

(define vl-warn-binddelta-undefined ((delta vl-binddelta-p)
                                     (warnings vl-warninglist-p))
  :returns (warnings vl-warninglist-p)
  :measure (len (vl-binddelta-fix delta))
  (b* ((delta (vl-binddelta-fix delta))
       ((when (atom delta))
        (ok))
       ((cons modname intents) (car delta))
       (warnings (vl-warn-bindintentlist-undefined modname intents warnings)))
    (vl-warn-binddelta-undefined (cdr delta) warnings)))

(local (in-theory (e/d (acl2::hons-assoc-equal-iff-member-alist-keys)
                       (acl2::alist-keys-member-hons-assoc-equal))))

(local (defthm string-listp-of-alist-keys-when-vl-binddelta-p
         (implies (vl-binddelta-p delta)
                  (string-listp (alist-keys delta)))
         :hints(("Goal" :induct (len delta)))))

(local (defthm vl-binddelta-p-of-fal-extract
         (implies (and (force (vl-binddelta-p x))
                       (force (subsetp-equal keys (alist-keys x))))
                  (vl-binddelta-p (acl2::fal-extract keys x)))
         :hints(("Goal" :in-theory (enable acl2::fal-extract)))))

(local (defthm l0
         (subsetp-equal (intersection-equal (set-difference-equal a b)
                                            (set-difference-equal a c))
                        a)
         :hints((set-reasoning))))

(define vl-design-bindelim-pass2 ((x     vl-design-p)
                                  (delta vl-binddelta-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) (vl-design-fix x))
       (delta (vl-binddelta-fix delta))
       (new-mods (vl-modulelist-apply-binddelta x.mods delta))
       (new-ifs  (vl-interfacelist-apply-binddelta x.interfaces delta))
       ;; That *should* be everything, but we might have found bind statements
       ;; that apply to modules that aren't even defined.  In that case we
       ;; should at least create a warning.  There's nothing to attach this
       ;; warning to, so we'll just make them floating warnings.
       (ok-names (set::union (set::mergesort (vl-interfacelist->names x.interfaces))
                             (set::mergesort (vl-modulelist->names x.mods))))
       (actual-names (set::mergesort (alist-keys delta)))
       (bad-names (set::difference actual-names ok-names))
       (bad-delta (acl2::fal-extract bad-names delta))
       (warnings (vl-warn-binddelta-undefined bad-delta x.warnings)))
    (fast-alist-free bad-delta)
    (change-vl-design x
                      :mods new-mods
                      :interfaces new-ifs
                      :warnings warnings)))

(define vl-design-bindelim ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((mv x delta) (vl-design-bindelim-pass1 x))
       (x (vl-design-bindelim-pass2 x delta)))
    (fast-alist-free delta)
    x))
