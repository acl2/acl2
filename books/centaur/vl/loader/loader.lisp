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
(include-book "read-file")
(include-book "find-file")
(include-book "lexer")
(include-book "preprocessor")
(include-book "parser")
(include-book "filemap")
(include-book "inject-comments")
(include-book "overrides")
(include-book "../mlib/hierarchy")
(include-book "../mlib/print-warnings")
(include-book "../util/cwtime")
(include-book "../util/gc")
(include-book "centaur/misc/hons-extra" :dir :system)
(include-book "defsort/duplicated-members" :dir :system)
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))


(defxdoc loader
  :parents (vl)
  :short "Finds and loads Verilog source files into parsed @(see modules)."

  :long "<p>Most Verilog designs involve many files spread out across multiple
directories.  To really load a high-level module @('top'), we typically need
to:</p>

<ul>

<li>start by parsing its file, say @('top.v'), then</li>

<li>figure out which supporting modules are used within @('top') and </li>

<li>use a search procedure to load these supporting modules from library
directories.</li>

</ul>

<p>Our top-level function for loading Verilog files, @(see vl-load),
implements such a scheme.  It has various <see topic='@(url
vl-loadconfig-p)'>options</see> that allow you to specify the search paths and
extensions to use when looking for files, etc.  It also features an @(see
overrides) mechanism that can be used to \"safely\" use alternate definitions
for certain (usually low-level) modules.</p>


<h3>VL-Only Comments</h3>

<p>VL supports a special comment syntax:</p>

@({
//+VL single-line version
/*+VL multi-line version */
})

<p>Which can be used to hide VL-specific code from other tools, e.g., if you
need your modules to work with an older Verilog implementation that doesn't
support Verilog-2005 style attributes, you might write something like:</p>

@({
//+VL (* my_attribute *)
assign foo = bar;
})

<p>There is also a special, more concise syntax for attributes:</p>

@({
//@VL my_attribute
})

<p><b>BOZO</b> where should things like VL-Only comments be documented?  There
are lots of special implementation details (and extensions like @(see
overrides)) that we should probably discuss somewhere.</p>")


(defaggregate vl-loadconfig
  :parents (loader)
  :short "Options for how to load Verilog modules."

  ((start-files    string-listp
                   "A list of file names (not module names) that you want to
                    load; @(see vl-load) begins by trying to read, preprocess,
                    lex, and parse the contents of these files.")

   (start-modnames string-listp
                   "Instead of (or in addition to) explicitly providing the
                    @('start-files'), you can also provide a list of module
                    names that you want to load.  @(see vl-load) will look for
                    these modules in the search path, unless they happen to get
                    loaded while processing the @('start-files').")

   (search-path    string-listp
                   "A list of directories to search (in order) for modules in
                    @('start-modnames') that were in the @('start-files'), and
                    for <see topic=\"@(url vl-modulelist-missing)\">missing
                    modules</see>.  This is similar to \"library directories\"
                    in tools like Verilog-XL and NCVerilog.")

   (search-exts    string-listp
                   :default '("v")
                   "List of file extensions to search (in order) to find files
                    in the @('search-path').  The default is @('(\"v\")'),
                    meaning that only files like @('foo.v') are considered.")

   (include-dirs   string-listp
                   "A list of directories that will be searched (in order) when
                    @('`include') directives are encountered.  This is similar
                    to the \"include directories\" for Verilog-XL.  Any
                    includes with relative path names are searched for in (1)
                    the current directory, then (2) these include dirs, in the
                    specified order.")

   (defines        vl-defines-p
                   "A list of initial definitions (i.e., @('`define')s) that
                    will be given to the @(see preprocessor).  You may want to
                    see @(see vl-make-initial-defines), and you should probably
                    be aware of the @(see scope-of-defines).")

   (filemapp       booleanp
                   :rule-classes :type-prescription
                   :default t
                   "This flag controls whether a @(see vl-filemap-p) will be
                    constructed for the files we have loaded.  You may wish to
                    turn this off to save some memory.")

   (override-dirs  string-listp
                   "Directories to scan for any @(see overrides).")

   (flush-tries    posp
                   :default 10000
                   "How many rounds of @(see vl-flush-out-modules) are
                    allowed.")

   (mintime        :default 1
                   "Minimum time threshold for performance messages."))

  :tag :vl-loadconfig)



(defaggregate vl-loadstate
  :parents (loader)
  :short "Internal state object used throughout the VL loading routines."

  ((config    vl-loadconfig-p
              "Original configuration passed to @(see vl-load).  This remains
               constant throughout our loading routines.")


   (overrides vl-override-db-p
              "Database of modules to override; see @(see overrides).")

   (oused     vl-overridelist-p
              "List of overrides that we have actually used so far.  This is
               needed so we can check that overrides are up to date with @(see
               vl-check-override-requirements), etc.")

   (mtokens   vl-modtokensalist-p
              "Alist binding module names to their actual tokens, used for
               checking that @(see overrides) are correct.")

   (required  string-listp
              "List of module names that must be defined because they are
               required by overrides.  Should always be equal to
               @('(vl-override-requirement-names oused)'), but that would
               be expensive to recompute during flushing, so we keep it as
               part of the state.")


   (mods      (and (vl-modulelist-p mods)
                   (uniquep (vl-modulelist->names mods)))
              "@(see modules) we have loaded so far.  These modules have been
               only minimally transformed, and are intended to capture the
               actual source code in the files on disk.")

   (modalist  (equal modalist (vl-modalist mods))
              "Provides fast module-name lookups.")

   (defines   vl-defines-p
              "The current set of @('`define')s at any point in time.")

   (walist    vl-modwarningalist-p
              "Associates module names with warnings we want to add to those modules.
               This is where most warnings from loading can be found.")

   (warnings  vl-warninglist-p
              "This holds any \"floating\" @(see warnings) that aren't
               associated with any module.  Few warnings get put here. Instead,
               most warnings get associated with particular modules. But some
               warnings from the early stages of file loading (like
               preprocessing and lexing), or warnings about malformed syntax
               that occurs <i>between</i> modules, can end up here.")

   (filemap   vl-filemap-p
              "Database mapping the names of files we have read to their contents.
               This is occasionally useful for seeing the original code for a
               module.  To save memory, you can avoid constructing this alist;
               see the @('filemapp') option in @(see vl-loadconfig-p)."))

  :tag :vl-loadstate)

(defthm return-type-vl-loadstate->modalist*
  ;; Non-forcing version.  Forcing things like (foop (accessor x)) is generally
  ;; fine.  But this rule is different: it unconditionally rewrites (accessor
  ;; x) into something else.  That leads to forcing any time that we ever see a
  ;; call of (accessor x), e.g., any time we ever call change-blah, and is just
  ;; generally problematic.  BOZO consider adding a :force nil option to
  ;; aggregate field specifiers.
  (implies (vl-loadstate-p x)
           (equal (vl-loadstate->modalist x)
                  (vl-modalist (vl-loadstate->mods x)))))

(in-theory (disable (:rewrite return-type-of-vl-loadstate->modalist)))



(defsection scope-of-defines
  :parents (loader)
  :short "How VL and other tools handle the scope of @('`defines')."

  :long "<p><i>What is the scope of a @('`define')?</i></p>

<p>Until the end of 2009, we treated @('`define')s as having file-scope, and
processed every file using only the initial @('define')s to begin with.  But
now we are treating @('`define')s as cumulative, allowing them to spill over
from one file into the next.  This is convenient in that it allows us to see
what defines have been encountered, and hence we can programmatically extract
the values associated with particular @('`define') symbols.</p>

<p>This is scary.  The order of file loading is not especially predictable when
@(see vl-flush-out-modules) is used, so different things might happen depending
on which files happen to get loaded first!</p>

<p>Well, our behavior appears to be at least similar to what other Verilog
tools do.  We found that, on both Verilog-XL and NCVerilog,</p>

<ul>

<li>@('`define')s that occur before an @('`include') do seem to carry over into
the included file.</li>

<li>When we give the tool multiple files, e.g., @('verilog foo.v bar.v') or
@('ncverilog foo.v bar.v'), the includes from the earlier files do carry over
to the later files.  Hence, switching the argument order can affect simulation
results.</li>

<li>@('`define')s that occur in the main files (those that are given as
explicit command line arguments) are indeed carried over into library
files</li>

<li>@('`define')s from earlier-loaded library files are carried over into
later-loaded library files.</li>

</ul>

<p>Our behavior is <b>approximately</b> the same.  However, it seems very
likely that our particular way of loading missing modules with @(see
vl-flush-out-modules) will be at least somewhat different from how other tools
look for missing modules.  Roughly, after parsing the main files, we figure out
what modules are missing and try to load them in alphabetical order.  Other
tools probably use different orders and may produce very different
behaviors.</p>

<p>BOZO we could probably defend against this by tracking which @('ifdef')
tests have ever been considered and what their values are.  If we find that two
files have ever done an @('ifdef') and gotten different results, we could add a
warning that maybe something is amiss with file loading.</p>")



(define vl-load-merge-modules ((new      vl-modulelist-p)
                               (old      vl-modulelist-p)
                               (modalist (equal modalist (vl-modalist old)))
                               (walist   vl-modwarningalist-p))
  :returns (mv (merged   (vl-modulelist-p merged) :hyp :fguard)
               (modalist (equal modalist (vl-modalist merged)) :hyp :fguard)
               (walist   vl-modwarningalist-p :hyp :fguard))
  :parents (loader)
  :short "Merge newly found Verilog modules with previously loaded modules,
warning about multiply defined modules."

  :long "<p>As a simple rule, we always keep the first definition of any module
we encounter.  This function is responsible for enforcing this rule: we merge
some newly parsed modules in with the already-parsed modules.  In case of any
name clashes, the previous definition wins, and we add a warning to the
@('walist') to say that the original definition is being kept.</p>"

  (b* (((when (atom new))
        (mv old modalist walist))
       (new-mod  (car new))
       (new-name (vl-module->name new-mod))
       (prev-def (vl-fast-find-module new-name old modalist))
       ((unless prev-def)
        ;; Great, new module, no redefinition.
        (vl-load-merge-modules (cdr new)
                               (cons new-mod old)
                               (hons-acons new-name new-mod modalist)
                               walist))
       ;; Warn about the redefinition,
       (warning (make-vl-warning
                 :type :vl-multidef-mod
                 :msg "~m0 is defined multiple times.  Keeping the old ~
                       definition (~a1) and ignoring the new one (~a2)."
                 :args (list new-name
                             (vl-module->minloc prev-def)
                             (vl-module->minloc new-mod))))
       (walist (vl-extend-modwarningalist new-name warning walist)))
    (vl-load-merge-modules (cdr new) old modalist walist))
  ///
  (defthm unique-names-after-vl-load-merge-modules
    (implies (and (uniquep (vl-modulelist->names old))
                  (force (vl-modulelist-p new))
                  (force (vl-modulelist-p old)))
             (b* (((mv merged ?modalist ?walist)
                   (vl-load-merge-modules new old modalist walist)))
               (uniquep (vl-modulelist->names merged))))))



(define vl-load-file ((filename stringp)
                      (st       vl-loadstate-p)
                      state)
  :returns (mv (st    vl-loadstate-p :hyp :fguard)
               (state state-p1       :hyp (force (state-p1 state))))
  :parents (loader)
  :short "Main function for loading a single Verilog file."

  :long "<p>Even loading a single file is a multi-step process:</p>

<ul>

<li>The contents of the file are loaded via @(see vl-read-file) into a list of
@(see extended-characters) in memory.</li>

<li>The @(see preprocessor) then expands away compiler directives like
@('`define')s, producing a new list of extended characters.</li>

<li>The @(see lexer) converts the preprocessed character list into a list of
<see topic='@(url vl-token-p)'>tokens</see>.</li>

<li>Any applicable @(see overrides) are applied, perhaps resulting in a new
token list.</li>

<li>The @(see parser) transforms the token list into a list of @(see modules),
our internal representation of Verilog.</li>

</ul>"

  (b* (((vl-loadstate st) st)
       ((vl-loadconfig config) st.config)

       (warnings st.warnings)

       ;; BOZO we should switch this to use some more subtle b* structure that
       ;; lets contents become unreachable.

       ((mv contents state)
        (time$ (vl-read-file (string-fix filename) state)
               :msg "; ~s0: read: ~st sec, ~sa bytes~%"
               :args (list filename)
               :mintime config.mintime))
       ((when (stringp contents))
        (b* ((warnings (warn :type :vl-read-failed
                             :msg  "Error reading file ~s0."
                             :args (list filename)))
             (st       (change-vl-loadstate st :warnings warnings)))
          (mv st state)))

       (filemap
        (time$ (and config.filemapp
                    (cons (cons filename (vl-echarlist->string contents))
                          st.filemap))
               :msg "; ~s0: filemap: ~st sec, ~sa bytes~%"
               :args (list filename)
               :mintime config.mintime))


; Subtle: If preprocessing fails, should we return the updated defines?  The
; answer isn't very clear, and you can probably make a case for it either way.
; I think it makes the most sense to impose a simple, consistent rule:
;
;   +---------------------------------------------------------------+
;   | If we can't parse the file successfully, we don't update any  |
;   | part of the state except the warnings (warnings and walist).  |
;   +---------------------------------------------------------------|
;
; This way things are pretty clear.  Whatever was in that file we couldn't
; parse didn't affect us.  If it had defines we wanted, that's too bad.

       ((mv successp defines preprocessed state)
        (time$ (vl-preprocess contents st.defines config.include-dirs state)
               :msg "; ~s0: preprocess: ~st sec, ~sa bytes~%"
               :args (list filename)
               :mintime config.mintime))
       ((unless successp)
        (b* ((warnings (warn :type :vl-preprocess-failed
                             :msg "Preprocessing failed for ~s0."
                             :args (list filename)))
             (st       (change-vl-loadstate st :warnings warnings)))
          (mv st state)))

       ((mv successp lexed warnings)
        (time$ (vl-lex preprocessed warnings)
               :msg "; ~s0: lex: ~st sec, ~sa bytes~%"
               :args (list filename)
               :mintime config.mintime))
       ((unless successp)
        (b* ((warnings (warn :type :vl-lex-failed
                             :msg "Lexing failed for ~s0."
                             :args (list filename)))
             (st       (change-vl-loadstate st :warnings warnings)))
          (mv st state)))

       ((mv cleaned comment-map)
        (time$ (vl-kill-whitespace-and-comments lexed)
               :msg "; ~s0: whitespace: ~st sec, ~sa bytes~%"
               :args (list filename)
               :mintime config.mintime))
       ((mv walist cleaned oused mtokens)
        (time$ (vl-apply-overrides cleaned st.overrides st.walist)
               :msg "; ~s0: override: ~st sec, ~sa bytes~%"
               :args (list filename)
               :mintime config.mintime))

       ((mv successp mods warnings)
        (time$ (vl-parse cleaned warnings)
               :msg "; ~s0: parse: ~st sec, ~sa bytes~%"
               :args (list filename)
               :mintime config.mintime))
       ((unless successp)
        ;; In practice this should be rare.  See vl-parse-module-declaration:
        ;; We do something pretty fancy to make sure that parse errors that
        ;; occur within a module only kill that particular module.
        (b* ((warnings (warn :type :vl-parse-failed
                             :msg "Parsing failed for ~s0."
                             :args (list filename)))
             (st       (change-vl-loadstate st
                                            :warnings warnings
                                            :walist walist)))
          (mv st state)))

       (mods
        (time$ (vl-inject-comments-modulelist mods comment-map)
               :msg "; ~s0: comment: ~st sec, ~sa bytes~%"
               :args (list filename)
               :mintime config.mintime))

       ;; Merge new modules into previous modules.
       ((mv mods modalist walist)
        (time$ (vl-load-merge-modules mods st.mods st.modalist walist)
               :msg "; ~s0: merge: ~st sec, ~sa bytes~%"
               :args (list filename)
               :mintime config.mintime))

       ;; Overrides tracking stuff.  BOZO this might not be quite right for
       ;; modules that are multiply defined, because we've dropped them during
       ;; the merge but not from oused/mtokens.  Blah.
       ((mv required oused mtokens)
        (time$
         (b* ((required (union (mergesort (vl-overridelist-requirement-names oused))
                               (redundant-mergesort st.required)))
              (oused    (append oused st.oused))
              (mtokens  (append mtokens st.mtokens)))
           (mv required oused mtokens))
         :msg "; ~s0: track overrides: ~st sec, ~sa bytes~%"
         :args (list filename)
         :mintime config.mintime))

       (st    (change-vl-loadstate st
                                   :warnings warnings
                                   :defines  defines
                                   :filemap  filemap
                                   :mods     mods
                                   :modalist modalist
                                   :walist   walist
                                   :oused    oused
                                   :mtokens  mtokens
                                   :required required)))

    (mv st state)))

(define vl-load-files ((filenames string-listp)
                       (st        vl-loadstate-p)
                       state)
  :returns (mv (st       vl-loadstate-p :hyp :fguard)
               (state    state-p1       :hyp (force (state-p1 state))))
  :parents (loader)
  :short "Load a list of files."
  (b* (((when (atom filenames))
        (mv st state))
       ((mv st state) (vl-load-file (car filenames) st state)))
    (vl-load-files (cdr filenames) st state)))



(define vl-load-module ((modname stringp)
                        (st      vl-loadstate-p)
                        state)
  :returns (mv (st    vl-loadstate-p :hyp :fguard)
               (state state-p1       :hyp (force (state-p1 state))))
  :parents (loader)
  :short "Try to load a module from the search path."

  (b* (((vl-loadstate st) st)
       ((vl-loadconfig config) st.config)
       (warnings st.warnings)

       ((mv filename warnings state)
        (vl-find-basename/extension modname config.search-exts config.search-path
                                    warnings state))
       ((unless filename)
        (b* ((warnings (warn :type :vl-warn-find-failed
                             :msg "Unable to find a file for module ~s0."
                             :args (list modname)))
             (st (change-vl-loadstate st :warnings warnings)))
          (mv st state)))

       (st (change-vl-loadstate st :warnings warnings)))

    (vl-load-file filename st state)))


(define vl-load-modules ((modnames string-listp)
                         (st       vl-loadstate-p)
                         state)
  :returns (mv (st    vl-loadstate-p :hyp :fguard)
               (state state-p1       :hyp (force (state-p1 state))))
  :parents (loader)
  :short "Extend @(see vl-load-module) to try to load a list of modules."

  (b* (((when (atom modnames))
        (mv st state))
       ((mv st state) (vl-load-module (car modnames) st state))
       ((mv st state) (vl-load-modules (cdr modnames) st state)))
    (mv st state)))


(define vl-modules-left-to-load ((st vl-loadstate-p))
  :returns (names string-listp :hyp :fguard)
  :parents (loader)
  :short "Determine which modules we still need to load."

  :long "<p>For loading to be completely done, we want to have:</p>

<ul>

<li>All modules that the user told us to load in the @(':start-modnames')</li>

<li>All modules that are ever instanced anywhere in any module that we have
loaded, and</li>

<li>All modules that are required to be loaded because of @(see
overrides).</li>

</ul>

<p>This function computes the names of modules that we want for the above
reasons, but which we do not yet have loaded.  These are the modules we'll end
up searching for.</p>"

  (b* (((vl-loadstate st) st)
       ((vl-loadconfig config) st.config)

       (mods-we-want-loaded
        (mergesort (vl-modulelist-everinstanced-exec
                    st.mods
                    (append st.required config.start-modnames))))

       (mods-we-have-loaded
        (mergesort (vl-modulelist->names-exec st.mods nil))))

    (difference mods-we-want-loaded mods-we-have-loaded)))


(define vl-flush-out-modules ((st vl-loadstate-p)
                              (n  natp "Counter to force termination.")
                              state)
  :returns (mv (st    vl-loadstate-p :hyp :fguard)
               (state state-p1       :hyp (force (state-p1 state))
                      :hints(("Goal" :in-theory (disable (force))))))
  :parents (loader)
  :short "Attempt to find and load any missing modules."

  :long "<p>After some initial files have been loaded, it is generally
necessary to track down and load any submodules that have been referenced but
not defined.  We call this process \"flushing out\" the module list.</p>

<p>To find some module @('foo'), we look through the provided search
directories, in order, for a file whose name is @('foo.v').  (We can also
consider files with other extensions, see the @('search-exts') option in @(see
vl-loadconfig-p).)</p>

<p>We try to load the first such @('foo.v') that we find.  This is <b>not
necessarily sensible</b>.  It might be, for instance, that @('foo.v') will not
define a module named @('foo'), or that it will define all sorts of other
modules instead of @('foo').  In other words, for this search procedure to make
sense, you need to follow a sort of naming discipline and keep library modules
in files that have appropriate names.</p>

<p>Flushing out the modules is necessarily an <b>iterative</b> process.  After
we load some library module @('foo'), we might find that it references some
other library module @('bar') that we have not yet loaded.  To ensure that the
process will eventually terminate, so cap the maximum number of times we will
look for new modules.</p>"

  :measure (nfix n)

  (b* ((missing (vl-modules-left-to-load st))
       ((unless missing)
        ;; We have everything loaded that we want, so we're all done.
        (mv st state))

       ((when (zp n))
        ;; (cw "Ran out of steps in vl-flush-out-modules.~%")
        (b* ((warnings (vl-loadstate->warnings st))
             (warnings (warn :type :vl-flush-failed
                             :msg "Failed to load module~s0 ~&1 because we ~
                                   reached the maximum number of tries."
                             :args (list (if (vl-plural-p missing) "s" "")
                                         missing)))
             (st (change-vl-loadstate st :warnings warnings)))
          (mv st state)))

       ;; (- (cw "Searching for ~x0 missing modules (~x1 tries left).~%" (length missing) n))

       (num-prev      (len (vl-loadstate->mods st)))
       ((mv st state) (vl-load-modules missing st state))
       (num-new       (len (vl-loadstate->mods st)))

       ((when (equal num-prev num-new))
        ;; Failed to load anything new, so we've loaded as much as we can.
        (b* ((warnings (vl-loadstate->warnings st))
             (warnings (warn :type :vl-search-failed
                             :msg  "Failed to find ~x0 module~s1: ~&2."
                             :args (list (length missing)
                                         (if (vl-plural-p missing) "s" "")
                                         (mergesort missing))))
             (st       (change-vl-loadstate st :warnings warnings)))
          (mv st state))))

    ;; Else, got at least some modules.  But remember: just because we
    ;; loaded N modules doesn't mean we loaded the ones we needed, and it
    ;; doesn't mean we don't now need new ones!  So don't try to detect
    ;; whether we're successful, just keep flushing out until we stop making
    ;; progress or find everything.
    (vl-flush-out-modules st (- n 1) state)))


(defaggregate vl-loadresult
  :parents (loader)
  :short "Return value from @(see vl-load)."

  ((mods        (and (vl-modulelist-p mods)
                     (uniquep (vl-modulelist->names mods)))
                "The @(see modules) that were loaded.  These modules have been
                 only minimally transformed (e.g., to add declarations for
                 implicit wires).  They meant to be close to the actual source
                 code as it occurs on the disk.  They are guaranteed to have
                 unique names.")

   (filemap     vl-filemap-p
                "Alist mapping file names to their original, unmodified
                 contents as strings.  This can be useful for interactively
                 looking at module definitions, but takes some memory.  You can
                 control whether a filemap is generated in your @(see
                 vl-loadconfig-p).")

   (warnings    vl-warninglist-p
                "This holds any <b>floating</b> @(see warnings)&mdash;those
                 that aren't associated with any module.  Few warnings get put
                 here.  Instead, most warnings are associated with particular
                 modules.  But some warnings from the early stages of file
                 loading (like preprocessing and lexing), or warnings that
                 somehow occur <i>between</i> modules, can end up here.")

   (defines     vl-defines-p
                "Final defines that we ended up with.  This can be useful for
                 extracting the values of @('`define')s.  See also @(see
                 scope-of-defines)."))

  :tag :vl-loadresult)


(define vl-load-main ((config vl-loadconfig-p)
                      state)
  :returns (mv (result vl-loadresult-p :hyp :fguard)
               (state  state-p1        :hyp (force (state-p1 state))))
  :parents (loader)
  :short "Top level interface for loading Verilog sources."

  (b* ((config
        ;; I'm pretty sure this is the right thing to do.  I've done a few
        ;; simple tests, and both Verilog-XL and NCVerilog seem to always
        ;; include files from the current directory first, even if +incdir
        ;; arguments are given, and even if there is a +incdir argument that
        ;; comes before an explicit +incdir+. or +incdir+`pwd`.  So, it seems
        ;; like "." is always implicitly the first place to search for
        ;; includes.
        (change-vl-loadconfig config
                              :include-dirs
                              (cons "." (vl-loadconfig->include-dirs config))))

       ((vl-loadconfig config) config)

       ((mv ?okp overrides filemap defines override-comments walist state)
        (time$ (vl-read-overrides config.override-dirs
                                  config.defines
                                  config.filemapp
                                  state)
               :msg "; read overrides: ~st sec, ~sa bytes~%"
               :mintime config.mintime))

       (st (make-vl-loadstate :config    config
                              :overrides overrides
                              :oused     nil
                              :mtokens   nil
                              :required  nil
                              :mods      nil
                              :modalist  nil
                              :defines   defines
                              :walist    walist
                              :warnings  nil
                              :filemap   filemap))

       ((mv st state)
        (time$ (vl-load-files config.start-files st state)
               :msg "; load start-files: ~st sec, ~sa bytes~%"
               :mintime config.mintime))

       ((mv st state)
        (time$ (vl-flush-out-modules st config.flush-tries state)
               :msg "; load missing modules: ~st sec, ~sa bytes~%"
               :mintime config.mintime))

       ;; Final override handling.  Need to add comments to the overridden
       ;; modules and check that all requirements are met.

       ((vl-loadstate st) st)

       (mods
        (time$ (vl-inject-comments-modulelist st.mods override-comments)
               :msg "; override comments: ~st sec, ~sa bytes~%"
               :mintime config.mintime))

       (walist
        (time$ (with-fast-alist st.mtokens
                 (vl-check-override-requirements st.oused st.mtokens st.walist))
               :msg "; override checks: ~st sec, ~sa bytes~%"
               :mintime config.mintime))

       (mods
        (time$ (vl-apply-modwarningalist mods walist)
               :msg "; apply warnings: ~st sec, ~sa bytes~%"
               :mintime config.mintime))

       (result (make-vl-loadresult :mods mods
                                   :filemap st.filemap
                                   :warnings st.warnings)))

    (fast-alist-free overrides)
    (fast-alist-free (vl-loadstate->modalist st))
    (mv result state)))



(defsection vl-load-summary
  :parents (loader)
  :short "Print summary information (e.g., warnings, numbers of modules loaded,
etc.) after modules have been loaded."

  :long "<p>This is attachable.  By default we print a rather elaborate report
that says how many modules were loaded.  Depending on the tool you are building
you might want to attach some other kind of report here.</p>

@(def vl-load-summary)"

  (encapsulate
    (((vl-load-summary * *) => *
      :formals (config result)
      :guard (and (vl-loadconfig-p config)
                  (vl-loadresult-p result))))
    (local (defun vl-load-summary (config result)
             (declare (ignore config result))
             nil))))

(define vl-default-load-summary ((config vl-loadconfig-p)
                                 (result vl-loadresult-p))
  :returns (nil)
  :parents (vl-load-summary)
  (declare (ignore config))
  (b* (((vl-loadresult result) result)
       (mods result.mods)
       (- (cw "Loaded ~x0 modules.~%" (len mods)))

       ;; The warnings get returned, but we also summarize the floating
       ;; warnings as a convenience to whomever is running the translator.
       (mod-warnings      (mergesort (vl-modulelist-flat-warnings mods)))
       (all-warnings      (mergesort (append-without-guard result.warnings mod-warnings)))
       (- (or (not all-warnings)
              (cw "Total number of warnings: ~x0.~%"
                  (len all-warnings))))

       (floating-warnings (difference all-warnings mod-warnings))
       (- (or (not floating-warnings)
              (vl-cw-ps-seq
               (vl-ps-update-autowrap-col 68)
               (vl-cw "~x0 floating warning~s1:~%"
                      (len floating-warnings)
                      (if (= (len floating-warnings) 1) "" "s"))
               (vl-print-warnings floating-warnings)
               (vl-println ""))))

       (multidef-warnings (vl-keep-warnings '(:vl-multidef-mod) mod-warnings))
       (- (or (not multidef-warnings)
              (vl-cw-ps-seq
               (vl-ps-update-autowrap-col 68)
               (vl-cw "~x0 multiply defined module warning~s1:~%"
                      (len multidef-warnings)
                      (if (= (len multidef-warnings) 1) "" "s"))
               (vl-print-warnings multidef-warnings)
               (vl-println "")))))
    nil))

(defattach vl-load-summary vl-default-load-summary)

(define vl-load ((config vl-loadconfig-p)
                 &key
                 (state 'state))
  :parents (loader)
  :short "Wrapper for @(see vl-load-main) that also reports errors or (with
some configuration) can print other information."

  :long "<p>This is very similar to @(see vl-load-main), but calls @(see
vl-load-summary) afterwards.</p>"

  :returns (mv (result vl-loadresult-p :hyp :fguard)
               (state  state-p1        :hyp (force (state-p1 state))))
  (b* (((vl-loadconfig config) config)
       ((mv result state)
        (time$ (vl-load-main config state)
               :msg "; vl-load-main: ~st sec, ~sa bytes~%"
               :mintime config.mintime)))
    ;; This is a reasonably good time to garbage collect since file reading,
    ;; lexing, etc. create a lot of garbage.
    (clear-memoize-table 'vl-actually-report-parse-error)
    (vl-gc)
    (vl-load-summary config result)
    (mv result state)))
