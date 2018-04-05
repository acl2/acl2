; VL 2014 -- VL Verilog Toolkit, 2014 Edition
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
(include-book "config")
(include-book "read-file")
(include-book "find-file")
(include-book "lexer/lexer")
(include-book "preprocessor/preprocessor")
(include-book "parser/parser")
(include-book "filemap")
(include-book "inject-comments")
(include-book "inject-warnings")
(include-book "../mlib/flat-warnings")
(include-book "../mlib/print-warnings")
(include-book "../mlib/scopestack")
(include-book "../util/cwtime")
(include-book "../util/gc")
(include-book "std/strings/fast-cat" :dir :system)
(include-book "centaur/misc/hons-extra" :dir :system)
(include-book "defsort/duplicated-members" :dir :system)
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))

(defxdoc loader
  :parents (vl2014)
  :short "Finds and loads Verilog source files."

  :long "<p>Most Verilog designs involve many files spread out across multiple
directories.  To really load a high-level module @('top'), we typically need
to:</p>

<ul>

<li>start by parsing its file, say @('top.v'), then</li>

<li>figure out which supporting descriptions are used within @('top') and </li>

<li>use a search procedure to load these supporting descriptions from library
directories.</li>

</ul>

<p>Our top-level function for loading Verilog files, @(see vl-load), implements
such a scheme.  It has various options (see @(see vl-loadconfig-p)) that allow
you to specify the search paths and extensions to use when looking for files,
etc.</p>


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
})")

(local (xdoc::set-default-parents loader))

(defprod vl-loadstate
  :short "Internal state object used throughout the VL loading routines."
  :tag :vl-loadstate
  :layout :tree
  ((config    vl-loadconfig-p
              "Original configuration passed to @(see vl-load).  This remains
               constant throughout our loading routines.")

   (descs     vl-descriptionlist-p
              "Top-level descriptions (modules, packages, interfaces, etc.)  we
               have loaded so far.  These descriptions have been only minimally
               transformed, and are intended to capture the actual source code
               in the files on disk.")

   (descalist  t
               "Fast alist of description names, for fast lookups."
               :reqfix (vl-make-descalist descs))

   (defines   vl-defines-p
              "The current set of @('`define')s at any point in time.")

   (reportcard vl-reportcard-p
               "Main storage for load-time warnings that we want to associate
                with particular descriptions.  This is where most load-time
                warnings from loading are kept during loading.  At the end of
                loading, these warnings get injected into the actual
                descriptions they pertain to.")

   (pstate    vl-parsestate-p
              "State that the parser needs.  BOZO probably we should consider
               moving some of the loadstate into the pstate.  This holds, among
               other things, any \"floating\" warnings that aren't associated
               with any description.  But few warnings get put here. Instead,
               most warnings get associated with particular descriptions. But
               some warnings from the early stages of file loading (like
               preprocessing and lexing), or warnings about malformed syntax
               that occurs <i>between</i> descriptions, can end up here.")

   (filemap   vl-filemap-p
              "Database mapping the names of files we have read to their contents.
               This is occasionally useful for seeing the original code for a
               description.  To save memory, you can avoid constructing this
               alist; see the @('filemapp') option in @(see
               vl-loadconfig-p)."))

  :require
  (equal descalist (vl-make-descalist descs)))

(define vl-loadstate-warn (&key
                           (type   symbolp)
                           (msg    stringp)
                           (args   true-listp)
                           ((fn    symbolp) '__function__)
                           (fatalp booleanp)
                           ((st    vl-loadstate-p) 'st))
  :returns (new-st vl-loadstate-p)
  :parents (vl-loadstate-p)
  (b* (((vl-loadstate st) st)
       ((vl-parsestate st.pstate) st.pstate)
       (w          (make-vl-warning :type type
                                    :msg msg
                                    :args args
                                    :fn fn
                                    :fatalp fatalp))
       (new-pstate (change-vl-parsestate st.pstate
                                         :warnings (cons w st.pstate.warnings))))
    (change-vl-loadstate st :pstate new-pstate)))

(define vl-loadstate-set-warnings ((warnings vl-warninglist-p)
                                   &key
                                   ((st vl-loadstate-p) 'st))
  :parents (vl-loadstate-p)
  :returns (new-st vl-loadstate-p)
  (b* (((vl-loadstate st) st)
       (new-pstate (change-vl-parsestate st.pstate :warnings warnings)))
    (change-vl-loadstate st :pstate new-pstate)))

(local (in-theory (enable vl-loadstate-set-warnings)))


(defsection scope-of-defines
  :short "How VL and other tools handle the scope of @('`defines')."

  :long "<p><i>What is the scope of a @('`define')?</i></p>

<p>Until the end of 2009, we treated @('`define')s as having file-scope, and
processed every file using only the initial @('define')s to begin with.  But
now we are treating @('`define')s as cumulative, allowing them to spill over
from one file into the next.  This is convenient in that it allows us to see
what defines have been encountered, and hence we can programmatically extract
the values associated with particular @('`define') symbols.</p>

<p>This is scary.  The order of file loading is not especially predictable when
@(see vl-flush-out-descriptions) is used, so different things might happen
depending on which files happen to get loaded first!</p>

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
likely that our particular way of loading missing descriptions with @(see
vl-flush-out-descriptions) will be at least somewhat different from how other tools
look for missing descriptions.  Roughly, after parsing the main files, we figure out
what descriptions are missing and try to load them in alphabetical order.  Other
tools probably use different orders and may produce very different
behaviors.</p>

<p>BOZO we could probably defend against this by tracking which @('ifdef')
tests have ever been considered and what their values are.  If we find that two
files have ever done an @('ifdef') and gotten different results, we could add a
warning that maybe something is amiss with file loading.</p>")

(define vl-load-merge-descriptions
  :short "Merge newly found Verilog descriptions with previously loaded
descriptions, warning about any multiply defined descriptions."
  ((new        vl-descriptionlist-p)
   (old        vl-descriptionlist-p)
   (descalist  (equal descalist (vl-make-descalist old)))
   (reportcard vl-reportcard-p))
  :returns (mv (merged        vl-descriptionlist-p)
               (new-descalist (equal new-descalist (vl-make-descalist merged))
                              :hyp (equal descalist (vl-make-descalist old)))
               (reportcard vl-reportcard-p))
  :long "<p>As a simple rule, we always keep the first definition of any
description we encounter.  This function is responsible for enforcing this
rule: we merge some newly parsed descriptions in with the already-parsed
descriptions.  If there are any name clashes, the original definition wins, and
we add a warning to the @('reportcard') to say that the original definition is
being kept.</p>"
  :hooks (:fix)
  :prepwork ((local (in-theory (enable vl-make-descalist))))
  (b* ((old        (vl-descriptionlist-fix old))
       (reportcard (vl-reportcard-fix reportcard))
       ((when (atom new))
        (mv old descalist reportcard))
       (newdesc1  (vl-description-fix (car new)))
       (newname1  (vl-description->name newdesc1))
       ((unless newname1)
        ;; Special kind of description like an import statement or an anonymous
        ;; program.  Since there's no name, there's no possible name clash.
        (vl-load-merge-descriptions (cdr new)
                                    (cons newdesc1 old)
                                    descalist
                                    reportcard))

       ;; Ordinary description with a name.  Check for previous definitions.
       (prevdesc  (vl-fast-find-description newname1 old descalist))
       ((unless prevdesc)
        ;; Great, new description, no redefinition.
        (vl-load-merge-descriptions (cdr new)
                                    (cons newdesc1 old)
                                    (hons-acons newname1 newdesc1 descalist)
                                    reportcard))
       ;; Whoops, trying to redefine newname1.  Warn that we're keeping the
       ;; original version.  Arguably this should be a fatal warning, but I'm
       ;; keeping it as a non-fatal warning because, as a VL user, it's often
       ;; useful to exploit the fact that VL keeps only the first definition
       ;; encountered, e.g., as a barbaric way to override problematic
       ;; definitions.
       (warning (make-vl-warning
                 :type :vl-warn-multidef
                 :msg "~m0 is defined multiple times.  Keeping the old ~
                       definition (~a1) and ignoring the new one (~a2)."
                 :args (list newname1
                             (vl-description->minloc prevdesc)
                             (vl-description->minloc newdesc1))))
       (reportcard (vl-extend-reportcard newname1 warning reportcard)))
    (vl-load-merge-descriptions (cdr new) old descalist reportcard))
  ///
  (defthm unique-names-after-vl-load-merge-descriptions
    (implies (uniquep (vl-descriptionlist->names old))
             (b* (((mv merged ?descalist ?reportcard)
                   (vl-load-merge-descriptions new old descalist reportcard)))
               (no-duplicatesp (vl-descriptionlist->names merged))))))


(define vl-load-file ((filename stringp)
                      (st       vl-loadstate-p)
                      state)
  :returns (mv (st    vl-loadstate-p)
               (state state-p1       :hyp (force (state-p1 state))))
  :short "Main function for loading a single Verilog file."
  :prepwork ((local (in-theory (disable (force)))))

  :long "<p>Even loading a single file is a multi-step process:</p>

<ul>

<li>The contents of the file are loaded via @(see vl-read-file) into a list of
@(see extended-characters) in memory.</li>

<li>The @(see preprocessor) then expands away compiler directives like
@('`define')s, producing a new list of extended characters.</li>

<li>The @(see lexer) converts the preprocessed character list into a list of
<see topic='@(url vl-token-p)'>tokens</see>.</li>

<li>The @(see parser) transforms the token list into a list of
descriptions.</li>

<li>We merge these newly loaded descriptions into the loader's state.</li>

</ul>"

  (b* (((vl-loadstate st) st)
       ((vl-loadconfig st.config) st.config)

       (warnings (vl-parsestate->warnings st.pstate))

       ;; BOZO we should switch this to use some more subtle b* structure that
       ;; lets contents become unreachable.

       ((mv okp contents state)
        (time$ (vl-read-file (string-fix filename))
               :msg "; ~s0: read: ~st sec, ~sa bytes~%"
               :args (list filename)
               :mintime st.config.mintime))
       ((unless okp)
        (b* ((warnings (warn :type :vl-read-failed
                             :msg  "Error reading file ~s0."
                             :args (list filename))))
          (mv (vl-loadstate-set-warnings warnings)
              state)))

       (filemap
        (time$ (and st.config.filemapp
                    (cons (cons filename (vl-echarlist->string contents))
                          st.filemap))
               :msg "; ~s0: filemap: ~st sec, ~sa bytes~%"
               :args (list filename)
               :mintime st.config.mintime))


; Subtle: If preprocessing fails, should we return the updated defines?  The
; answer isn't very clear, and you can probably make a case for it either way.
; I think it makes the most sense to impose a simple, consistent rule:
;
;   +------------------------------------------------------------------+
;   | If we can't parse the file successfully, we don't update any     |
;   | part of the state except the warnings (warnings and reportcard). |
;   +------------------------------------------------------------------|
;
; This way things are pretty clear.  Whatever was in that file we couldn't
; parse didn't affect us.  If it had defines we wanted, that's too bad.

       ((mv successp defines filemap preprocessed state)
        (time$ (vl-preprocess contents
                              :defines st.defines
                              :filemap filemap
                              :config st.config)
               :msg "; ~s0: preprocess: ~st sec, ~sa bytes~%"
               :args (list filename)
               :mintime st.config.mintime))
       ((unless successp)
        (b* ((warnings (warn :type :vl-preprocess-failed
                             :msg "Preprocessing failed for ~s0."
                             :args (list filename))))
          (mv (vl-loadstate-set-warnings warnings)
              state)))

       ((mv successp lexed warnings)
        (time$ (vl-lex preprocessed
                       :config st.config
                       :warnings warnings)
               :msg "; ~s0: lex: ~st sec, ~sa bytes~%"
               :args (list filename)
               :mintime st.config.mintime))
       ((unless successp)
        (b* ((warnings (warn :type :vl-lex-failed
                             :msg "Lexing failed for ~s0."
                             :args (list filename))))
          (mv (vl-loadstate-set-warnings warnings)
              state)))

       ((mv cleaned comment-map)
        (time$ (vl-kill-whitespace-and-comments lexed)
               :msg "; ~s0: whitespace: ~st sec, ~sa bytes~%"
               :args (list filename)
               :mintime st.config.mintime))

       ;; Subtle, horrible nonsense.  Install all warnings into the pstate.

       (pstate        (change-vl-parsestate st.pstate :warnings warnings))
       (pstate-backup pstate)

       ((mv successp descs pstate)
        (time$ (vl-parse cleaned pstate st.config)
               :msg "; ~s0: parse: ~st sec, ~sa bytes~%"
               :args (list filename)
               :mintime st.config.mintime))

       ((unless successp)
        ;; In practice this should be rare.  See vl-parse-module-declaration:
        ;; We work hard to make sure that parse errors that occur within a
        ;; module only kill that particular module.

        ;; At any rate, following our convention, we want to add nothing but
        ;; warnings to the parse state.  That means unwinding and restoring
        ;; the pstate-backup that we had.
        (b* ((-      (vl-parsestate-free pstate))
             (pstate (vl-parsestate-restore pstate-backup))
             (w      (make-vl-warning :type :vl-parse-failed
                                      :msg "Parsing failed for ~s0."
                                      :args (list filename)
                                      :fn __function__))
             (pstate (vl-parsestate-add-warning w pstate))
             (st     (change-vl-loadstate st :pstate pstate)))
          (mv st state)))

       ;; If we get here, parsing was successful, pstate has already been
       ;; extended, etc.

       (descs
        (time$ (vl-descriptionlist-inject-comments descs comment-map)
               :msg "; ~s0: comment: ~st sec, ~sa bytes~%"
               :args (list filename)
               :mintime st.config.mintime))

       ;; Try to associate low-level, "early" warnings (e.g., from the lexer)
       ;; with the appropriate modules.
       ((mv descs pstate)
        (b* ((warnings (vl-parsestate->warnings pstate))
             ((mv descs warnings)
              (vl-descriptionlist-inject-warnings descs warnings))
             (pstate (change-vl-parsestate pstate :warnings warnings)))
          (mv descs pstate)))

       ;; Merge new descriptions into previous descriptions.
       ((mv descs descalist reportcard)
        (time$ (vl-load-merge-descriptions descs st.descs st.descalist st.reportcard)
               :msg "; ~s0: merge: ~st sec, ~sa bytes~%"
               :args (list filename)
               :mintime st.config.mintime))

       (st    (change-vl-loadstate st
                                   :pstate     pstate
                                   :defines    defines
                                   :filemap    filemap
                                   :descs      descs
                                   :descalist  descalist
                                   :reportcard reportcard)))

    (mv st state))
  ///
  (defthm unique-names-after-vl-load-file
    (b* (((mv new-st &) (vl-load-file filename st state)))
      (implies (uniquep (vl-descriptionlist->names (vl-loadstate->descs st)))
               (no-duplicatesp (vl-descriptionlist->names (vl-loadstate->descs new-st)))))))


(define vl-load-files ((filenames string-listp)
                       (st        vl-loadstate-p)
                       state)
  :returns (mv (st       vl-loadstate-p)
               (state    state-p1       :hyp (force (state-p1 state))))
  :short "Load a list of files."
  (b* (((when (atom filenames))
        (mv (vl-loadstate-fix st) state))
       ((mv st state) (vl-load-file (car filenames) st state)))
    (vl-load-files (cdr filenames) st state))
  ///
  (defthm unique-names-after-vl-load-files
    (b* (((mv new-st &) (vl-load-files filenames st state)))
      (implies (uniquep (vl-descriptionlist->names (vl-loadstate->descs st)))
               (no-duplicatesp (vl-descriptionlist->names (vl-loadstate->descs new-st)))))))



(define vl-load-description
  :short "Try to load a description from the search path."
  ((name    stringp         "The name of the description we want to load.")
   (st      vl-loadstate-p)
   state)
  :returns (mv (st    vl-loadstate-p)
               (state state-p1       :hyp (force (state-p1 state))))

  :prepwork ((local (in-theory (disable (force)))))

  (b* (((vl-loadstate st) st)
       ((vl-loadconfig config) st.config)
       (warnings (vl-parsestate->warnings st.pstate))

       ((mv filename warnings state)
        (vl-find-basename/extension name config.search-exts config.search-path
                                    warnings state))
       ((unless filename)
        (b* ((warnings (warn :type :vl-warn-find-failed
                             :msg "Unable to find a file for ~s0."
                             :args (list name))))
          (mv (vl-loadstate-set-warnings warnings)
              state)))

       (st (vl-loadstate-set-warnings warnings)))

    (vl-load-file filename st state))
  ///
  (defthm unique-names-after-vl-load-description
    (b* (((mv new-st &) (vl-load-description name st state)))
      (implies (uniquep (vl-descriptionlist->names (vl-loadstate->descs st)))
               (no-duplicatesp (vl-descriptionlist->names (vl-loadstate->descs new-st)))))))


(define vl-load-descriptions
  :short "Extend @(see vl-load-description) to try to load a list of descriptions."
  ((names string-listp)
   (st    vl-loadstate-p)
   state)
  :returns (mv (st    vl-loadstate-p)
               (state state-p1       :hyp (force (state-p1 state))))
  (b* (((when (atom names))
        (mv (vl-loadstate-fix st) state))
       ((mv st state) (vl-load-description (car names) st state))
       ((mv st state) (vl-load-descriptions (cdr names) st state)))
    (mv st state))
  ///
  (defthm unique-names-after-vl-load-descriptions
    (b* (((mv new-st &) (vl-load-descriptions names st state)))
      (implies (uniquep (vl-descriptionlist->names (vl-loadstate->descs st)))
               (no-duplicatesp (vl-descriptionlist->names (vl-loadstate->descs new-st)))))))


(define vl-collect-modules-from-descriptions ((x vl-descriptionlist-p))
  :returns (mods vl-modulelist-p)
  (b* (((when (atom x))
        nil)
       (x1 (vl-description-fix (car x)))
       ((when (eq (tag x1) :vl-module))
        (cons x1 (vl-collect-modules-from-descriptions (cdr x)))))
    (vl-collect-modules-from-descriptions (cdr x))))

(define vl-descriptions-left-to-load ((st vl-loadstate-p))
  :returns (names string-listp)
  :short "Determine which descriptions we still need to load."

  :long "<p>For loading to be completely done, we want to have:</p>

<ul>

<li>All descriptions that the user told us to load in the
@(':start-names'), and</li>

<li>All descriptions that are ever referenced anywhere in any description that
we have already loaded.</li>

</ul>

<p>This function computes the names of descriptions that we want for the above
reasons, but which we do not yet have loaded.  These are the descriptions we'll
need to search for.</p>"

  (b* (((vl-loadstate st) st)
       ((vl-loadconfig config) st.config)

       ;; BOZO.  This will need to be extended when we support other kinds of
       ;; descriptions.  For now we only look for the modules we're missing.
       (current-mods   (vl-collect-modules-from-descriptions st.descs))
       (things-we-want-loaded (mergesort (append config.start-names
                                                 (vl-modulelist-everinstanced current-mods))))
       (things-we-have-loaded (mergesort (vl-descriptionlist->names st.descs))))

    (difference things-we-want-loaded
                things-we-have-loaded)))


(define vl-flush-out-descriptions
  :short "Attempt to find and load any missing modules."
  ((st vl-loadstate-p)
   (n  natp "Counter to force termination.")
   state)
  :returns (mv (st    vl-loadstate-p)
               (state state-p1       :hyp (force (state-p1 state))
                      :hints(("Goal" :in-theory (disable (force))))))

  :long "<p>After some initial files have been loaded, it is generally
necessary to track down and load, e.g., any submodules that have been
referenced but not defined.  We call this process \"flushing out\" the
description list.</p>

<p>To find some description @('foo'), we look through the provided search
directories, in order, for a file whose name is @('foo.v').  (We can also
consider files with other extensions, see the @('search-exts') option in @(see
vl-loadconfig-p).)</p>

<p>We try to load the first such @('foo.v') that we find.  This is <b>not
necessarily sensible</b>.  It might be, for instance, that @('foo.v') will not
define anything named @('foo'), or that it will define all sorts of other
modules instead of @('foo').  In other words, for this search procedure to make
sense, you need to follow a sort of naming discipline and keep descriptions in
files that have appropriate names.</p>

<p>Flushing out the descriptions is necessarily an <b>iterative</b> process.
After we load some library module @('foo'), we might find that it references
some other library module @('bar') that we have not yet loaded.  To ensure that
the process will eventually terminate, so cap the maximum number of times we
will look for new modules.</p>"

  :measure (nfix n)

  (b* ((st      (vl-loadstate-fix st))
       (missing (vl-descriptions-left-to-load st))
       ((unless missing)
        ;; We have everything loaded that we want, so we're all done.
        (mv st state))

       ((when (zp n))
        ;; (cw "Ran out of steps in vl-flush-out-descriptions.~%")
        (mv (vl-loadstate-warn :type :vl-flush-failed
                               :msg "Failed to load description~s0 ~&1 ~
                                     because we reached the maximum number of ~
                                     tries."
                               :args (list (if (vl-plural-p missing) "s" "")
                                           missing))
            state))

       ;; (- (cw "Searching for ~x0 missing modules (~x1 tries left).~%" (length missing) n))

       (num-prev      (len (vl-loadstate->descs st)))
       ((mv st state) (vl-load-descriptions missing st state))
       (num-new       (len (vl-loadstate->descs st)))

       ((when (equal num-prev num-new))
        ;; Failed to load anything new, so we've loaded as much as we can.
        (mv (vl-loadstate-warn :type :vl-search-failed
                               :msg  "Failed to find ~x0 description~s1: ~&2."
                               :args (list (length missing)
                                           (if (vl-plural-p missing) "s" "")
                                           (mergesort missing)))
            state)))

    ;; Else, got at least some modules.  But remember: just because we
    ;; loaded N modules doesn't mean we loaded the ones we needed, and it
    ;; doesn't mean we don't now need new ones!  So don't try to detect
    ;; whether we're successful, just keep flushing out until we stop making
    ;; progress or find everything.
    (vl-flush-out-descriptions st (- n 1) state)))


(defprod vl-loadresult
  :short "Return value from @(see vl-load)."

  ((design      vl-design-p
                "The design that we loaded.  The contents of the design have
                 been only minimally transformed (e.g., to add declarations for
                 implicit wires).  They meant to closely reflect the actual
                 source code as it occurs on the disk.")

   (filemap     vl-filemap-p
                "Alist mapping file names to their original, unmodified
                 contents as strings.  This can be useful for interactively
                 looking at module definitions, but takes some memory.  You can
                 control whether a filemap is generated in your @(see
                 vl-loadconfig-p).")

   (defines     vl-defines-p
                "Final defines that we ended up with.  This can be useful for
                 extracting the values of @('`define')s.  See also @(see
                 scope-of-defines)."))

  :tag :vl-loadresult)


(define vl-load-main
  :short "Top level interface for loading Verilog sources."
  ((config vl-loadconfig-p)
   state)
  :returns (mv (result vl-loadresult-p)
               (state  state-p1        :hyp (force (state-p1 state))))
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

       (pstate (make-vl-parsestate :warnings nil
                                   :usertypes nil))

       (st     (make-vl-loadstate :config     config
                                  :descs      nil
                                  :descalist  nil
                                  :defines    config.defines
                                  :reportcard nil
                                  :pstate     pstate
                                  :filemap    nil))

       ((mv st state)
        (time$ (vl-load-files config.start-files st state)
               :msg "; load start-files: ~st sec, ~sa bytes~%"
               :mintime config.mintime))

       ((mv st state)
        (time$ (vl-flush-out-descriptions st config.flush-tries state)
               :msg "; load missing modules: ~st sec, ~sa bytes~%"
               :mintime config.mintime))

       ;; Final override handling.  Need to add comments to the overridden
       ;; modules and check that all requirements are met.

       ((vl-loadstate st) st)
       (design (vl-design-from-descriptions st.descs))
       (design (vl-apply-reportcard design st.reportcard))
       (design (change-vl-design design
                                 :warnings (append-without-guard (vl-parsestate->warnings st.pstate)
                                                                 (vl-design->warnings design))))
       (result (make-vl-loadresult :design   design
                                   :filemap  st.filemap
                                   :defines  st.defines)))
    (vl-parsestate-free st.pstate)
    (fast-alist-free st.descalist)
    (mv result state)))


(defsection vl-load-summary
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
       ((vl-design result.design) result.design)
       (- (cw "Load Summary:"))
       (- (cw " - ~x0 modules.~%" (len result.design.mods)))
       (- (cw " - ~x0 interfaces.~%" (len result.design.interfaces)))
       (- (cw " - ~x0 packages.~%" (len result.design.packages)))
       (- (cw " - ~x0 programs.~%" (len result.design.programs)))
       (- (cw " - ~x0 configs.~%" (len result.design.configs)))
       (- (cw " - ~x0 user-defined primitives.~%" (len result.design.udps)))

       ;; The warnings get returned, but we also summarize the floating
       ;; warnings as a convenience to whomever is running the translator.
       (regular-warnings (mergesort (vl-design-flat-warnings result.design)))
       (all-warnings     (mergesort (append-without-guard result.design.warnings regular-warnings)))
       (- (or (not all-warnings)
              (cw "Total number of warnings: ~x0.~%" (len all-warnings))))

       (floating-warnings (mergesort result.design.warnings))
       (- (or (not floating-warnings)
              (vl-cw-ps-seq
               (vl-ps-update-autowrap-col 68)
               (vl-cw "~x0 floating warning~s1:~%"
                      (len floating-warnings)
                      (if (vl-plural-p floating-warnings) "s" ""))
               (vl-print-warnings floating-warnings)
               (vl-println ""))))

       (multidef-warnings (vl-keep-warnings '(:vl-warn-multidef) regular-warnings))
       (- (or (not multidef-warnings)
              (vl-cw-ps-seq
               (vl-ps-update-autowrap-col 68)
               (vl-cw "~x0 multiply defined module warning~s1:~%"
                      (len multidef-warnings)
                      (if (vl-plural-p multidef-warnings) "s" ""))
               (vl-print-warnings multidef-warnings)
               (vl-println "")))))
    nil))

(defattach vl-load-summary vl-default-load-summary)

(define vl-load ((config vl-loadconfig-p)
                 &key
                 (state 'state))
  :short "Wrapper for @(see vl-load-main) that also reports errors or (with
some configuration) can print other information."

  :long "<p>This is very similar to @(see vl-load-main), but calls @(see
vl-load-summary) afterwards.</p>"

  :returns (mv (result vl-loadresult-p)
               (state  state-p1        :hyp (force (state-p1 state))))
  (b* (((vl-loadconfig config) (vl-loadconfig-clean config))
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
