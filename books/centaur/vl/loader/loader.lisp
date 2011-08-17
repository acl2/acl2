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
(include-book "../util/cwtime")
(include-book "../util/gc")
(include-book "centaur/misc/hons-extra" :dir :system)
(include-book "defsort/duplicated-members" :dir :system)
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))


(defxdoc loader
  :parents (vl)
  :short "How we read Verilog source files and convert them into @(see
modules)."

  :long "<p>Our top-level function for loading Verilog sources is @(see
vl-load).  For any particular source file, the process is roughly as
follows:</p>

<ul>

<li>We use @(see vl-read-file) to read the file from disk and convert it into a
list of @(see extended-characters) in memory.</li>

<li>The @(see preprocessor) then expands away compiler directives such as
<tt>`define</tt>, producing a new list of characters.</li>

<li>The @(see lexer) tokenizes this character list into a list of @(see
vl-token-p)s.</li>

<li>Any applicable @(see overrides) are applied.</li>

<li>The @(see parser) transforms the token list into a list of @(see
vl-module-p)s, our internal module representation.</li>

</ul>

<p>The @(see vl-load) function manages this process and deals with searching
for modules in other files.</p>")

(defsection vl-load-file
  :parents (vl-load)
  :short "Load an individual file."

  :long "<p><b>Signature:</b> @(call vl-load-file) returns
<tt>(mv successp mods filemap oused mtokens defines warnings walist state)</tt></p>

<p>This is our main file-loading routine.  The filename to load and initial
defines to use have already been provided.  We read the file, preprocess it,
lex it, clean it up by removing whitespace and comments, apply any overrides,
and finally parse it into a list of modules.</p>"

  (defund vl-load-file (filename include-dirs defines overrides warnings walist filemapp state)
    "Returns (MV SUCCESSP MODS FILEMAP OUSED MTOKENS DEFINES WARNINGS WALIST STATE)"
    (declare (xargs :guard (and (stringp filename)
                                (string-listp include-dirs)
                                (vl-defines-p defines)
                                (vl-warninglist-p warnings)
                                (vl-override-db-p overrides)
                                (vl-modwarningalist-p walist)
                                (booleanp filemapp))
                    :stobjs state))
    (b* (((mv contents state)
          (cwtime (vl-read-file (string-fix filename) state)
                  :mintime 1/2))

         ((when (stringp contents))
          (mv nil nil nil nil nil defines
              (cons (make-vl-warning :type :vl-read-failed
                                     :msg "Error reading file ~s0."
                                     :args (list filename)
                                     :fn 'vl-load-file)
                    warnings)
              walist state))

         (filemap (and filemapp
                       (list (cons filename (vl-echarlist->string contents)))))

         ((mv successp defines preprocessed state)
          (cwtime (vl-preprocess contents defines include-dirs state)
                  :mintime 1/2))

         ((unless successp)
          (mv nil nil filemap nil nil defines
              (cons (make-vl-warning :type :vl-preprocess-failed
                                     :msg "Preprocessing failed for ~s0."
                                     :args (list filename)
                                     :fn 'vl-load-file)
                    warnings)
              walist state))

         ((mv successp lexed warnings)
          (cwtime (vl-lex preprocessed warnings)
                  :mintime 1))

         ((unless successp)
          (mv nil nil filemap nil nil defines
              (cons (make-vl-warning :type :vl-lex-failed
                                     :msg "Lexing failed for ~s0."
                                     :args (list filename)
                                     :fn 'vl-load-file)
                    warnings)
              walist state))

         ((mv cleaned comment-map)
          (cwtime (vl-kill-whitespace-and-comments lexed)
                  :mintime 1))

         ((mv walist cleaned oused mtokens)
          (cwtime (vl-apply-overrides cleaned overrides walist)
                  :mintime 1))

         ((mv successp mods warnings)
          (cwtime (vl-parse cleaned warnings)
                  :mintime 1))

         ((when (not successp))
          ;; I think we want to not include oused and mtokens here, since
          ;; the parsing failed and we're not building any modules.
          (mv nil nil filemap nil nil defines
              (cons (make-vl-warning :type :vl-parse-failed
                                     :msg "Parsing failed for ~s0."
                                     :args (list filename)
                                     :fn 'vl-load-file)
                    warnings)
              walist state))

         (mods  (cwtime (vl-inject-comments-modulelist mods comment-map)
                        :mintime 1/2)))

      (mv t mods filemap oused mtokens defines warnings walist state)))

  (local (in-theory (enable vl-load-file)))

  (defmvtypes vl-load-file
    (booleanp true-listp true-listp true-listp true-listp nil))

  (defthm state-p1-of-vl-load-file
    (implies (force (state-p1 state))
             (state-p1
              (mv-nth 8 (vl-load-file filename include-dirs defines overrides warnings walist
                                      filemapp state)))))

  (defthm vl-load-file-basics
    (implies
     (and (force (stringp filename))
          (force (string-listp include-dirs))
          (force (vl-defines-p defines))
          (force (vl-override-db-p overrides))
          (force (vl-warninglist-p warnings))
          (force (vl-modwarningalist-p walist))
          (force (state-p state)))
     (let ((result (vl-load-file filename include-dirs defines overrides warnings walist
                                 filemapp state)))
       (and (vl-modulelist-p      (mv-nth 1 result))
            (vl-filemap-p         (mv-nth 2 result))
            (vl-overridelist-p    (mv-nth 3 result))
            (vl-modtokensalist-p  (mv-nth 4 result))
            (vl-defines-p         (mv-nth 5 result))
            (vl-warninglist-p     (mv-nth 6 result))
            (vl-modwarningalist-p (mv-nth 7 result)))))))



(defsection vl-load-files
  :parents (vl-load)
  :short "Extend @(see vl-load-file) for a list of files."

  :long "<p><b>Signature:</b> @(call vl-load-files) returns <tt>(mv successp
mods filemap oused mtokens defines warnings walist state)</tt>.</p>

<p>We just call @(see vl-load-file) on each file in <tt>filenames</tt> and
append together all of the modules, origsrc entries, and warnings which
result.</p>

<p>In this function, <tt>successp</tt> indicates if <b>all</b> of the files
were loaded successfully.  But even if <tt>successp</tt> is <tt>nil</tt>, the
resulting module-list may contain at least some partial results.  That is, we
try to load as much as possbile, even in the face of errors in some files.</p>"

  (defund vl-load-files (filenames include-dirs defines overrides warnings walist filemapp state)
    "Returns (MV SUCCESSP MODS FILEMAP OUSED MTOKENS DEFINES WARNINGS WALIST STATE)"
    (declare (xargs :guard (and (string-listp filenames)
                                (string-listp include-dirs)
                                (vl-defines-p defines)
                                (vl-override-db-p overrides)
                                (vl-warninglist-p warnings)
                                (vl-modwarningalist-p walist)
                                (booleanp filemapp))
                    :stobjs state))
    (if (atom filenames)
        (mv t nil nil nil nil defines warnings walist state)
      (b* (((mv car-successp car-mods car-filemap car-oused car-mtokens
                defines warnings walist state)
            (vl-load-file (car filenames) include-dirs defines overrides warnings walist
                          filemapp state))
           ((mv cdr-successp cdr-mods cdr-filemap cdr-oused cdr-mtokens
                defines warnings walist state)
            (vl-load-files (cdr filenames) include-dirs defines overrides warnings walist
                           filemapp state)))
        (mv (and car-successp cdr-successp)
            (append car-mods cdr-mods)
            (append car-filemap cdr-filemap)
            (append car-oused cdr-oused)
            (append car-mtokens cdr-mtokens)
            defines
            warnings
            walist
            state))))

  (local (in-theory (enable vl-load-files)))

  (defmvtypes vl-load-files
    (booleanp true-listp true-listp true-listp true-listp nil))

  (defthm state-p1-of-vl-load-files
    (implies (force (state-p1 state))
             (state-p1
              (mv-nth 8 (vl-load-files filenames include-dirs defines overrides warnings walist
                                       filemapp state)))))

  (defthm vl-load-files-basics
    (implies
     (and (force (string-listp filenames))
          (force (string-listp include-dirs))
          (force (vl-defines-p defines))
          (force (vl-override-db-p overrides))
          (force (vl-warninglist-p warnings))
          (force (vl-modwarningalist-p walist))
          (force (state-p state)))
     (let ((result (vl-load-files filenames include-dirs defines overrides warnings walist
                                  filemapp state)))
       (and (vl-modulelist-p      (mv-nth 1 result))
            (vl-filemap-p         (mv-nth 2 result))
            (vl-overridelist-p    (mv-nth 3 result))
            (vl-modtokensalist-p  (mv-nth 4 result))
            (vl-defines-p         (mv-nth 5 result))
            (vl-warninglist-p     (mv-nth 6 result))
            (vl-modwarningalist-p (mv-nth 7 result)))))))



(defsection vl-load-module
  :parents (vl-load)
  :short "Try to load a module from the search path."

  :long "<p><b>Signature:</b> @(call vl-load-module) returns <tt>(mv successp
mods filemap oused mtokens defines warnings walist state)</tt>.</p>

<p>This is a thin wrapper around @(see vl-load-file) which, instead of taking a
filename, takes a module name, e.g., \"foo\", and uses the search path to
decide where the corresponding \"foo.v\" file is.</p>

<p>The search is controlled by the <tt>searchpath</tt>, which is a list of
strings.  We look for a file named <tt>foo.v</tt> in each directory in the
search path, and try to process the first such file that we find using
@(see vl-load-file).</p>

<p>Note that this process can lead us to load any additional modules besides
<tt>foo</tt> that happen to be defined in <tt>foo.v</tt>.  Also, if
<tt>foo.v</tt> does not actually include a definition for <tt>foo</tt>, this
may not yield <tt>foo</tt> at all.</p>

<p>In other words, the successful return of this function only actually results
in a module <tt>foo</tt> being loaded if the logic designers are disciplined in
their file naming.</p>"

  (defund vl-load-module (modname searchpath searchext include-dirs defines overrides
                                  warnings walist filemapp state)
    "Returns (MV SUCCESSP MODS FILEMAP OUSED MTOKENS DEFINES WARNINGS WALIST STATE)"
    (declare (xargs :guard (and (stringp modname)
                                (string-listp searchpath)
                                (string-listp searchext)
                                (string-listp include-dirs)
                                (vl-defines-p defines)
                                (vl-override-db-p overrides)
                                (vl-warninglist-p warnings)
                                (vl-modwarningalist-p walist)
                                (booleanp filemapp))
                    :stobjs state))
    (b* (((mv filename warnings state)
          (vl-find-basename/extension modname searchext searchpath warnings state))
         ((unless filename)
          (mv nil nil nil nil nil defines
              (cons (make-vl-warning :type :vl-warn-find-failed
                                     :msg "Unable to find module ~s0."
                                     :args (list modname)
                                     :fn 'vl-load-module)
                    warnings)
              walist state)))
      (vl-load-file filename include-dirs defines overrides warnings walist filemapp state)))

  (local (in-theory (enable vl-load-module)))

  (defmvtypes vl-load-module
    (booleanp true-listp true-listp true-listp true-listp nil))

  (defthm state-p1-of-vl-load-module
    (implies (force (state-p1 state))
             (state-p1
              (mv-nth 8 (vl-load-module modname searchpath searchext include-dirs defines overrides
                                        warnings walist filemapp state)))))

  (defthm vl-load-module-basics
    (implies
     (and (force (stringp modname))
          (force (string-listp searchpath))
          (force (string-listp searchext))
          (force (string-listp include-dirs))
          (force (vl-defines-p defines))
          (force (vl-override-db-p overrides))
          (force (vl-warninglist-p warnings))
          (force (vl-modwarningalist-p walist))
          (force (state-p state)))
     (let ((result (vl-load-module modname searchpath searchext include-dirs defines overrides
                                   warnings walist filemapp state)))
       (and (vl-modulelist-p      (mv-nth 1 result))
            (vl-filemap-p         (mv-nth 2 result))
            (vl-overridelist-p    (mv-nth 3 result))
            (vl-modtokensalist-p  (mv-nth 4 result))
            (vl-defines-p         (mv-nth 5 result))
            (vl-warninglist-p     (mv-nth 6 result))
            (vl-modwarningalist-p (mv-nth 7 result)))))))




(defsection vl-load-modules
  :parents (vl-load)
  :short "Extend @(see vl-load-module) to a list of modules."

  :long "<p><b>Signature:</b> @(call vl-load-modules) returns <tt>(mv successp
mods filemap oused mtokens defines warnings walist state)</tt>.</p>

<p>As with @(see vl-load-filenames), here <tt>successp</tt> indicates whether
<b>all</b> of the files were loaded successfully.  Even if <tt>successp</tt> is
<tt>nil</tt>, the resulting mods may contain at least some of the modules.
That is, we try to load as much as possible, even in the face of errors.</p>

<p>Note that as in @(see vl-load-module), a successful return does not
necessarily indicate that we have loaded modules of the desired names, and we
may also load additional modules.  See the comments in @(see vl-load-module)
for details.</p>"

  (defund vl-load-modules (modnames searchpath searchext include-dirs defines overrides
                                    warnings walist filemapp state)
    "Returns (MV SUCCESSP MODS FILEMAP DEFINES WARNINGS WALIST STATE)"
    (declare (xargs :guard (and (string-listp modnames)
                                (string-listp searchpath)
                                (string-listp searchext)
                                (string-listp include-dirs)
                                (vl-defines-p defines)
                                (vl-override-db-p overrides)
                                (vl-warninglist-p warnings)
                                (vl-modwarningalist-p walist)
                                (booleanp filemapp))
                    :stobjs state))

    (if (atom modnames)
        (mv t nil nil nil nil defines warnings walist state)
      (b* (((mv car-successp car-mods car-filemap car-oused car-mtokens
                defines warnings walist state)
            (vl-load-module (car modnames) searchpath searchext include-dirs defines overrides
                            warnings walist filemapp state))
           ((mv cdr-successp cdr-mods cdr-filemap cdr-oused cdr-mtokens
                defines warnings walist state)
            (vl-load-modules (cdr modnames) searchpath searchext include-dirs defines overrides
                             warnings walist filemapp state)))
        (mv (and car-successp cdr-successp)
            (append car-mods cdr-mods)
            (append car-filemap cdr-filemap)
            (append car-oused cdr-oused)
            (append car-mtokens cdr-mtokens)
            defines
            warnings
            walist
            state))))

  (local (in-theory (enable vl-load-modules)))

  (defmvtypes vl-load-modules
    (booleanp true-listp true-listp true-listp true-listp nil))

  (defthm state-p1-of-vl-load-modules
    (implies (force (state-p1 state))
             (state-p1
              (mv-nth 8 (vl-load-modules modnames searchpath searchext include-dirs defines overrides
                                         warnings walist filemapp state)))))

  (defthm vl-load-modules-basics
    (implies
     (and (force (string-listp modnames))
          (force (string-listp searchpath))
          (force (string-listp searchext))
          (force (string-listp include-dirs))
          (force (vl-defines-p defines))
          (force (vl-override-db-p overrides))
          (force (vl-warninglist-p warnings))
          (force (vl-modwarningalist-p walist))
          (force (state-p state)))
     (let ((result (vl-load-modules modnames searchpath searchext include-dirs defines overrides
                                    warnings walist filemapp state)))
       (and (vl-modulelist-p      (mv-nth 1 result))
            (vl-filemap-p         (mv-nth 2 result))
            (vl-overridelist-p    (mv-nth 3 result))
            (vl-modtokensalist-p  (mv-nth 4 result))
            (vl-defines-p         (mv-nth 5 result))
            (vl-warninglist-p     (mv-nth 6 result))
            (vl-modwarningalist-p (mv-nth 7 result)))))))



(defsection vl-flush-out-modules
  :parents (vl-load)
  :short "Attempt to find and load any missing modules."

  :long "<p><b>Signature:</b> @(call vl-flush-out-modules) returns <tt>(mv
successp mods filemap oused mtokens defines warnings walist state)</tt>.</p>

<p>After some initial files have been loaded, it is generally necessary to
track down and load any submodules that have been referenced but not defined.
We call this process \"flushing out\" the module list.</p>

<p>Note that flushing out the modules is an iterative process.  That is, after
we load some missing module, we might find that it references other missing
modules that will also need to be loaded.</p>

<p>One could probably argue that flushing out will reach a fixed point so long
as the file system is finite.  But there isn't any good way to argue that this
function terminates within the ACL2 logic, so we simply cap the maximum number
of times we will look for new modules with the counter <tt>n</tt>.</p>

<p>We return successfully only if, after some number of iterations, we arrive
at a <see topic=\"@(url completeness)\">complete</see> module list, i.e., one
where every referenced module is defined.</p>

<p>However, even when <tt>successp</tt> is <tt>nil</tt>, there may be many
useful modules in the module list.  We return everything we were able to parse.
You can get a complete subset of these modules by, e.g., using @(see
vl-remove-bad-modules) to eliminate all of the modules named by @(see
vl-modulelist-missing).</p>"

  ;; speed hint
  (local (in-theory (disable consp-under-iff-when-true-listp
                             vl-modulelist-p-when-subsetp-equal
                             vl-warninglist-p-when-subsetp-equal
                             mergesort
                             difference
                             length
                             subsetp-equal-when-first-two-same-yada-yada
                             vl-overridelist-p-when-subsetp-equal
                             consp-when-member-equal-of-cons-listp
                             (:ruleset tag-reasoning)
                             append-when-not-consp
                             consp-by-len
                             sets::nonempty-means-set
                             string-listp-when-subsetp-equal-of-string-listp
                             )))


  (defund vl-flush-out-modules (mods start-modnames searchpath searchext include-dirs defines overrides
                                     required warnings walist filemapp state n)
    "Returns (MV SUCCESSP MODS FILEMAP OUSED MTOKENS DEFINES WARNINGS WALIST STATE)"
    (declare (xargs :guard (and (vl-modulelist-p mods)
                                (true-listp mods)
                                (string-listp start-modnames)
                                (string-listp searchpath)
                                (string-listp searchext)
                                (string-listp include-dirs)
                                (vl-defines-p defines)
                                (vl-override-db-p overrides)
                                ;; The modules required by overrides
                                (string-listp required)
                                (vl-warninglist-p warnings)
                                (vl-modwarningalist-p walist)
                                (booleanp filemapp)
                                (natp n))
                    :stobjs state
                    :measure (nfix n)))
    (b* ( ;; Before we introduced overrides, we just determined which modules
         ;; were missing with (vl-modulelist-missing).  But now, we also need
         ;; to try to find the current definitions for any modules that are
         ;; "required" by overrides and not yet loaded.
         (mentioned (mergesort (append start-modnames
                                       (vl-modulelist-everinstanced-exec mods required))))
         (defined   (mergesort (vl-modulelist->names-exec mods nil)))
         (missing   (difference mentioned defined))

         ((unless missing)
;          (cw "No modules are missing; stopping.~%")
          (mv t mods nil nil nil defines warnings walist state))

         ((when (zp n))
          (cw "Ran out of steps in vl-flush-out-modules.~%")
          (mv nil mods nil nil nil defines
              (cons (make-vl-warning
                     :type :vl-flush-failed
                     :msg "Ran out of steps for flushing out modules."
                     :args nil
                     :fn 'vl-flush-out-modules)
                    warnings)
              walist state))

;         (- (cw "Searching for ~x0 missing modules (~x1 tries left).~%"
;                (length missing) n))

         ((mv successp new-mods new-filemap new-oused new-mtokens
              defines warnings walist state)
          (vl-load-modules missing searchpath searchext include-dirs defines overrides
                           warnings walist filemapp state))

         ;; When we switched to the new overrides system, we found that we
         ;; needed to be careful to make sure the new modules aren't the exact
         ;; same ones we've seen before, or this could get into a bad loop.
         (new-mods (set-difference-equal new-mods mods))

;         (- (cw "Found ~x0 new modules in this iteration.~%" (len new-mods)))
         ((unless new-mods)
          ;; We check the module list, not successp, because we want to keep
          ;; going as long as some new things were found, even if some files have
          ;; problems.
;          (cw "Stopping since no new modules were found.~%")
          (mv nil mods new-filemap new-oused new-mtokens defines
              (cons (make-vl-warning
                     :type :vl-search-failed
                     :msg "~x0 module~s1 could not be found: ~&2."
                     :args (list (length missing)
                                 (if (= (length missing) 1) "" "s")
                                 (mergesort missing))
                     :fatalp nil
                     :fn 'vl-flush-out-modules)
                    warnings)
              walist state))

         (required (vl-overridelist-requirement-names-exec new-oused required))

         ;; We previously tried to defend against multiply-defined modules here.
         ;; But in our new scheme, we permit multiple definitions and throw away
         ;; the subsequent ones during vl-simplify-part1.  So, we no longer need
         ;; to do anything here.  The new scheme is really nice for being able to
         ;; override modules.

         ((mv rest-successp rest-mods rest-filemap rest-oused rest-mtokens
              defines warnings walist state)
          (vl-flush-out-modules (append mods new-mods) start-modnames
                                searchpath searchext include-dirs defines overrides required
                                warnings walist filemapp state (- n 1))))

      (mv (and successp rest-successp)
          rest-mods
          (append new-filemap rest-filemap)
          (append new-oused rest-oused)
          (append new-mtokens rest-mtokens)
          defines
          warnings
          walist
          state)))

  (local (in-theory (enable vl-flush-out-modules)))

; (local (in-theory (disable vl-modulelist-everinstanced-exec-removal)))
  (local (in-theory (disable (force))))

  (defthm booleanp-of-vl-flush-out-modules-0
    (booleanp
     (mv-nth 0 (vl-flush-out-modules mods start-modnames searchpath searchext include-dirs defines overrides required
                                     warnings walist filemapp state n)))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-flush-out-modules-1
    (implies (true-listp mods)
             (true-listp
              (mv-nth 1 (vl-flush-out-modules mods start-modnames searchpath searchext include-dirs defines overrides required
                                              warnings walist filemapp state n))))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-flush-out-modules-2
    (true-listp
     (mv-nth 2 (vl-flush-out-modules mods start-modnames searchpath searchext include-dirs defines overrides required
                                     warnings walist filemapp state n)))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-flush-out-modules-3
    (implies (true-listp mods)
             (true-listp
              (mv-nth 3 (vl-flush-out-modules mods start-modnames searchpath searchext include-dirs defines overrides required
                                              warnings walist filemapp state n))))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-flush-out-modules-4
    (true-listp
     (mv-nth 4 (vl-flush-out-modules mods start-modnames searchpath searchext include-dirs defines overrides required
                                     warnings walist filemapp state n)))
    :rule-classes :type-prescription)

  (defthm state-p1-of-vl-flush-out-modules
    (implies (force (state-p1 state))
             (state-p1
              (mv-nth 8 (vl-flush-out-modules mods start-modnames searchpath searchext include-dirs defines overrides required
                                              warnings walist filemapp state n)))))

  (local (in-theory (enable (force))))

  (local (in-theory (disable mergesort difference string-listp
                             true-listp symbol-listp
                             set-difference-equal-when-subsetp-equal
                             true-listp-when-symbol-listp)))

  (defthm vl-flush-out-modules-basics
    (implies
     (and (force (vl-modulelist-p mods))
          (force (true-listp mods))
          (force (string-listp start-modnames))
          (force (string-listp searchpath))
          (force (string-listp searchext))
          (force (string-listp include-dirs))
          (force (vl-defines-p defines))
          (force (vl-override-db-p overrides))
          (force (string-listp required))
          (force (vl-warninglist-p warnings))
          (force (vl-modwarningalist-p walist))
          (force (state-p state)))
     (let ((result (vl-flush-out-modules mods start-modnames searchpath searchext include-dirs defines overrides required
                                         warnings walist filemapp state n)))
       (and (vl-modulelist-p      (mv-nth 1 result))
            (vl-filemap-p         (mv-nth 2 result))
            (vl-overridelist-p    (mv-nth 3 result))
            (vl-modtokensalist-p  (mv-nth 4 result))
            (vl-defines-p         (mv-nth 5 result))
            (vl-warninglist-p     (mv-nth 6 result))
            (vl-modwarningalist-p (mv-nth 7 result)))))))




(defsection vl-handle-multidef-mods
  :parents (vl-simplify)
  :short "Add warnings about modules with multiple definitions, and throw away
all but the first definition of any multiply-defined module."

  :long "<p><b>Signature:</b> @(call vl-handle-multidef-mods) returns
<tt>(mv x-prime warnings)</tt>.</p>

<p>The new list of modules, <tt>x-prime</tt>, has uniquely named modules and is
formed by removing from <tt>x</tt> all but the first definition of any module
that has been encountered.  Non-fatal warnings are also added to any surviving
modules which had multiple definitions.</p>

<p>The list of <tt>warnings</tt> contains no additional information, but merely
collects up the warnings that have been added to modules in <tt>x</tt>.</p>"

  (defund vl-gather-multidef-locstrings (name mods)
    "Returns a string list."
    (declare (xargs :guard (and (stringp name)
                                (vl-modulelist-p mods))))
    (cond ((atom mods)
           nil)
          ((equal name (vl-module->name (car mods)))
           (cons (vl-location-string (vl-module->minloc (car mods)))
                 (vl-gather-multidef-locstrings name (cdr mods))))
          (t
           (vl-gather-multidef-locstrings name (cdr mods)))))

  (defund vl-add-multidef-warnings (x names mods)
    "Returns (MV X-PRIME WARNINGS)"
    (declare (xargs :guard (and (vl-modulelist-p x)
                                (string-listp names)
                                (vl-modulelist-p mods))))
    (b* (((when (atom x))
          (mv nil nil))

         ((mv cdr-prime warnings)
          (vl-add-multidef-warnings (cdr x) names mods))

         (car  (car x))
         (name (vl-module->name car))
         ((unless (member-equal name names))
          (mv (cons car cdr-prime) warnings))

         (car-warning (make-vl-warning
                       :type :vl-multidef-mod
                       :msg "~m0 is defined multiple times, so we are keeping only ~
                           the definition which occurs at ~l1.  The definition(s) ~
                           from ~&2 have been discarded!"
                       :args (list name
                                   (vl-module->minloc car)
                                   (remove-equal
                                    (vl-location-string (vl-module->minloc car))
                                    (vl-gather-multidef-locstrings name mods)))
                       :fn 'vl-add-multidef-warnings))
         (car-warnings (cons car-warning (vl-module->warnings car)))
         (car-prime    (change-vl-module car :warnings car-warnings)))
        (mv (cons car-prime cdr-prime)
            (cons car-warning warnings))))

  (defmvtypes vl-add-multidef-warnings (true-listp true-listp))

  (defthm vl-modulelist-p-of-vl-add-multidef-warnings
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (mv-nth 0 (vl-add-multidef-warnings x names mods))))
    :hints(("Goal" :in-theory (enable vl-add-multidef-warnings))))

  (defthm vl-warninglist-p-of-vl-add-multidef-warnings
    (vl-warninglist-p (mv-nth 1 (vl-add-multidef-warnings x names mods)))
    :hints(("Goal" :in-theory (enable vl-add-multidef-warnings))))


  (defund vl-remove-multidef-modules (names seen x)
    "Returns X-PRIME"
    (declare (xargs :guard (and (string-listp names)
                                (string-listp seen)
                                (vl-modulelist-p x))))
    ;; Remove all but the first instance of names.  NAMES are the names of all
    ;; multiply-defined modules.  SEEN are those members of NAMES we have already
    ;; encountered.
    (if (atom x)
        nil
      (let ((name (vl-module->name (car x))))
        (cond ((not (member-equal name names))
               ;; Not multiply defined, so keep it.
               (cons (car x)
                     (vl-remove-multidef-modules names seen (cdr x))))

              ((not (member-equal name seen))
               ;; Multiply-defined, but this is the first time we've seen it.  Keep
               ;; this occurrence and add name to the seen list.
               (cons (car x)
                     (vl-remove-multidef-modules names (cons name seen) (cdr x))))

              (t
               ;; Multiply-defined, and already seen.  Skip it.
               (vl-remove-multidef-modules names seen (cdr x)))))))

  (defthm vl-modulelist-p-of-vl-remove-multidef-modules
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-remove-multidef-modules names seen x)))
    :hints(("Goal" :in-theory (enable vl-remove-multidef-modules))))

  (defund vl-handle-multidef-mods (x)
    "Returns (MV X-PRIME WARNINGS)"
    (declare (xargs :guard (vl-modulelist-p x)))
    (b* ((names (vl-modulelist->names x))
         ((when (cwtime (uniquep names)
                        :name check-unique-names
                        :mintime 1/2))
          (mv x nil))
         (dupes   (duplicated-members names))
         ;; First eliminate any shadowed modules
         (x-clean (vl-remove-multidef-modules dupes nil x))
         ;; Now add warnings about any shadowed modules
         ((mv x-prime warnings)
          (vl-add-multidef-warnings x-clean dupes x)))
        ;; This is kind of gross.  Explicitly check that our handling worked to
        ;; eliminate any duplicated modules.  Eventually one might try to prove
        ;; this never happens, and hence avoid the check.
        (if (uniquep (vl-modulelist->names x-prime))
            (mv x-prime warnings)
          (prog2$
           (er hard? 'vl-handle-multidef-mods
               "Programming error.  Expected names to be unique.")
           (mv nil warnings)))))

  (local (in-theory (enable vl-handle-multidef-mods)))

  (defthm true-listp-of-vl-handle-multidef-mods-0
    (implies (true-listp x)
             (true-listp (mv-nth 0 (vl-handle-multidef-mods x))))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-handle-multidef-mods-1
    (true-listp (mv-nth 1 (vl-handle-multidef-mods x)))
    :rule-classes :type-prescription)

  (defthm vl-modulelist-p-of-vl-handle-multidef-mods
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (mv-nth 0 (vl-handle-multidef-mods x)))))

  (defthm vl-warninglist-p-of-vl-handle-multidef-mods
    (vl-warninglist-p (mv-nth 1 (vl-handle-multidef-mods x))))

  (defthm no-duplicatesp-equal-of-vl-modulelist->names-of-vl-handle-multidef-mods
    (no-duplicatesp-equal
     (vl-modulelist->names
      (mv-nth 0 (vl-handle-multidef-mods x))))))



(defsection scope-of-defines
  :parents (loader)
  :short "How VL and other tools handle the scope of <tt>`defines</tt>."

  :long "<p><i>What is the scope of a <tt>`define</tt>?</i></p>

<p>Until the end of 2009, we treated <tt>`define</tt>s as having file-scope,
and processed every file using only the initial <tt>define</tt>s to begin with.
But now we are treating <tt>`define</tt>s as cumulative, allowing them to spill
over from one file into the next.  This is convenient in that it allows us to
see what defines have been encountered, and hence we can programmatically
extract the values associated with particular <tt>`define</tt> symbols.</p>

<p>This is scary.  The order of file loading is not especially predictable when
@(see vl-flush-out-modules) is used, so different things might happen depending
on which files happen to get loaded first!</p>

<p>Well, our behavior appears to be at least similar to what other Verilog
tools do.  We found that, on both Verilog-XL and NCVerilog,</p>

<ul>

<li><tt>`define</tt>s that occur before an <tt>`include</tt> do seem to carry
over into the included file.</li>

<li>When we give the tool multiple files, e.g., <tt>verilog foo.v bar.v</tt> or
<tt>ncverilog foo.v bar.v</tt>, the includes from the earlier files do carry
over to the later files.  Hence, switching the argument order can affect
simulation results.</li>

<li><tt>`define</tt>s that occur in the main files (those that are given as
explicit command line arguments) are indeed carried over into library
files</li>

<li><tt>`define</tt>s from earlier-loaded library files are carried over into
later-loaded library files.</li>

</ul>

<p>Our behavior is <b>approximately</b> the same.  However, it seems very
likely that our particular way of loading missing modules with @(see
vl-flush-out-modules) will be at least somewhat different from how other tools
look for missing modules.  Roughly, after parsing the main files, we figure out
what modules are missing and try to load them in alphabetical order.  Other
tools probably use different orders and may produce very different
behaviors.</p>

<p>BOZO we could probably defend against this by tracking which <tt>ifdef</tt>
tests have ever been considered and what their values are.  If we find that two
files have ever done an <tt>ifdef</tt> and gotten different results, we could
add a warning that maybe something is amiss with file loading.</p>")



(defsection vl-load
  :parents (loader)
  :short "Top level interface for loading Verilog sources."

  :long "<p><b>Signature:</b> @(call vl-load) returns <tt>(mv successp mods
filemap defines warnings state)</tt></p>

<h5>Inputs</h5>

<ul>

<li><tt>override-dirs</tt> give the directories to find any @(see overrides)
that you wish to use.</li>

<li><tt>start-files</tt> is a list of file names (not module names) that you
want to load.  We begin by trying to read, preprocess, lex, and parse the
contents of these files.</li>

<li><tt>start-modnames</tt> is a list of module names that you want to load.
We look for these in the search path unless they are defined after we have
loaded the <tt>start-files</tt>.</li>

<li><tt>search-path</tt> is a list of directories that may contain additional
Verilog files.  After we load the <tt>start-files</tt>, we will start looking
for any <see topic=\"@(url vl-modulelist-missing)\">missing modules</see> in
the search path.  This is similar to the \"library directories\" of tools like
Verilog-XL and NCVerilog; see @(see vl-load-module) and @(see
vl-flush-out-modules) for details.</li>

<li><tt>searchext</tt> is a list of file extensions to consider Verilog files
when looking in the <tt>search-path</tt>.  The default is <tt>(\"v\")</tt>,
meaning that only files such as <tt>foo.v</tt> are considered.</li>

<li><tt>include-dirs</tt> is a list of directories that will be searched when
<tt>`include</tt> directives are encountered.  This is similar to the \"include
directories\" for Verilog-XL.  Any includes with relative path names are
searched for in (1) the current directory, then (2) these include dirs, in the
specified order.</li>

<li><tt>defines</tt> is a @(see vl-defines-p) alist which will be given to the
@(see preprocessor), and can be used to set up any initial <tt>`defines</tt>
that you want to use.  See also @(see scope-of-defines).</li>

<li><tt>filemapp</tt> is a flag that says whether to generate a filemap; see
below where we describe the <tt>filemap</tt> output.</li>

<li><tt>state</tt> is the ACL2 state stobj, which is needed since this
function reads from files.</li>

</ul>

<h5>Outputs</h5>

<ul>

<li><tt>successp</tt> indicates whether all modules were loaded successfully.
Even when <tt>successp</tt> is <tt>nil</tt>, there may be at least some
portion of the modules that have been loaded successfully.</li>

<li><tt>mods</tt> are our representation of any @(see modules) that have been
successfully parsed from the files.  The modules have not been transformed, and
is intended to capture the actual source code as it occurs on the disk.  The
modules in the list are guaranteed to have unique names.  To accomplish this,
we keep only the first definition of any module we encounter.</li>

<li><tt>filemap</tt> is an ordinary alist that maps filenames to their
contents; see @(see vl-filemap-p).  This alist is only constructed if
<tt>filemapp</tt> is <tt>t</tt>.</li>

<li><p><tt>defines</tt> is an updated @(see vl-defines-p) alist, which represents
the final list of define bindings at the end of the loading process.</p>

</li>

<li><tt>warnings</tt> are any \"floating\" @(see warnings) that were generated
during the loading process.  Note that most warnings generated during the
parsing of modules are automatically associated with their modules, and these
warnings are <i>not</i> included.  Instead, this list will have warnings
generated in the early stages of file loading, such as preprocessing and
lexing, and perhaps any warnings about malformed syntax that occurs
<i>between</i> modules, etc.</li>

</ul>"

  (defmacro vl-load (&key override-dirs start-files start-modnames
                          search-path
                          (searchext ''("v"))
                          include-dirs defines filemapp)
    `(vl-load-fn ,override-dirs ,start-files ,start-modnames
                 ,search-path ,searchext ,include-dirs
                 ,defines ,filemapp state))

  (defund vl-load-fn (override-dirs start-files start-modnames
                                    search-path searchext include-dirs
                                    defines filemapp state)
    "Returns (MV SUCCESSP MODS FILEMAP DEFINES WARNINGS STATE)"
    (declare (xargs :guard (and (string-listp override-dirs)
                                (string-listp start-files)
                                (string-listp start-modnames)
                                (string-listp search-path)
                                (string-listp searchext)
                                (string-listp include-dirs)
                                (vl-defines-p defines)
                                (booleanp filemapp))
                    :guard-debug t
                    :stobjs state))
    (mv-let (successp mods filemap defines warnings state)

      ;; Kind of subtle -- we do all the computation inside this mv-let body,
      ;; so that all of the local variables we bind here go out of scope before
      ;; we garbage collect at the end of this function.  This is particularly
      ;; important for the oused and mtokens stuff, since those can be become
      ;; really giant lists of tokens that we really want to be freed.
      (b* ((warnings    nil)

           (include-dirs
            ;; I'm pretty sure this is the right thing to do.  I've done a few
            ;; simple tests, and both Verilog-XL and NCVerilog seem to always
            ;; include files from the current directory first, even if +incdir
            ;; arguments are given, and even if there is a +incdir argument
            ;; that comes before an explicit +incdir+. or +incdir+`pwd`.  So,
            ;; it seems like "." is always implicitly the first place to search
            ;; for includes.
            (cons "." include-dirs))

           ((mv override-successp overrides ov-filemap
                defines override-comments
                walist state)
            (cwtime (vl-read-overrides override-dirs defines filemapp state)
                    :mintime 1))

           ((mv start-successp start-mods start-filemap
                start-oused start-mtokens
                defines warnings walist state)
            (cwtime (vl-load-files start-files include-dirs defines overrides
                                   warnings walist filemapp state)
                    :mintime 1))

           (required (vl-overridelist-requirement-names-exec start-oused nil))

           ((mv flush-successp flushed-mods flushed-filemap
                flushed-oused flushed-mtokens
                defines warnings walist state)
            (cwtime (vl-flush-out-modules start-mods start-modnames search-path
                                          searchext include-dirs defines overrides
                                          required warnings walist filemapp
                                          state 10000)
                    :mintime 1))

           (- (fast-alist-free overrides))

           ((mv mods multidef-warnings)
            (cwtime (vl-handle-multidef-mods flushed-mods)
                    :mintime 1))

           ;; Final override handling.  Need to add comments to the overridden
           ;; modules and check that all requirements are met.

           (mods (cwtime (vl-inject-comments-modulelist mods override-comments)
                         :mintime 1/2))

           (oused   (append start-oused flushed-oused))
           (mtokens (make-fast-alist (append start-mtokens flushed-mtokens)))
           (walist  (cwtime (vl-check-override-requirements oused mtokens walist)
                            :mintime 1/2))
           (- (fast-alist-free mtokens))

           ;; Apply the walist throughout all modules
           (mods (cwtime (vl-apply-modwarningalist mods walist)
                         :mintime 1/2))


           (successp (and override-successp start-successp flush-successp))
           (filemap  (append ov-filemap start-filemap flushed-filemap))

           (- (cw "vl-load-fn: loaded ~x0 modules.~%" (len mods)))
           (- (or successp
                  ;; We don't really care that not everything was loaded, because
                  ;; vl-load-fn gives us as much as it can.  We'll just print a
                  ;; message, but the real reasons are in the warnings list.
                  (cw "vl-load-fn: not all modules were loaded successfully.~%")))

           ;; The warnings get returned, but we also summarize the floating
           ;; warnings as a convenience to whomever is running the translator.
           (mod-warnings (mergesort (vl-modulelist-flat-warnings mods)))
           (all-warnings (mergesort (append multidef-warnings
                                            (redundant-list-fix warnings)
                                            mod-warnings)))
           (floating-warnings (difference all-warnings mod-warnings))
           (- (or (not all-warnings)
                  (cw "vl-load-fn: total number of warnings: ~x0.~%"
                      (len all-warnings))))
           (- (or (not floating-warnings)
                  (vl-cw-ps-seq
                   (vl-ps-update-autowrap-col 68)
                   (vl-cw "vl-load-fn: ~x0 floating warning~s1:~%"
                          (len floating-warnings)
                          (if (= (len floating-warnings) 1) "" "s"))
                   (vl-print-warnings warnings)
                   (vl-println "")))))
        (mv successp mods filemap defines floating-warnings state))

      (progn$
       ;; We're now after the mv-let's body, so the temporary bindings above
       ;; should now be out of scope.  This is a reasonably good time to
       ;; garbage collect since file reading, lexing, etc. create a lot of
       ;; garbage.  There is a trade-off: it's slower to GC here than to not GC
       ;; here when we run our nightly translations, but it frees up a lot of
       ;; memory and helps when running the translator on any more modest
       ;; machine (e.g., in the command-line use-set and vl-prove tools).  So,
       ;; I'm willing to wait slightly longer.
       (clear-memoize-table 'vl-actually-report-parse-error)
       (vl-gc)
       (mv successp mods filemap defines warnings state))))

  (local (in-theory (enable vl-load-fn)))

  (defthm booleanp-of-vl-load-fn-0
    (booleanp (mv-nth 0 (vl-load-fn override-dirs start-files start-modnames
                                    search-path searchext include-dirs defines filemapp state)))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-load-fn-1
    (implies (true-listp mods)
             (true-listp (mv-nth 1 (vl-load-fn override-dirs start-files start-modnames
                                               search-path searchext include-dirs defines filemapp state))))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-load-fn-2
    (true-listp (mv-nth 2 (vl-load-fn override-dirs start-files start-modnames
                                      search-path searchext include-dirs defines filemapp state)))
    :rule-classes :type-prescription)

  (defthm state-p1-of-vl-load-fn
    (implies (force (state-p1 state))
             (state-p1 (mv-nth 5 (vl-load-fn override-dirs start-files start-modnames
                                             search-path searchext include-dirs defines filemapp state)))))

  (defthm no-duplicatesp-equal-of-vl-load-fn
    (no-duplicatesp-equal
     (vl-modulelist->names (mv-nth 1 (vl-load-fn override-dirs start-files start-modnames
                                                 search-path searchext include-dirs defines filemapp state)))))

  (defthm vl-load-fn-basics
    (implies
     (and (force (string-listp override-dirs))
          (force (string-listp start-files))
          (force (string-listp start-modnames))
          (force (string-listp search-path))
          (force (string-listp searchext))
          (force (string-listp include-dirs))
          (force (vl-defines-p defines))
          (force (state-p state)))
     (let ((result (vl-load-fn override-dirs start-files start-modnames
                               search-path searchext include-dirs
                               defines filemapp state)))
       (and (vl-modulelist-p (mv-nth 1 result))
            (vl-filemap-p (mv-nth 2 result))
            (vl-defines-p (mv-nth 3 result))
            (vl-warninglist-p (mv-nth 4 result)))))))



