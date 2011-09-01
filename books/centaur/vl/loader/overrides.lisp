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
(include-book "lexer")
(include-book "preprocessor")
(include-book "parse-utils")
(include-book "parse-error")
(include-book "filemap")
(include-book "../util/cwtime")
(include-book "../mlib/warnings")
(include-book "centaur/misc/ls" :dir :system)
(include-book "str/top" :dir :system)
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))



(defxdoc overrides
  :parents (loader)
  :short "How to give custom definitions to modules for VL."

  :long "<p>If you are trying to translate a design that uses constructs which
VL does not support (e.g., transistors, multi-dimensional arrays, etc.), you
may need to <b>override</b> the real definition of these modules with a custom
definition for VL.</p>

<p>An obvious way to handle overrides would be to set up a <tt>`define</tt> so
that, e.g., <tt>`ifdef VL</tt> and <tt>`else</tt> can control which version of
the module is loaded.  But this might not be appropriate in all cases, e.g., it
may not be desirable for a formal verification team to even have write access
to the design.</p>

<p>An alternative is to keep the custom definitions in separate Verilog files,
then use a custom search path for parsing with VL.  But a challenge here is to
keep the overridden definitions up-to-date as the original source files are
modified and extended.</p>

<p>To facilitate this, VL's loading routines can be given a list of
<tt>:override-dirs</tt>, directories which are expected to contain \"override
files\" with an <tt>.ov</tt> extension.  The <tt>.ov</tt> files in this
collection of directories must all have distinct names or an error will be
caused.</p>


<h3>Override Files</h3>

<p>Before any ordinary Verilog parsing begins, VL reads all of the <tt>.ov</tt>
files in all of the the override directories and constructs a database.  Each
override file should contain a list of <tt>VL_OVERRIDE</tt> statements.  The
syntax of these statements is a superset of Verilog:</p>

<code>
override_file ::= { override }

override ::= 'VL_OVERRIDE' { require_list } original_list replacement 'VL_ENDOVERRIDE'

require_list ::= require { require }

original_list ::= original { original }

require ::= 'VL_REQUIRE' 'module' id { non_endmodule } 'endmodule'
          | 'VL_REQUIRE' 'macromodule' id { non_endmodule } 'endmodule'

original ::= 'VL_ORIGINAL' 'module' id { non_endmodule } 'endmodule'
           | 'VL_ORIGINAL' 'macromodule' id { non_endmodule } 'endmodule'

replacement ::= 'VL_REPLACEMENT' { std_token }
</code>

<p>Where <tt>std_token</tt> may be any token other than:</p>

<ul>
<li><tt>VL_OVERRIDE</tt>,</li>
<li><tt>VL_REQUIRE</tt>,</li>
<li><tt>VL_ORIGINAL</tt>,</li>
<li><tt>VL_REPLACEMENT</tt>, or</li>
<li><tt>VL_ENDOVERRIDE</tt>,</li>
</ul>

<p>and where <tt>non_endmodule</tt> is any <tt>std_token</tt> except for
<tt>endmodule</tt>.</p>

<p>In addition to the syntactic requirements above, we require the names of
every module or macromodule in an <tt>original</tt> form to be the same as the
filename.</p>


<h3>Override Semantics</h3>

<p>VL loads all of the available override files into a database before reading
any ordinary Verilog files.  This database then influences the way that the
ordinary Verilog files are read.</p>

<p>In particular, when VL encounters the \"current\" definition of each module
<tt>m</tt> in an ordinary Verilog source file, it first checks to see whether
there are any overrides for <tt>m</tt>.</p>

<p>Typically there are not any overrides, so we leave the current definition of
<tt>m</tt> unchanged.  But when there are overrides for <tt>m</tt>, we try to
match the current definition of <tt>m</tt> against each definition provided in
an \"original\" entry.  If we find a match, we replace the current definition
of <tt>m</tt> with the corresponding \"replacement\" definition.</p>

<p>As changes are made to the design, the module <tt>m</tt> may eventually be
changed so that its definition no longer matches any of the \"original\"
entries in the override file.  In this case, we add a fatal warning to
<tt>m</tt> saying that its override is out of date.</p>

<p>We have now covered the meaning of the \"original\" and \"replacement\"
forms, but what are requirements?  A particular module <tt>m</tt> that we wish
to override might instantiate various submodules.  In such cases, for the
override to be valid we need to ensure that these modules have not been
changed.  Requirements allow us to do this.</p>

<p>Whenever we make a replacement, we make note of all of the corresponding
requirements.  After all of the modules have been loaded, we can check whether
the requirements are met, i.e., whether the submodules involved still have the
expected definitions.  If multiple require statements have the same module
name, <tt>r</tt>, it means that the current definition of <tt>r</tt> must match
any one of these definitions.</p>


<h3>Sketch of a Typical Override</h3>

<p>Here's a hypothetical override file that demonstrates these features.</p>

<code>
VL_OVERRIDE

 VL_REQUIRE
   module sub1 (p, q, r); ... sub1 version A/B ... ; endmodule

 VL_REQUIRE
   module sub2 (p, q, r); ... sub2 version A/B ... ; endmodule

 VL_ORIGINAL
   module foo (o, a, b) ; ... foo version A ... ; endmodule

 VL_ORIGINAL
   module foo (o, a, b) ; ... foo version B ... ; endmodule

 VL_REPLACEMENT
   module foo (o, a, b) ;
     ... replacement for foo versions A or B ... ;
   endmodule

VL_ENDOVERRIDE


VL_OVERRIDE

  VL_REQUIRE
    module sub3 (p, q, r, powerdown) ; ... sub3 version C1 ... ; endmodule

  VL_REQUIRE
    module sub3 (p, q, r, powerdown) ; ... sub3 version C2 ... ; endmodule

  VL_ORIGINAL
    module foo (o, a, b, powerdown) ; ... foo version C ... ; endmodule

  VL_REPLACEMENT
    module foo (o, a, b, powerdown) ;
      ... replacement for foo version C ... ;
    endmodule

VL_ENDOVERRIDE
</code>

<p>In this scenario, we imagine that <tt>foo</tt> is a module that is currently
being used in three different designs named A, B, and C.</p>

<p>The definition of <tt>foo</tt> in Versions A and B are presumably very
similar, and make use of the same submodules <tt>sub1</tt> and <tt>sub2</tt>.
Since only minor changes were made to <tt>foo</tt> between versons A and B, we
can use the same override in either version.</p>

<p>In Version C, the interface of <tt>foo</tt> has been changed, so a different
replacement is necessary.  We also imagine that <tt>foo</tt> now instances a
new submodule, <tt>sub3</tt>, and that there have been two different variants
of this module but they have the same semantics.</p>



<h3>Matching Details</h3>

<p>We match modules against the overrides database after lexing, but before
parsing.  This approach allows us to automatically ignore changes to comments
and whitespace for the purposes of matching.  On the other hand, even simple
changes like reordering of module elements or adding explicit declarations for
implicit wires is enough to prevent matches.</p>

<p>Note that we have decided to preprocess overrides files as if they were
ordinary Verilog files.  This means you can write things like this:</p>

<code>
`define bar 3

VL_OVERRIDE

 VL_ORIGINAL {
   module foo (o, a, b) ; ... `bar ... ; endmodule
 }

 VL_REPLACEMENT {
   module foo (o, a, b) ; ... `bar ... ; endmodule
 }

VL_ENDOVERRIDE
</code>

<p>and you can use <tt>`ifdef</tt>, etc., within override files.</p>

<p>This can be subtle.  All matching will be done on the already-preprocessed
source text, so for matching to succeed you must ensure that the relevant
<tt>`define</tt> directives that we used when reading the override file will
still be the same when we read the \"current version\" of the module.  Note
also that any <tt>`define</tt> directives introduced in overrides will \"spill
out\" and affect the parsing of Verilog files; see also @(see vl-load) for some
additional details about this decision.</p>")

(defaggregate vl-override
  (name replacement requirements originals)
  :tag :vl-override
  :legiblep nil
  :parents (overrides)
  :short "Parsed representation of a VL_OVERRIDE."
  :require ((stringp-of-vl-override->name (stringp name))
            (vl-tokenlistlist-p-of-vl-override-entry->requirements
             (vl-tokenlistlist-p requirements))
            (vl-tokenlistlist-p-of-vl-override-entry->originals
             (vl-tokenlistlist-p originals))
            (vl-tokenlist-p-of-vl-override-entry->replacement
             (vl-tokenlist-p replacement))))

(deflist vl-overridelist-p (x)
  (vl-override-p x)
  :guard t
  :elementp-of-nil nil)



(defsection vl-override-requirement-names
  :parents (vl-override-p)
  :short "Extract the module names from all \"require\" entries in an override."
  :long "@(def vl-override-requirement-names)
@(def vl-override-requirement-names-aux)"

  (defund vl-override-requirement-names-aux (requirements)
    (declare (xargs :guard (vl-tokenlistlist-p requirements)))
    (b* (((when (atom requirements))
          nil)
         (body (car requirements))
         ((unless (and (consp body)
                       (or (eq (vl-token->type (first body)) :vl-kwd-module)
                           (eq (vl-token->type (first body)) :vl-kwd-macromodule))
                       (consp (cdr body))
                       (eq (vl-token->type (second body)) :vl-idtoken)))
          (er hard? 'vl-override-requirement-names-aux
              "Requirement body is not well-formed: ~x0.~%" body))
         (name (vl-idtoken->name (second body))))
      (cons name (vl-override-requirement-names-aux (cdr requirements)))))

  (defthm string-listp-of-vl-override-requirement-names-aux
    (implies (vl-tokenlistlist-p requirements)
             (string-listp (vl-override-requirement-names-aux requirements)))
    :hints(("Goal" :in-theory (enable vl-override-requirement-names-aux))))

  (defund vl-override-requirement-names (x)
    (declare (xargs :guard (vl-override-p x)))
    (mergesort (vl-override-requirement-names-aux (vl-override->requirements x))))

  (defthm string-listp-of-vl-override-requirement-names
    (implies (force (vl-override-p x))
             (string-listp (vl-override-requirement-names x)))
    :hints(("Goal" :in-theory (enable vl-override-requirement-names)))))


(defmapappend vl-overridelist-requirement-names (x)
  (vl-override-requirement-names x)
  :guard (vl-overridelist-p x)
  :transform-true-list-p t)

(defthm string-listp-of-vl-overridelist-requirement-names
  (implies (force (vl-overridelist-p x))
           (string-listp (vl-overridelist-requirement-names x)))
  :hints(("Goal" :induct (len x))))




(defsection vl-override-db-p
  :parents (overrides)
  :short "Fast alist binding module names to the list of @(see vl-override-p)s
for each module that has overrides."

  :long "<p>We use this as a filter so we only have to consider the overrides
corresponding to a particular module.</p>

 @(def vl-override-db-p)"

  (defund vl-override-db-p (x)
    (declare (xargs :guard t))
    (if (atom x)
        (not x)
      (and (consp (car x))
           (stringp (caar x))
           (vl-overridelist-p (cdar x))
           (vl-override-db-p (cdr x)))))

  (local (in-theory (enable vl-override-db-p)))

  (defthm vl-override-db-p-when-atom
    (implies (atom x)
             (equal (vl-override-db-p x)
                    (not x))))

  (defthm vl-override-db-p-of-cons
    (equal (vl-override-db-p (cons a x))
           (and (consp a)
                (stringp (car a))
                (vl-overridelist-p (cdr a))
                (vl-override-db-p x))))

  (defthm vl-override-db-p-of-append
    (implies (and (vl-override-db-p x)
                  (vl-override-db-p y))
             (vl-override-db-p (append x y))))

  (defthm alistp-when-vl-override-db-p
    (implies (vl-override-db-p x)
             (alistp x)))

  (defthm vl-override-db-p-of-make-fal
    (implies (and (vl-override-db-p acc)
                  (vl-override-db-p x))
             (vl-override-db-p (make-fal x acc)))
    :hints(("Goal" :in-theory (enable make-fal))))

  (defthm vl-overridelist-p-of-lookup-in-vl-override-db-p
    (implies (vl-override-db-p x)
             (vl-overridelist-p (cdr (hons-assoc-equal name x))))))





; -----------------------------------------------------------------------------
;
;                            PARSING OVERRIDE FILES
;
; -----------------------------------------------------------------------------

; require_list ::= require { require }
;
; require ::= 'VL_REQUIRE' 'module' id { non_endmodule } 'endmodule'
;           | 'VL_REQUIRE' 'macromodule' id { non_endmodule } 'endmodule'

(defparser vl-parse-through-endmodule (tokens warnings)
  ;; Matches { non_endmodule } 'endmodule'
  :result (vl-tokenlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (when (vl-is-token? :vl-kwd-endmodule)
          (tok := (vl-match-token :vl-kwd-endmodule))
          (return (list tok)))
        (first := (vl-match-any-except '(:vl-kwd-vl_override
                                         :vl-kwd-vl_require
                                         :vl-kwd-vl_original
                                         :vl-kwd-vl_replacement
                                         :vl-kwd-vl_endoverride)))
        (rest := (vl-parse-through-endmodule))
        (return (cons first rest))))

(defparser vl-parse-require (tokens warnings)
  :result (vl-tokenlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token ':vl-kwd-vl_require))
        (mod  := (vl-match-some-token '(:vl-kwd-module :vl-kwd-macromodule)))
        (name := (vl-match-token :vl-idtoken))
        (rest := (vl-parse-through-endmodule))
        (return (list* mod name rest))))

(defparser vl-parse-require-list (tokens warnings)
  ;; Matches require { require }
  :result (vl-tokenlistlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (first := (vl-parse-require))
        (when (vl-is-token? :vl-kwd-vl_require)
          (rest := (vl-parse-require-list)))
        (return (cons first rest))))



; original ::= 'VL_ORIGINAL' 'module' id { non_endmodule } 'endmodule'
;            | 'VL_ORIGINAL' 'macromodule' id { non_endmodule } 'endmodule'
;
; original_list ::= original { original }

(defparser vl-parse-original (filename tokens warnings)
  :guard (stringp filename)
  :result (vl-tokenlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token ':vl-kwd-vl_original))
        (mod  := (vl-match-some-token '(:vl-kwd-module :vl-kwd-macromodule)))
        (name := (vl-match-token :vl-idtoken))
        (unless (equal (vl-idtoken->name name) filename)
          (return-raw
           (vl-parse-error (str::cat "Module name " (vl-idtoken->name name)
                                     " does not match file name "
                                     filename "."))))
        (rest := (vl-parse-through-endmodule))
        (return (list* mod name rest))))

(defparser vl-parse-original-list (filename tokens warnings)
  ;; Matches original { original }
  :guard (stringp filename)
  :result (vl-tokenlistlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (first := (vl-parse-original filename))
        (when (vl-is-token? :vl-kwd-vl_original)
          (rest := (vl-parse-original-list filename)))
        (return (cons first rest))))



; replacement ::= 'VL_REPLACEMENT' { std_token }

(defparser vl-parse-replacement-misc (tokens warnings)
  ;; Matches { std_token }, stopping at VL_ENDOVERRIDE
  :result (vl-tokenlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong-on-value
  (seqw tokens warnings
        (when (vl-is-token? :vl-kwd-vl_endoverride)
          (return nil))
        (first := (vl-match-any-except '(:vl-kwd-vl_override
                                         :vl-kwd-vl_require
                                         :vl-kwd-vl_original
                                         :vl-kwd-vl_replacement
                                         :vl-kwd-vl_endoverride)))
        (rest := (vl-parse-replacement-misc))
        (return (cons first rest))))

(defparser vl-parse-replacement (tokens warnings)
  :result (vl-tokenlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-kwd-vl_replacement))
        (body := (vl-parse-replacement-misc))
        (return body)))


; override ::= 'VL_OVERRIDE' { require_list } original_list replacement 'VL_ENDOVERRIDE'
;
; override_file ::= { override }

(defparser vl-parse-override (filename tokens warnings)
  :guard (stringp filename)
  :result (vl-override-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-kwd-vl_override))
        (when (vl-is-token? :vl-kwd-vl_require)
          (requirements := (vl-parse-require-list)))
        (originals := (vl-parse-original-list filename))
        (replacement := (vl-parse-replacement))
        (:= (vl-match-token :vl-kwd-vl_endoverride))
        (return (make-vl-override :name filename
                                  :requirements requirements
                                  :originals originals
                                  :replacement replacement))))

(defparser vl-parse-override-list (filename tokens warnings)
  :guard (stringp filename)
  :result (vl-overridelist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong-on-value
  (seqw tokens warnings
        (when (atom tokens)
          (return nil))
        (first := (vl-parse-override filename))
        (rest  := (vl-parse-override-list filename))
        (return (cons first rest))))



(defsection vl-parse-override-file

  (defund vl-parse-override-file (filename tokens warnings)
    "Returns (MV SUCCESSP OVERRIDELIST WARNINGS)"
    (declare (xargs :guard (and (stringp filename)
                                (vl-tokenlist-p tokens)
                                (vl-warninglist-p warnings))))
    (b* (((mv err val tokens warnings)
          (vl-parse-override-list filename tokens warnings))
         ((when err)
          (vl-report-parse-error err tokens)
          (mv nil nil warnings)))
      (mv t val warnings)))

  (local (in-theory (enable vl-parse-override-file)))

  (defthm true-listp-of-vl-parse-override-file-1
    (true-listp (mv-nth 1 (vl-parse-override-file filename tokens warnings)))
    :rule-classes :type-prescription)

  (defthm vl-overridelist-p-of-vl-parse-override-file
    (implies (and (force (stringp filename))
                  (force (vl-tokenlist-p tokens))
                  (force (vl-warninglist-p warnings)))
             (vl-overridelist-p
              (mv-nth 1 (vl-parse-override-file filename tokens warnings)))))

  (defthm vl-warninglist-p-of-vl-parse-override-file
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 2 (vl-parse-override-file filename tokens warnings))))))



(defsection vl-read-override-file
  :parents (overrides)
  :short "Load an override file into a @(see vl-override-alistp)."

  :long "<p>Signature: @(call vl-read-override-file) returns <tt>(mv successp
override-alist filemap defines' comment-map' walist' state)</tt>.</p>

@(def vl-read-override-file)"

  (defund vl-read-override-file (path modname defines comment-map walist filemapp state)
    "Returns (MV SUCCESSP OVERRIDE-LIST FILEMAP DEFINES' COMMENT-MAP' WALIST' STATE)"
    (declare (xargs :guard (and (stringp path)
                                (stringp modname)
                                (vl-defines-p defines)
                                (vl-commentmap-p comment-map)
                                (vl-modwarningalist-p walist)
                                (booleanp filemapp))
                    :stobjs state))

    (b* ((filename (str::cat path "/" modname ".ov"))
         (- (cw "Reading override file ~s0.~%" filename))

         (filemap nil)

         ((mv contents state)
          (cwtime (vl-read-file filename state) :mintime 1/2))
         ((when (stringp contents))
          (b* ((w (make-vl-warning :type :vl-read-failed
                                   :msg "Error reading override file ~s0."
                                   :args (list filename)
                                   :fn 'vl-read-override-file))
               (walist (vl-extend-modwarningalist modname w walist)))
            (mv nil nil filemap defines comment-map walist state)))

         (filemap (and filemapp
                       (list (cons filename (vl-echarlist->string contents)))))

         ((mv successp defines preprocessed state)
          ;; BOZO for now overrides don't have any include-dirs.  Not sure what
          ;; the right way to handle this is.
          (cwtime (vl-preprocess contents defines nil state) :mintime 1/2))
         ((unless successp)
          (b* ((w (make-vl-warning :type :vl-preprocess-failed
                                   :msg "Preprocessing failed for override file ~s0."
                                   :args (list filename)
                                   :fn 'vl-read-override-file))
               (walist (vl-extend-modwarningalist modname w walist)))
            (mv nil nil filemap defines comment-map walist state)))

         ((mv successp lexed warnings)
          (cwtime (vl-lex preprocessed nil) :mintime 1/2))
         (walist (if warnings
                     (vl-extend-modwarningalist-list modname warnings walist)
                   walist))
         ((unless successp)
          (b* ((w (make-vl-warning :type :vl-lex-failed
                                   :msg "Lexing failed for override file ~s0."
                                   :args (list filename)
                                   :fn 'vl-read-override-file))
               (walist (vl-extend-modwarningalist modname w walist)))
            (mv nil nil filemap defines comment-map walist state)))

         ((mv cleaned new-comments)
          (cwtime (vl-kill-whitespace-and-comments lexed) :mintime 1/2))
         (comment-map (append new-comments comment-map))

         ((mv successp override-list warnings)
          (cwtime (vl-parse-override-file modname cleaned nil) :mintime 1/2))
         (walist (if warnings
                     (vl-extend-modwarningalist-list modname warnings walist)
                   walist))
         ((unless successp)
          (b* ((w (make-vl-warning :type :vl-parse-failed
                                   :msg "Parsing failed for ~s0."
                                   :args (list filename)
                                   :fn 'vl-read-override-file))
               (walist (vl-extend-modwarningalist modname w walist)))
            (mv nil nil filemap defines comment-map walist state))))

      (mv t override-list filemap defines comment-map walist state)))

  (local (in-theory (enable vl-read-override-file)))

  (defthm state-p1-of-vl-read-override-file
    (implies (force (state-p1 state))
             (state-p1
              (mv-nth 6 (vl-read-override-file path modname defines comment-map
                                               walist filemapp state)))))

  (defthm true-listp-of-vl-read-file-2
    (true-listp (mv-nth 2 (vl-read-override-file path modname defines comment-map
                                                 walist filemapp state)))
    :rule-classes :type-prescription)

  (defthm vl-read-override-file-basics
    (implies
     (and (force (stringp path))
          (force (stringp modname))
          (force (vl-defines-p defines))
          (force (vl-modwarningalist-p walist))
          (force (vl-commentmap-p comment-map))
          (force (state-p1 state)))
     (let ((result (vl-read-override-file path modname defines comment-map
                                          walist filemapp state)))
       (and (vl-overridelist-p (mv-nth 1 result))
            (vl-filemap-p (mv-nth 2 result))
            (vl-defines-p (mv-nth 3 result))
            (vl-commentmap-p (mv-nth 4 result))
            (vl-modwarningalist-p (mv-nth 5 result)))))))




(defsection vl-read-override-files
  :parents (overrides)
  :short "Load a list of override files into a @(see vl-override-db-p)."

  :long "<p>Signature: @(call vl-read-override-files) returns <tt>(mv successp
override-db filemap defines' comment-map' walist' state)</tt>.</p>

<p><tt>successp</tt> indicates whether all of the files were loaded with no
problems, and even when <tt>successp</tt> is nil there may be at least a partial
overrides database loaded.</p>

@(def vl-read-override-files)"

  (defund vl-read-override-files (path modnames defines comment-map walist filemapp state)
    "Returns (MV SUCCESSP OVERRIDE-DB FILEMAP DEFINES' COMMENT-MAP' WALIST' STATE)"
    (declare (xargs :guard (and (stringp path)
                                (string-listp modnames)
                                (vl-defines-p defines)
                                (vl-commentmap-p comment-map)
                                (vl-modwarningalist-p walist)
                                (booleanp filemapp))
                    :stobjs state))
    (b* (((when (atom modnames))
          (mv t nil nil defines comment-map walist state))

         ((mv successp1 alist1 filemap1 defines comment-map walist state)
          (vl-read-override-file path (car modnames)
                                 defines comment-map walist filemapp state))

         ((mv successp2 rest-db filemap2 defines comment-map walist state)
          (vl-read-override-files path (cdr modnames)
                                  defines comment-map walist filemapp state))

         (successp    (and successp1 successp2))
         (override-db (cons (cons (car modnames) alist1) rest-db))
         (filemap     (append filemap1 filemap2)))

      (mv successp override-db filemap defines comment-map walist state)))

  (local (in-theory (enable vl-read-override-files)))

  (defthm true-listp-of-vl-read-override-files-1
    (true-listp (mv-nth 1 (vl-read-override-files path modnames defines comment-map
                                                  walist filemapp state)))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-read-override-files-2
    (true-listp (mv-nth 2 (vl-read-override-files path modnames defines comment-map
                                                  walist filemapp state)))
    :rule-classes :type-prescription)

  (defthm state-p1-of-vl-read-override-files
    (implies (force (state-p1 state))
             (state-p1
              (mv-nth 6 (vl-read-override-files path modnames defines comment-map
                                                walist filemapp state)))))

  (defthm vl-read-override-files-basics
    (implies
     (and (force (stringp path))
          (force (string-listp modnames))
          (force (vl-defines-p defines))
          (force (vl-modwarningalist-p walist))
          (force (vl-commentmap-p comment-map))
          (force (state-p1 state)))
     (let ((result (vl-read-override-files path modnames defines comment-map
                                           walist filemapp state)))
       (and (vl-override-db-p (mv-nth 1 result))
            (vl-filemap-p (mv-nth 2 result))
            (vl-defines-p (mv-nth 3 result))
            (vl-commentmap-p (mv-nth 4 result))
            (vl-modwarningalist-p (mv-nth 5 result)))))))



(defsection vl-collect-override-modnames

  (defund vl-collect-override-modnames (filenames)
    (declare (xargs :guard (string-listp filenames)))
    (b* (((when (atom filenames))
          nil)
         (parts (str::strtok (car filenames) (list #\.)))
         ((when (and (equal (len parts) 2)
                     (equal (second parts) "ov")))
          (cons (car parts)
                (vl-collect-override-modnames (cdr filenames)))))
      (vl-collect-override-modnames (cdr filenames))))

  (local (in-theory (enable vl-collect-override-modnames)))

  (local (defthm stringp-of-car-when-string-listp
           (implies (string-listp x)
                    (equal (stringp (car x))
                           (consp x)))))

  (defthm string-listp-of-vl-collect-override-modnames
    (implies (string-listp x)
             (string-listp (vl-collect-override-modnames x)))))



(defsection vl-read-overrides-aux

  (defund vl-read-overrides-aux (dirs defines comment-map walist filemapp state)
    "Returns (MV SUCCESSP OVERRIDE-DB FILEMAP DEFINES' COMMENT-MAP' WALIST' STATE)"
    (declare (xargs :guard (and (string-listp dirs)
                                (vl-defines-p defines)
                                (vl-commentmap-p comment-map)
                                (vl-modwarningalist-p walist)
                                (booleanp filemapp))
                    :stobjs state))
    (b* (((when (atom dirs))
          (mv t nil nil defines comment-map walist state))

         (path1 (car dirs))
         ((mv err filenames state) (acl2::ls-files path1 state))
         (filenames (if err
                        (er hard? 'vl-read-overrides-aux "Error listing ~x0.~%" (car dirs))
                      filenames))

         (modnames1 (vl-collect-override-modnames filenames))
         ((mv successp1 override-db1 filemap1 defines comment-map walist state)
          (vl-read-override-files path1 modnames1 defines comment-map
                                  walist filemapp state))

         ((mv successp2 override-db2 filemap2 defines comment-map walist state)
          (vl-read-overrides-aux (cdr dirs) defines comment-map
                                 walist filemapp state))

         (successp    (and successp1 successp2))
         (override-db (append override-db1 override-db2))
         (filemap     (append filemap1 filemap2)))

      (mv successp override-db filemap defines comment-map walist state)))

  (local (in-theory (enable vl-read-overrides-aux)))

  (defthm true-listp-of-vl-read-overrides-aux-1
    (true-listp (mv-nth 1 (vl-read-overrides-aux dirs defines comment-map
                                                 walist filemapp state)))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-read-overrides-aux-2
    (true-listp (mv-nth 2 (vl-read-overrides-aux dirs defines comment-map
                                                 walist filemapp state)))
    :rule-classes :type-prescription)

  (defthm state-p1-of-vl-read-overrides-aux
    (implies (force (state-p1 state))
             (state-p1
              (mv-nth 6 (vl-read-overrides-aux dirs defines comment-map
                                               walist filemapp state)))))

  (defthm vl-read-overrides-aux-basics
    (implies
     (and (force (string-listp dirs))
          (force (vl-defines-p defines))
          (force (vl-modwarningalist-p walist))
          (force (vl-commentmap-p comment-map))
          (force (state-p1 state)))
     (let ((result (vl-read-overrides-aux dirs defines comment-map walist filemapp state)))
       (and (vl-override-db-p (mv-nth 1 result))
            (vl-filemap-p (mv-nth 2 result))
            (vl-defines-p (mv-nth 3 result))
            (vl-commentmap-p (mv-nth 4 result))
            (vl-modwarningalist-p (mv-nth 5 result)))))))



(defsection vl-read-overrides
  :parents (overrides)
  :short "Scan directories for override files and load them into an @(see
vl-override-db-p)."

  :long "<p><b>Signature:</b> @(call vl-read-overrides) returns <tt>(mv
successp override-db defines' comment-map walist state)</tt>.</p>

<p>The success flag says whether everything was loaded successfully; even if
successp is nil, a partial override database will be produced and may be
useful.</p>

@(def vl-read-overrides)
@(def vl-read-overrides-aux)"

  (defund vl-read-overrides (dirs defines filemapp state)
    "Returns (MV SUCCESSP OVERRIDE-DB FILEMAP DEFINES' COMMENT-MAP WALIST STATE)"
    (declare (xargs :guard (and (string-listp dirs)
                                (vl-defines-p defines)
                                (booleanp filemapp))
                    :stobjs state))
    (b* (((mv successp override-db filemap defines comment-map walist state)
          (vl-read-overrides-aux dirs defines nil nil filemapp state))
         (overridden-mods (strip-cars override-db))
         (- (or (uniquep overridden-mods)
                ;; This is probably too severe.  We could instead add fatal
                ;; warnings to each of these modules, for instance.
                (er hard? 'vl-read-overrides
                    "Multiple override files for ~&0.~%"
                    (duplicated-members overridden-mods)))))
      (mv successp
          (make-fal override-db nil)
          filemap
          defines comment-map walist state)))

  (local (in-theory (enable vl-read-overrides)))

  (defthm state-p1-of-vl-read-overrides
    (implies (force (state-p1 state))
             (state-p1 (mv-nth 6 (vl-read-overrides dirs defines filemapp state)))))

  (defthm true-listp-of-vl-overrides-2
    (true-listp (mv-nth 2 (vl-read-overrides dirs defines filemapp state)))
    :rule-classes :type-prescription)

  (defthm vl-read-overrides-basics
    (implies
     (and (force (string-listp dirs))
          (force (vl-defines-p defines))
          (force (state-p1 state)))
     (let ((result (vl-read-overrides dirs defines filemapp state)))
       (and
        (vl-override-db-p (mv-nth 1 result))
        (vl-filemap-p (mv-nth 2 result))
        (vl-defines-p (mv-nth 3 result))
        (vl-commentmap-p (mv-nth 4 result))
        (vl-modwarningalist-p (mv-nth 5 result)))))))





; -----------------------------------------------------------------------------
;
;                         APPLYING OVERRIDE DATABASES
;
; -----------------------------------------------------------------------------

(defsection vl-match-through-endmodule
  :parents (overrides)
  :short "Collect tokens through <tt>endmodule</tt>."
  :long "<p><b>Signature:</b> @(call vl-match-through-endmodule) returns
<tt>(mv successp prefix rest)</tt>.</p>

<p>We attept to split the @(see vl-tokenlist-p) <tt>tokens</tt> into
<tt>prefix</tt> and <tt>rest</tt>, where <tt>prefix</tt> contains everything up
through the first occurrence of the <tt>endmodule</tt> keyword, and
<tt>rest</tt> contains whatever follows.</p>

<p><tt>successp</tt> is true exactly when there is any occurrence of
<tt>endmodule</tt> within <tt>tokens</tt>.</p>

@(def vl-match-through-endmodule)
@(def vl-match-through-endmodule-aux)"

  (defund vl-match-through-endmodule-aux (tokens prefix-rev)
    "Returns (MV SUCCESSP PREFIX-REV REST)"
    (declare (xargs :guard (vl-tokenlist-p tokens)))
    (cond ((atom tokens)
           (mv nil prefix-rev tokens))
          ((eq (vl-token->type (car tokens)) :vl-kwd-endmodule)
           (mv t (cons (car tokens) prefix-rev) (cdr tokens)))
          (t
           (vl-match-through-endmodule-aux (cdr tokens) (cons (car tokens) prefix-rev)))))

  (defund vl-match-through-endmodule (tokens)
    "Returns (MV SUCCESSP PREFIX REST)"
    (declare (xargs :guard (vl-tokenlist-p tokens)
                    :verify-guards nil))
    (b* (((mv successp prefix-rev rest)
          (vl-match-through-endmodule-aux tokens nil)))
      (mv successp (reverse prefix-rev) rest)))

  (defttag vl-optimize)
  (progn!
   (set-raw-mode t)
   (setf (gethash 'vl-match-through-endmodule-aux ACL2::*never-profile-ht*) t)
   (defun vl-match-through-endmodule (tokens)
     (b* (((mv successp prefix-rev rest)
           (vl-match-through-endmodule-aux tokens nil)))
       (mv successp (nreverse prefix-rev) rest))))
  (defttag nil)

  (local (in-theory (enable vl-match-through-endmodule-aux vl-match-through-endmodule)))

  (local
   (defthm lemma
     (and
      (implies (true-listp prefix-rev)
               (true-listp (mv-nth 1 (vl-match-through-endmodule-aux tokens prefix-rev))))
      (implies (true-listp tokens)
               (true-listp (mv-nth 2 (vl-match-through-endmodule-aux tokens prefix-rev))))
      (implies (and (vl-tokenlist-p tokens)
                    (vl-tokenlist-p prefix-rev))
               (vl-tokenlist-p (mv-nth 1 (vl-match-through-endmodule-aux tokens prefix-rev))))
      (implies (and (vl-tokenlist-p tokens)
                    (vl-tokenlist-p prefix-rev))
               (vl-tokenlist-p (mv-nth 2 (vl-match-through-endmodule-aux tokens prefix-rev)))))))

  (verify-guards vl-match-through-endmodule)

  (defthm true-listp-of-vl-match-through-endmodule-1
    (true-listp (mv-nth 1 (vl-match-through-endmodule tokens)))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-match-through-endmodule-2
    (implies (true-listp tokens)
             (true-listp (mv-nth 2 (vl-match-through-endmodule tokens))))
    :rule-classes ((:rewrite) (:type-prescription)))

  (defthm vl-tokenlist-of-vl-match-through-endmodule-1
    (implies (vl-tokenlist-p tokens)
             (vl-tokenlist-p (mv-nth 1 (vl-match-through-endmodule tokens)))))

  (defthm vl-tokenlist-of-vl-match-through-endmodule-2
    (implies (vl-tokenlist-p tokens)
             (vl-tokenlist-p (mv-nth 2 (vl-match-through-endmodule tokens)))))

  (local
   (defthm lemma2
     (and
      (implies (mv-nth 0 (vl-match-through-endmodule-aux tokens prefix-rev))
               (< (acl2-count (mv-nth 2 (vl-match-through-endmodule-aux tokens prefix-rev)))
                  (acl2-count tokens)))
      (<= (acl2-count (mv-nth 2 (vl-match-through-endmodule-aux tokens prefix-rev)))
          (acl2-count tokens)))))

  (defthm acl2-count-of-vl-match-through-endmodule-weak
    (<= (acl2-count (mv-nth 2 (vl-match-through-endmodule tokens)))
        (acl2-count tokens))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-vl-match-through-endmodule-strong
    (implies (mv-nth 0 (vl-match-through-endmodule tokens))
             (< (acl2-count (mv-nth 2 (vl-match-through-endmodule tokens)))
                (acl2-count tokens)))
    :rule-classes ((:rewrite) (:linear))))



(defsection vl-tokenlist-equiv

  (defund vl-echarlist-equiv-p (x y)
    ;; Determine if extended character lists have the same characters.
    ;; MBE avoids any consing.
    (declare (xargs :guard (and (vl-echarlist-p x)
                                (vl-echarlist-p y))))
    (mbe :logic (equal (vl-echarlist->chars x)
                       (vl-echarlist->chars y))
         :exec (if (atom x)
                   (atom y)
                 (and (consp y)
                      (eql (the character (vl-echar->char (car x)))
                           (the character (vl-echar->char (car y))))
                      (vl-echarlist-equiv-p (cdr x) (cdr y))))))

  (defund vl-token-equiv-p (x y)
    ;; Determine if tokens are "the same" for the purposes of override
    ;; matching.
    (declare (xargs :guard (and (vl-token-p x)
                                (vl-token-p y))
                    :guard-hints (("Goal" :in-theory (enable vl-token-p)))))
    (and (eq (tag x) (tag y))
         (case (tag x)
           (:vl-plaintoken
            (eq (vl-plaintoken->type x) (vl-plaintoken->type y)))
           (:vl-idtoken
            (equal (the string (vl-idtoken->name x))
                   (the string (vl-idtoken->name y))))
           (:vl-inttoken
            (vl-echarlist-equiv-p (vl-inttoken->etext x)
                                  (vl-inttoken->etext y)))
           (:vl-sysidtoken
            (equal (the string (vl-sysidtoken->name x))
                   (the string (vl-sysidtoken->name y))))
           (:vl-stringtoken
            (equal (the string (vl-stringtoken->expansion x))
                   (the string (vl-stringtoken->expansion y))))
           (otherwise
            (vl-echarlist-equiv-p (vl-realtoken->etext x)
                                  (vl-realtoken->etext y))))))

  (defund vl-tokenlist-equiv-p (x y)
    ;; Determine if two token lists are the same length and have
    ;; pairwise-equivalent elements.
    (declare (xargs :guard (and (vl-tokenlist-p x)
                                (vl-tokenlist-p y))))
    (if (atom x)
        (atom y)
      (and (consp y)
           (vl-token-equiv-p (car x) (car y))
           (vl-tokenlist-equiv-p (cdr x) (cdr y)))))

  (defund vl-tokenlist-equiv-to-some-p (a x)
    (declare (xargs :guard (and (vl-tokenlist-p a)
                                (vl-tokenlistlist-p x))))
    (if (atom x)
        nil
      (or (vl-tokenlist-equiv-p a (car x))
          (vl-tokenlist-equiv-to-some-p a (cdr x))))))



(defsection vl-find-override
  :parents (overrides)
  :short "Try to find a match for some body in a @(see vl-overridelist-p)."

  :long "<p>Signature: @(call vl-find-override) returns an @(see vl-override-p)
on success or <tt>nil</tt> on failure.</p>

@(def vl-find-override)"

  (defund vl-find-override (body overrides)
    (declare (xargs :guard (and (vl-tokenlist-p body)
                                (vl-overridelist-p overrides))))
    (b* (((when (atom overrides))
          nil)

         (originals1 (vl-override->originals (car overrides)))
         ((when (vl-tokenlist-equiv-to-some-p body originals1))
          (car overrides)))
      (vl-find-override body (cdr overrides))))

  (local (in-theory (enable vl-find-override)))

  (defthm vl-override-p-of-vl-find-override
    (implies (and (force (vl-tokenlist-p body))
                  (force (vl-overridelist-p overrides)))
             (equal (vl-override-p (vl-find-override body overrides))
                    (if (vl-find-override body overrides)
                        t
                      nil)))))




(defsection vl-modtokensalist-p

  (defund vl-modtokensalist-p (x)
    (declare (xargs :guard t))
    (if (atom x)
        (not x)
      (and (consp (car x))
           (stringp (caar x))
           (vl-tokenlist-p (cdar x))
           (vl-modtokensalist-p (cdr x)))))

  (local (in-theory (enable vl-modtokensalist-p)))

  (defthm vl-modtokensalist-p-when-not-consp
    (implies (not (consp x))
             (equal (vl-modtokensalist-p x)
                    (not x))))

  (defthm vl-modtokensalist-p-of-cons
    (equal (vl-modtokensalist-p (cons a x))
           (and (stringp (car a))
                (vl-tokenlist-p (cdr a))
                (vl-modtokensalist-p x))))

  (defthm alistp-when-vl-modtokensalist-p
    (implies (vl-modtokensalist-p x)
             (alistp x)))

  (defthm vl-modtokensalist-p-of-append
    (implies (and (force (vl-modtokensalist-p x))
                  (force (vl-modtokensalist-p y)))
             (vl-modtokensalist-p (append x y))))

  (defthm vl-tokenlist-p-of-lookup-in-vl-modtokensalist-p
    (implies (vl-modtokensalist-p x)
             (vl-tokenlist-p (cdr (hons-assoc-equal a x))))))




(defsection vl-apply-overrides
  :parents (overrides)
  :short "Transform a token list using the overrides database."

  :long "<p><b>Signature:</b> @(call vl-apply-overrides) returns <tt>(mv
walist-prime x-prime used modtokens)</tt>.</p>

<p>Inputs:</p>

<ul>
<li><tt>x</tt> is the list of tokens to transform, and have presumably just
been read from some ordinary Verilog file,</li>

<li><tt>db</tt> is the @(see vl-override-db-p) and is typically constructed by
@(see vl-read-overrides), and</li>

<li><tt>walist</tt> is an @(see vl-modwarningalist-p) that we may extend with
fatal warnings for any modules that we cannot find current overrides for.</li>
</ul>

<p>Outputs:</p>

<ul>
<li><tt>x-prime</tt>, a new token list that has been transformed by replacing
overridden modules with their replacements,</li>

<li><tt>walist-prime</tt>, the updated warning alist, and</li>

<li><tt>used</tt>, the list of overrides we actually used to transform
<tt>x</tt> into <tt>x-prime</tt>, and from which we can get all of the
requirements we need to discharge.</li>

<li><tt>modtokens</tt> is a (slow) alist that associates the name of each
module we encounter in <tt>x</tt> with its (possibly overridden) token list.
We use this eventually to check the \"requirements\" for each override.</li>

</ul>

@(def vl-apply-overrides)
@(def vl-apply-overrides-aux)"

  (defund vl-apply-overrides-aux (x db walist acc used modtokens)
    (declare (xargs :guard (and (vl-tokenlist-p x)
                                (vl-override-db-p db)
                                (vl-modwarningalist-p walist)
                                (vl-tokenlist-p acc)
                                (vl-overridelist-p used)
                                (vl-modtokensalist-p modtokens))))

; Tail recursive core.
;  - ACC holds the processed tokens of X in reverse order.
;  - USED accumulates the overrides that we use.
;  - MODTOKENS is a partial modtokens alist.

    (b* (((when (atom x))
          (mv walist acc used modtokens))

         ((unless (and (or (eq (vl-token->type (first x)) :vl-kwd-module)
                           (eq (vl-token->type (first x)) :vl-kwd-macromodule))
                       (consp (cdr x))
                       (eq (vl-token->type (second x)) :vl-idtoken)))
          ;; Not the start of a module, keep going
          (vl-apply-overrides-aux (cdr x) db walist (cons (car x) acc)
                                  used modtokens))

         ;; If we get this far, we've found "module foo" and there are overrides
         ;; for foo.  Try to collect the tokens through the end of the module.
         (modname (vl-idtoken->name (second x)))
         ((mv successp body rest)
          (vl-match-through-endmodule x))
         ((unless successp)
          (b* ((w (make-vl-warning
                   :type :vl-override-fail
                   :msg "~l0: failed to find 'endmodule' keyword corresponding ~
                         to module ~m1.~%"
                   :args (list (vl-token->loc (first x)) modname)
                   :fatalp t
                   :fn 'vl-apply-overrides-aux))
               (walist (vl-extend-modwarningalist modname w walist)))
            (vl-apply-overrides-aux (cdr x) db walist (cons (car x) acc)
                                    used modtokens)))

         ;; Now decide if we need to do an override.
         (entry   (hons-get modname db))
         ((unless entry)
          ;; No overrides for this module, keep going
          (vl-apply-overrides-aux rest db walist
                                  (revappend body acc)
                                  used
                                  (acons modname body modtokens)))

         ;; Now we've got the whole body for the module, try to find an override
         ;; that is the same.
         (- (cw "Overriding ~s0 at ~s1~%"
                modname (vl-location-string (vl-token->loc (second x)))))
         (override (vl-find-override body (cdr entry)))
         ((unless override)
;          (cw "; Can't find a suitable override.~%")
          (b* ((w (make-vl-warning
                   :type :vl-overrides-outdated
                   :msg "~l0: module ~m1 has overrides, but none of the ~
                         VL_ORIGINAL entries in the override file match its ~
                         current source code."
                   :args (list (vl-token->loc (first x)) modname)
                   :fatalp t
                   :fn 'vl-apply-overrides-aux))
               (walist (vl-extend-modwarningalist modname w walist)))
            (vl-apply-overrides-aux rest db walist
                                    (revappend body acc)
                                    used
                                    (acons modname body modtokens))))

         ;; Otherwise, successfully found an override, make the replacement.
         (replacement (vl-override->replacement override))

;         (- (cw "Override details: ~% original ~s0 ~%~% replacement ~s1 ~%~%"
;                (vl-tokenlist->string-with-spaces body)
;                (vl-tokenlist->string-with-spaces replacement)))

         (acc         (revappend-without-guard replacement acc))
         (used        (cons override used))
         (modtokens   (acons modname replacement modtokens)))

      (vl-apply-overrides-aux rest db walist acc used modtokens)))

  (local (in-theory (enable vl-apply-overrides-aux)))

  (defthm true-listp-of-vl-apply-overrides-aux-1
    (equal (true-listp (mv-nth 1 (vl-apply-overrides-aux x db walist acc used modtokens)))
           (true-listp acc)))

  (defthm true-listp-of-vl-apply-overrides-aux-2
    (equal (true-listp (mv-nth 2 (vl-apply-overrides-aux x db walist acc used modtokens)))
           (true-listp used)))

  (defthm true-listp-of-vl-apply-overrides-aux-3
    (equal (true-listp (mv-nth 3 (vl-apply-overrides-aux x db walist acc used modtokens)))
           (true-listp modtokens)))

  (defthm vl-apply-overrides-aux-basics
    (implies (and (force (vl-tokenlist-p x))
                  (force (vl-tokenlist-p acc))
                  (force (vl-override-db-p db))
                  (force (vl-modwarningalist-p walist))
                  (force (vl-overridelist-p used))
                  (force (vl-modtokensalist-p modtokens)))
             (let ((result (vl-apply-overrides-aux x db walist acc used modtokens)))
               (and (vl-modwarningalist-p (mv-nth 0 result))
                    (vl-tokenlist-p (mv-nth 1 result))
                    (vl-overridelist-p (mv-nth 2 result))
                    (vl-modtokensalist-p (mv-nth 3 result))))))


  (defund vl-apply-overrides (x db walist)
    "Returns (MV WALIST-PRIME X-PRIME USED MODTOKENS)"
    (declare (xargs :guard (and (vl-tokenlist-p x)
                                (vl-override-db-p db)
                                (vl-modwarningalist-p walist))))
    (b* (((when (atom db))
          ;; Optimization: if there are no overrides, don't do any of this
          ;; nonsense.
          (mv walist x nil nil))
         ((mv walist x-prime-rev used modtokens)
          (vl-apply-overrides-aux x db walist nil nil nil))
         (x-prime (reverse x-prime-rev)))
      (mv walist x-prime used modtokens)))

  (defttag vl-optimize)
  (progn!
   (set-raw-mode t)
   (setf (gethash 'vl-apply-overrides-aux ACL2::*never-profile-ht*) t)
   (defun vl-apply-overrides (x db walist)
     (b* (((when (atom db))
           (mv walist x nil nil))
          ((mv walist x-prime-rev used modtokens)
           (vl-apply-overrides-aux x db walist nil nil nil))
          (x-prime (nreverse x-prime-rev)))
       (mv walist x-prime used modtokens))))
  (defttag nil)

  (local (in-theory (enable vl-apply-overrides)))

  (defthm true-listp-of-vl-apply-overrides-1
    (implies (force (true-listp x))
             (true-listp (mv-nth 1 (vl-apply-overrides x db walist))))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-apply-overrides-2
    (true-listp (mv-nth 2 (vl-apply-overrides x db walist)))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-apply-overrides-3
    (true-listp (mv-nth 3 (vl-apply-overrides x db walist)))
    :rule-classes :type-prescription)

  (defthm vl-apply-overrides-basics
    (implies (and (force (vl-tokenlist-p x))
                  (force (vl-override-db-p db))
                  (force (vl-modwarningalist-p walist)))
             (let ((result (vl-apply-overrides x db walist)))
               (and (vl-modwarningalist-p (mv-nth 0 result))
                    (vl-tokenlist-p (mv-nth 1 result))
                    (vl-overridelist-p (mv-nth 2 result))
                    (vl-modtokensalist-p (mv-nth 3 result)))))))



(defsection vl-check-override-requirements
  :parents (overrides)
  :short "Check that all of the requirements from overrides are met."

  :long "<p><b>Signature:</b> @(call vl-check-override-requirements) returns
an updated <tt>walist</tt>.</p>

<p>As inputs, we are given the actual list of all <tt>overrides</tt> that were
actually applied, and the full <tt>modtokens</tt> alist which associates every
module name with all of the tokens that comprise its (perhaps overridden)
body.  We are also given <tt>walist</tt>, a @(see vl-modwarningalist-p) that
will be applied to the list of tokens after our check is done.</p>

<p>We extend this warning alist with a fatal warning for any overridden module
whose requirements were not met.</p>

<p><tt>modtokens</tt> is expected to be a fast alist.</p>

@(def vl-check-override-requirements)"

  (defund vl-check-override-requirements-aux (required-names override modtokens walist)
    (declare (xargs :guard (and (string-listp required-names)
                                (vl-override-p override)
                                (vl-modtokensalist-p modtokens)
                                (vl-modwarningalist-p walist))))
    (b* (((when (atom required-names))
          walist)
         (actual-body1      (cdr (hons-get (car required-names) modtokens)))
         (acceptable-bodies (vl-override->requirements override))
         (acceptablep       (vl-tokenlist-equiv-to-some-p actual-body1 acceptable-bodies))
         ((when acceptablep)
          (vl-check-override-requirements-aux (cdr required-names) override modtokens walist))
         (modname (vl-override->name override))
         (w (make-vl-warning
             :type :vl-overrides-outdated
             :msg "The override for module ~m0 has VL_REQUIRE entries for ~m1, ~
                   but these requirements are unmet.  This probably means the ~
                   definition of ~m1 has changed and that the override for ~m0 ~
                   needs to be updated to accommodate this change."
             :args (list modname (car required-names))
             :fatalp t
             :fn 'vl-check-override-requirements-aux))
         (walist (vl-extend-modwarningalist modname w walist)))
      (vl-check-override-requirements-aux (cdr required-names) override modtokens walist)))

  (defthm vl-modwarningalist-p-of-vl-check-override-requirements-aux
    (implies (and (force (string-listp required-names))
                  (force (vl-override-p override))
                  (force (vl-modtokensalist-p modtokens))
                  (force (vl-modwarningalist-p walist)))
             (vl-modwarningalist-p
              (vl-check-override-requirements-aux required-names override modtokens walist)))
    :hints(("Goal" :in-theory (enable vl-check-override-requirements-aux))))


  (defund vl-check-override-requirements (overrides modtokens walist)
    (declare (xargs :guard (and (vl-overridelist-p overrides)
                                (vl-modtokensalist-p modtokens)
                                (vl-modwarningalist-p walist))))
    (b* (((when (atom overrides))
          walist)
         (override1       (car overrides))
         (required-names1 (vl-override-requirement-names override1))
         (walist          (vl-check-override-requirements-aux required-names1
                                                              override1
                                                              modtokens
                                                              walist)))
      (vl-check-override-requirements (cdr overrides) modtokens walist)))

  (defthm vl-modwarningalist-p-of-vl-check-override-requirements
    (implies (and (force (vl-overridelist-p overrides))
                  (force (vl-modtokensalist-p modtokens))
                  (force (vl-modwarningalist-p walist)))
             (vl-modwarningalist-p
              (vl-check-override-requirements overrides modtokens walist)))
    :hints(("Goal" :in-theory (enable vl-check-override-requirements)))))

