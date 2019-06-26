; ACL2 Getopt Library
; Copyright (C) 2013 Centaur Technology
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

(in-package "GETOPT")
(include-book "std/util/top" :dir :system)
(include-book "std/strings/case-conversion" :dir :system)
(include-book "std/strings/strprefixp" :dir :system)
(include-book "std/strings/subseq" :dir :system)
(include-book "std/strings/strpos" :dir :system)
(include-book "parsers")
(include-book "xdoc/word-wrap" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)


(defxdoc getopt
  :parents (acl2::command-line)
  :short "A library for processing command-line option."

  :long "<h3>Introduction</h3>

<p><b>Getopt</b> is a tool for writing command-line programs in ACL2.  It is
similar in spirit to <a
href='http://perldoc.perl.org/Getopt/Long.html'>Getopt::Long</a> for Perl, <a
href='https://rubygems.org/gems/trollop/'>Trollop</a> for Ruby, and so on.</p>

<p>We basically extend @(see defaggregate) with a command-line parsing layer.
This has some nice consequences:</p>

<ul>

<li>Argument parsing gives you an ordinary aggregate that can have nice, strong
type guarantees on its fields.</li>

<li>It's very easy to add new options, pass the arguments throughout your
program, etc.</li>

<li>You get excellent integration with @(see xdoc), i.e., documentation is
mostly automated.</li>

<li>We can automatically generate usage messages that stay up to date as you
add new arguments.</li>

</ul>

<p>To make Getopt more automatic, we insist on some typical Unix conventions.
We support options like these:</p>

@({
    --help              Long names use two dashes.
    --color red         Values can use spaces or = signs.
    --shape=square

    -c red              Short aliases use one dash.  Plain
    -s=square           aliases (with no arguments) can be
    -xfvz               bundled.  E.g., -xfvz instead of
                        -x -f -v -z.
})

<p>We insist on two dashes for long options, and one dash for short options.
This lets us support mixing options in with other arguments like file names.
For instance, after parsing something like:</p>

@({ myprogram --depth 3 --verbose foo.java bar.java -o report.txt })

<p>You get two things out:</p>

<ul>

<li>A proper options structure with <i>depth</i> @('3'), <i>verbose</i> @('t'),
and <i>output</i> @('report.txt').</li>

<li>The \"extra\" arguments, i.e., @('(\"foo.java\" \"bar.java\")').</li>

</ul>

<p>For rare cases where you need to process a file that starts with @('-'), the
special syntax @('--') is a marker that means \"stop looking for options
here.\"</p>

<h3>Using Getopts</h3>

<p>Getopts is an ordinary library with no ttags.  To load it, just include the
top book:</p>

@({ (include-book \"centaur/getopt/top\" :dir :system) })

<p>After that, the main command is @(see defoptions).</p>

<p>There is also a demo of how to use Getopt: @(see getopt-demo::demo-p).</p>")


(defsection defoptions
  :parents (getopt)
  :short "Define a structure for representing command line options, and a
command-line parser that creates this structure."

  :long "<p>@('defoptions') is the main command provided by @(see getopt)
library.  It is really a thin wrapper around @(see defaggregate), where each
field can have some additional keywords that have certain effects.</p>


<h3>A Basic Example</h3>

@({
    (defoptions myopts
      :parents (myprogram)
      :short \"Command line options for my program.\"
      :tag :myopts
      ((help    booleanp
                \"Print a help message and exit with status 0.\")
       (outfile stringp
                \"Where to write the output.\"
                :default \"a.out\")))
})

<p>So far, this is identical to @('defaggregate') except that we use
@('defoptions') instead.  Indeed, the first thing the above @('defoptions')
form expands into is an ordinary @('defaggregate') call.  The @('defaggregate')
introduces a @('myopts-p') structure as usual, complete with the usual
accessors like @('myopts->help'), a @('make-myopts') macro, etc.</p>

<p>But in addition to introducing an aggregate, @('defoptions') introduces a
usage message and a command-line parsing function.</p>

<p>For @('myopts') above, the usage message, @('*myopts-usage*'), will just
be:</p>

@({
    --help                Print a help message and exit with status 0.
    --outfile=ARG         Where to write the output.
})

<p>So that's handy, and below we'll see how to customize this message a bit.
You can probably easily imagine incorporating this into your program's
@('--help') message.</p>

<p>Meanwhile, the parsing function, @('parse-myopts'), allows you to parse a
@(see string-listp) into a @('myopts-p') structure.  The signature of
@('parse-myopts') is:</p>

@({
 (parse-myopts args &key (init '*default-myopts*))
  -->
 (mv errmsg result extra)
})

<p>The @('args') here are just a string list.  Normally, if you were writing a
real command-line program with ACL2, you would normally get the @('args') to
process by calling @(see oslib::argv).  But for testing and development, we can
just use any old string list we want.</p>

<p>Usually you won't care about the optional @(':init') argument: it just lets
you use a custom @('myopts') structure as the starting point, instead of
starting from the default structure (which has the @(':default') value for each
field.)</p>

<p>Command-line parsing can fail because the user might type in something
crazy.  For instance, they might try to run @('myprogram --hlep') instead of
@('myprogram --help').  The @('errmsg') will be NIL if everything is okay, or
else will be an error message produced by @(see msg), which is suitable for
printing with the @(see fmt) directive @('~@').  For example:</p>

@({
    (b* (((mv errmsg result extra)
           (parse-myopts '(\"--hlep\")))
          ((when errmsg)
           (cw \"Error processing options!~%\")
           (cw \"~@0~%\" errmsg)
           nil))
       result)
})

<p>Will print out:</p>

@({
    Error processing options!
    Unrecognized option --hlep
})

<p>When command-line processing is successful, the main return value,
@('result'), is a valid @('myopts-p') structure that contains the various
settings, and the @('extra') return value is a list of any command-line options
that we skipped because they didn't look like options.  For example:</p>

@({
    (b* (((mv ?errmsg result extra)
          (parse-myopts
           '(\"foo.java\" \"--outfile\" \"report.txt\" \"bar.java\"))))
      (list :result result
            :extra extra))
})

<p>Will return:</p>

@({
    (:RESULT (:MYOPTS (HELP)
                      (OUTFILE . \"report.txt\"))
     :EXTRA (\"foo.java\" \"bar.java\"))
})


<h3>Adding Short Aliases (-h, -o, ...)</h3>

<p>Ordinarily a program that takes options like @('--help') and @('--outfile')
will also have shorter ways to give these options, e.g., @('-h') and @('-o').
You can set up these short names by just adding an @(':alias') to your fields,
like this:</p>

@({
    (defoptions myopts
      :parents (myprogram)
      :short \"Command line options for my program.\"
      :tag :myopts
      ((help    booleanp
                \"Print a help message and exit with status 0.\"
                :alias #\\h)
       (outfile stringp
                \"Where to write the output.\"
                :default \"a.out\"
                :alias #\\o)))
})

<p>Note that the usage message gets automatically extended to take these
into account.  @('*myopts-usage*') becomes:</p>

@({
    -h,--help             Print a help message and exit with status 0.
    -o,--outfile=ARG      Where to write the output.
})


<h3>Custom Option Types</h3>

<p>The @('myopts-p') structure is especially simple in that it only contains
@(see booleanp) and @(see stringp) fields.  Getopt has built-in @(see parsers)
for these types, as well as for @(see natp) and @(see posp).  But in some cases
these may not be sufficient.</p>

<p>If you need something fancier, you can write your own parser.  See @(see
custom-parser) for details.  After writing your own @('parse-foo') function, you can
either register it as the default for all @('foo-p') fields, or you can install
it just as the parser for a particular field using the @(':parser') option.
For instance:</p>

@({
       (outfile stringp
                \"Where to write the output.\"
                :default \"a.out\"
                :alias #\\o
                ;; redundant, but acceptable, to explicitly say to use the
                ;; default stringp parser
                :parser getopt::parse-string)
})


<h3>Changing Option Names</h3>

<p>By default the option name is just automatically inferred from the field
name.  In rare cases you might want to change this, e.g., perhaps you prefer to
use field-names like @('verbosep') instead of @('verbose').  You can accomplish
this with a custom @(':longname') for the field, e.g.,</p>

@({
    (defoptions myopts
      :parents (myprogram)
      :short \"Command line options for my program.\"
      :tag :myopts
      ((verbosep booleanp
                 :longname \"verbose\"
                 \"Print excessive debugging information.\")
       (help    booleanp
                \"Print a help message and exit with status 0.\"
                :alias #\\h)
       (outfile stringp
                \"Where to write the output.\"
                :default \"a.out\"
                :alias #\\o)))
})


<h3>List Types</h3>

<p>By default options are <i>unmergeable</i>, meaning that it is an error to
try to specify them more than once.  This is generally sensible behavior, e.g.,
you probably don't want to support things like:</p>

@({ myprog --username jared --username sol ... })

<p>But occasionally you want to have an option that \"stacks\" with other
options.  For instance, in our Verilog parsing stuff we often want a \"search
path\" that is a list of directories.</p>

<p>To facilitate this, the @(':merge') option can be used to specify a custom
\"merging function\" (typically @(see cons)) that can extend a field with a new
value.  For instance, here's basically the canonical way to have an option that
lets the user write:</p>

@({ myprog --dir /dir1 --dir /dir2 ... })

<p>And turns them into a @('dirs') field:</p>

@({
      (dirs string-listp
            :longname \"dir\"
            :parser getopt::parse-string
            :merge cons)
})

<p>Note that this will actually accumulate the options in the reverse
order (because @(see cons) extends the front of a list).  This is easily
corrected for by using some kind of @('push') function instead of @('cons'), or
by reversing the list at the end.  See @(see getopt-demo::demo-p) for an
example.</p>


<h3>Customizing Usage Messages</h3>

<p>By default we reuse the @(see xdoc) documentation for a field as its usage
message.  If you want to have a separate usage message instead, you can just
add one, e.g., via @(':usage \"blah blah\"').</p>

<p>For options that take arguments, you may occasionally want to name the
argument.  That is, by default, we will produce usage messages like:</p>

@({
    --port ARG      The port to connect to.
    --out ARG       Where to write the output.
})

<p>But maybe you'd rather have this print as:</p>

@({
    --port PORT     The port to connect to.
    --out FILE      Where to write the output.
})

<p>You can do this by adding, e.g., @(':argname \"PORT\"') and @(':argname
\"FILE\"') to the port/out fields.</p>")


(define split-equals ((x stringp))
  :returns (mv (pre stringp
                    :rule-classes :type-prescription)
               (post (or (not post)
                         (stringp post))
                     :rule-classes :type-prescription))
  (b* ((x (str::str-fix x))
       (pos (str::strpos "=" x))
       ((when pos)
        (mv (subseq x 0 pos)
            (subseq x (+ 1 pos) nil))))
    (mv x nil)))


#||
(split-equals "foo=bar") --> (mv "foo" "bar")
||#

(program)

(defconst *extra-fields-for-defoptions*
  '(:longname   ;; Full name for this option, like "verbose".  Overrides
                ;; the field name, if supplied.

    :alias      ;; Short alias for this option, like #\v, if desired.

    :parser     ;; What function will parse the arguments.  Automatically
                ;; inferred from the field type, if not specified.

    :merge      ;; How to merge the new values with the old, if applicable,
                ;; e.g., for list-type values.

    :usage      ;; A custom usage message, if one is needed instead of just
                ;; using the formal's documentation

    :argname    ;; Name for this argument in the usage message, e.g., you
                ;; might want the message to look like
                ;;
                ;;   --port PORT     The port to connect to on the server.
                ;;
                ;;   --out FILE      Where to write the output
                ;;
                ;; And so on, so you'd use :argnames like "PORT" and "FILE"
                ;; The default is "ARG" unless it's a plain option.

    :hide       ;; A hidden option.  This requires that there is no alias,
                ;; usage message, argname, or any of that.  This is generally
                ;; useful for options you're going to fill in yourself, like
                ;; file names.
    ))

(define formal->longname ((x formal-p))
  :parents (getopt)
  :returns (longname stringp)
  (b* (((formal x) x)
       (longname (cdr (assoc :longname x.opts)))
       ((when (and (stringp longname)
                   (not (equal longname ""))))
        longname)
       ((when longname)
        (raise "In ~x0, :longname must be ~s1, but found: ~x2"
               x.name
               (if (stringp longname) "nonempty" "a string")
               longname)
        ""))
    ;; Else, no longname at all, by default use the name of the formal.
    (str::downcase-string (symbol-name x.name))))

(defprojection formallist->longnames (x)
  (formal->longname x)
  :guard (formallist-p x)
  :result-type string-listp
  :optimize nil)


(define formal->alias ((x formal-p))
  :parents (getopt)
  :returns (alias (or (not alias)
                      (characterp alias)))
  (b* (((formal x) x)
       (alias (cdr (assoc :alias x.opts)))
       ((when (characterp alias))
        alias)
       ((when alias)
        (raise "In ~x0, :alias must be a character, but found ~x1."
               x.name alias)
        nil))
    ;; No automatic inference of an alias
    nil))

(defprojection formallist->aliases (x)
  (formal->alias x)
  :guard (formallist-p x)
  ;; :result-type maybe-character-listp
  :optimize nil)



(define formal->parser ((x formal-p) (world plist-worldp))
  :parents (getopt)
  :returns (parser-fn symbolp)
  (b* (((formal x) x)
       (parser (cdr (assoc :parser x.opts)))
       ((when parser)
        (check-plausibly-a-parser-p x.name parser world)
        parser)
       ;; Else, see if there is a default parser for this type
       ((unless (and (tuplep 2 x.guard)
                     (equal (second x.guard) x.name)))
        (raise "In ~x0, there's no :parser and the type isn't simple enough ~
                to infer a default." x.name))
       (predicate (first x.guard))
       (parser (default-getopt-parser predicate world))
       ((when parser)
        (check-plausibly-a-parser-p x.name parser world)
        parser))
    (raise "In ~x0, there's no :parser and there's no default parser for type ~
            ~x1." x.name predicate)))

(defprojection formallist->parsers (x world)
  (formal->parser x world)
  :guard (and (formallist-p x)
              (plist-worldp world))
  :result-type symbol-listp
  :optimize nil)


(define formal->merge ((x formal-p))
  :parents (getopt)
  :returns (merge-fn symbolp)
  (b* (((formal x) x)
       (merge (cdr (assoc :merge x.opts)))
       ((unless (symbolp merge))
        (raise "In ~x0, :merge is not even a symbol: ~x1." x.name merge)))
    merge))

(defprojection formallist->merges (x)
  (formal->merge x)
  :guard (formallist-p x)
  :result-type symbol-listp
  :optimize nil)


(define formal->usage ((x formal-p))
  :parents (getopt)
  :returns (usage stringp)
  (b* (((formal x) x))
    (or (cdr (assoc :usage x.opts))
        x.doc)))

(define formal->argname ((x formal-p) (world plist-worldp))
  :parents (getopt)
  :returns (argname stringp)
  (b* (((formal x) x)
       (custom (assoc :argname x.opts))
       ((when (stringp (cdr custom)))
        (cdr custom))
       ((when custom)
        (raise "In ~x0, :argname is not even a stringp: ~x1."
               x.name (cdr custom)))
       (parser (formal->parser x world))
       ((when (equal parser 'parse-plain))
        ""))
    "ARG"))

(define formal->hiddenp ((x formal-p))
  :parents (getopt)
  :returns (longname stringp)
  (b* (((formal x) x)
       (hide (cdr (assoc :hide x.opts)))
       ((when hide)
        t))
    nil))

(define drop-hidden-options ((x formallist-p))
  :returns (subset formallist-p)
  (cond ((atom x)
         nil)
        ((formal->hiddenp (car x))
         (drop-hidden-options (cdr x)))
        (t
         (cons (car x) (drop-hidden-options (cdr x))))))

(define sanity-check-formals ((basename symbolp)
                              (x        formallist-p)
                              (world    plist-worldp))
  :parents (getopt)
  :short "Make sure longnames and aliases are unique, every field has a parser,
and so forth.  This only applies to visible options."

  (b* ((longnames (formallist->longnames x))
       ((unless (uniquep longnames))
        (raise "In ~x0, multiple fields have :longname ~&1."
               basename (duplicated-members longnames)))

       (aliases (remove nil (formallist->aliases x)))
       ((unless (uniquep aliases))
        (raise "In ~x0, multiple fields have :alias ~&1."
               basename (duplicated-members aliases)))

       ;; These are just doing the basic checks...
       (?parsers (formallist->parsers x world))
       (?merges  (formallist->merges x)))
    t))

(defun parser-name (basename)
  (intern-in-package-of-symbol
   (str::cat "PARSE-" (symbol-name basename))
   basename))

(defun parser-name-aux (basename)
  (intern-in-package-of-symbol
   (str::cat "PARSE-" (symbol-name basename) "-AUX")
   basename))

(defun parser-name-long (basename)
  (intern-in-package-of-symbol
   (str::cat "PARSE-" (symbol-name basename) "-LONG")
   basename))

(defun parser-name-bundle (basename)
  (intern-in-package-of-symbol
   (str::cat "PARSE-" (symbol-name basename) "-BUNDLE")
   basename))

(defun parser-name-short->long (basename)
  (intern-in-package-of-symbol
   (str::cat "PARSE-" (symbol-name basename) "-SHORT->LONG")
   basename))

(defun parser-name-short->long-list (basename)
  (intern-in-package-of-symbol
   (str::cat "PARSE-" (symbol-name basename) "-SHORT->LONG-LIST")
   basename))

(defun default-name (basename)
  (intern-in-package-of-symbol
   (str::cat "*DEFAULT-" (symbol-name basename) "*")
   basename))



(define make-parse-short->long ((basename symbolp)
                                (formals  formallist-p))
  (b* ((parse-foo              (parser-name basename))
       (parse-short->long      (parser-name-short->long basename))
       (parse-short->long-list (parser-name-short->long-list basename))
       (alist                  (pairlis$ (formallist->aliases formals)
                                         (formallist->longnames formals))))
    `(progn
       (define ,parse-short->long ((alias characterp))
         :parents (,parse-foo)
         :returns (mv errmsg?
                      (longname stringp :rule-classes :type-prescription))
         (b* ((look (assoc alias ',alist))
              ((when look)
               (mv nil (cdr look))))
           (mv (msg "Unrecognized option -~s0." (implode (list alias)))
               "")))

       (define ,parse-short->long-list ((aliases character-listp))
         :parents (,parse-foo)
         :returns (mv (errmsg)
                      (longnames string-listp))
         (b* (((when (atom aliases))
               (mv nil nil))
              ((mv err longname) (,parse-short->long (car aliases)))
              ((when err)
               (mv err nil))
              ((mv err rest) (,parse-short->long-list (cdr aliases))))
           (mv err (cons longname rest)))
         ///
         (defthm ,(intern-in-package-of-symbol
                   (cat "TRUE-LISTP-OF-" (symbol-name parse-short->long-list))
                   parse-short->long-list)
           (true-listp (mv-nth 1 (,parse-short->long-list aliases)))
           :rule-classes :type-prescription)))))

(define collect-plain-options ((x formallist-p) (world plist-worldp))
  :returns (subset formallist-p)
  (cond ((atom x)
         nil)
        ((equal (formal->parser (car x) world) 'parse-plain)
         (cons (car x) (collect-plain-options (cdr x) world)))
        (t
         (collect-plain-options (cdr x) world))))

(define make-parse-long-cases ((basename symbolp)
                               (formals  formallist-p)
                               (world    plist-worldp))
  (b* (((when (atom formals))
        nil)
       (field    (formal->name (car formals)))
       (longname (formal->longname (car formals)))
       (parser   (formal->parser (car formals) world))
       (merge    (formal->merge (car formals)))
       (accessor (std::da-accessor-name basename field))
       (changer  (std::da-changer-name basename))
       (kwd      (intern$ (symbol-name field) "KEYWORD"))
       (case1
        `((equal longname ,longname)
          (b* (;; If an option isn't mergeable, we don't allow it to be given
               ;; multiple times.
               ,@(and (not merge)
                      '(((when (member-equal longname seen))
                         (mv (msg "Option --~s0 given multiple times" longname)
                             acc args))))

               ((mv err value rest) (,parser (cat "--" longname) explicit-val args))
               ((when err)
                (mv err acc args))
               ;; If an option is mergeable, we need to merge this new value
               ;; into the old one.
               ,@(and merge
                      `((old-value (,accessor acc))
                        (value     (,merge value old-value))))
               ;; At this point everything should be good.
               (acc (,changer acc ,kwd value)))
            (mv nil acc rest)))))
    (cons case1
          (make-parse-long-cases basename (cdr formals) world))))

(define make-parse-long ((basename symbolp)
                         (pred     symbolp)
                         (formals  formallist-p)
                         (world    plist-worldp))
  (b* ((parse-foo  (parser-name basename))
       (parse-long (parser-name-long basename))
       (foop       (std::da-recognizer-name basename pred)))
    `(define ,parse-long
       :parents (,parse-foo)
       ((longname stringp
                  "Longname we've just found, e.g., \"foo\" if we've just
                   seen @('--foo=bar').")
        (explicit-val (or (not explicit-val)
                          (stringp explicit-val))
                      "Any explicit value passed to this option, e.g.,
                       \"bar\" if we've just seen @('--foo=bar'), or NIL
                       if we've just seen @('--foo').")
        (args string-listp
              "Remaining arguments <b>past longname</b>.")
        (acc  ,foop
              "Structure we're updating")
        (seen string-listp
              "List of longnames that we've seen so far."))
       :returns
       (mv (errmsg "NIL on success or an error message.")
           (acc    ,foop
                   :hyp (force (,foop acc))
                   "Updated structure.")
           (rest   string-listp :hyp (force (string-listp args))
                   "Rest after this one."))
       (cond ,@(make-parse-long-cases basename formals world)
             (t
              ;; No matching case for these formals
              (mv (msg "Unrecognized option --~s0" longname)
                  acc
                  args)))
       ///
       (defthm ,(intern-in-package-of-symbol
                 (cat (symbol-name parse-long) "-MAKES-PROGRESS")
                 basename)
         (<= (len (mv-nth 2 (,parse-long longname explicit-val args acc seen)))
             (len args))
         :rule-classes ((:rewrite) (:linear))))))

(define make-parse-bundle ((basename symbolp)
                           (pred     symbolp))
  (b* ((parse-foo    (parser-name basename))
       (parse-long   (parser-name-long basename))
       (parse-bundle (parser-name-bundle basename))
       (foop         (std::da-recognizer-name basename pred)))
    `(define ,parse-bundle
       :parents (,parse-foo)
       ((longnames string-listp "The already-expanded out names of the bundled
                                 options, with no dashes.")
        (args      string-listp "Remaining arguments <b>past longname</b>.")
        (acc       ,foop        "Structure we're updating")
        (seen      string-listp "List of longnames that we've seen so far."))
       :returns
       (mv (errmsg "NIL on success or an error message.")
           (acc    ,foop :hyp (force (,foop acc)))
           (seen   string-listp :hyp (and (force (string-listp longnames))
                                          (force (string-listp seen))))
           (rest   string-listp :hyp (force (string-listp args))))
       (b* (((when (atom longnames))
             (mv nil acc seen args))
            ((mv err acc rest)
             (,parse-long (car longnames) nil args acc seen))
            ((when err)
             (mv err acc seen rest))
            (seen (cons (car longnames) seen)))
         (,parse-bundle (cdr longnames) rest acc seen))
       ///
       (defthm ,(intern-in-package-of-symbol
                 (cat (symbol-name parse-bundle) "-MAKES-PROGRESS")
                 basename)
         (<= (len (mv-nth 3 (,parse-bundle longnames args acc seen)))
             (len args))
         :rule-classes ((:rewrite) (:linear))))))

(define make-parse-aux ((basename symbolp)
                        (pred     symbolp)
                        (formals  formallist-p)
                        (world    plist-worldp))
  (b* ((parse-foo    (parser-name basename))
       (parse-aux    (parser-name-aux basename))
       (parse-long   (parser-name-long basename))
       (parse-short->long      (parser-name-short->long basename))
       (parse-short->long-list (parser-name-short->long-list basename))
       (parse-bundle (parser-name-bundle basename))
       (foop         (std::da-recognizer-name basename pred))
       (plain        (collect-plain-options formals world))
       (plain-longnames (formallist->longnames plain)))
    `(define ,parse-aux
       :parents (,parse-foo)
       ((args    string-listp "Arguments we're processing")
        (acc     ,foop        "Structure we're building.")
        (seen    string-listp "List of longnames that we've seen so far.")
        (skipped string-listp "Arguments we've skipped since they don't go with
                               options, in reverse order."))
       :returns (mv errmsg
                    (result  ,foop :hyp (force (,foop acc)))
                    (skipped string-listp
                             :hyp (and (force (string-listp skipped))
                                       (force (string-listp args)))))
       :measure (len args)
       (b* (((when (or (atom args)
                       (equal (car args) "--")))
             ;; Successfully processed all the arguments that belong to us.  We
             ;; leave the -- in, so the programmer can choose to process it, if
             ;; they want.
             (mv nil acc (revappend skipped args)))

            ((unless (str::strprefixp "-" (car args)))
             ;; Not an option.  Skip it.
             (,parse-aux (cdr args) acc seen (cons (car args) skipped)))

            ((when (str::strprefixp "--" (car args)))
             (b* (((mv longname explicit-value)
                   (split-equals (subseq (car args) 2 nil)))
                  ((mv err acc rest)
                   (,parse-long longname explicit-value (cdr args) acc seen))
                  ((when err)
                   (mv err acc rest))
                  (seen (cons longname seen)))
               (,parse-aux rest acc seen skipped)))

            ;; Else, just one leading dash.
            ((mv shortnames explicit-value)
             (split-equals (subseq (car args) 1 nil)))

            (aliases (explode shortnames))
            ((when (atom aliases))
             ;; Very weird, either a stray dash or something like -= or -=blah.
             ;; I guess we'll tolerate this but just treat it as a non-option
             ;; by skipping it?
             (,parse-aux (cdr args) acc seen (cons (car args) skipped)))

            ((when (atom (cdr aliases)))
             ;; A single alias.  This is easy, just try to translate it into a
             ;; long option and handle it normally.
             (b* ((alias (car aliases))
                  ((mv err longname) (,parse-short->long alias))
                  ((when err)
                   (mv err acc args))
                  ((mv err acc rest)
                   (,parse-long longname explicit-value (cdr args) acc seen))
                  ((when err)
                   (mv err acc rest))
                  (seen (cons longname seen)))
               (,parse-aux rest acc seen skipped)))

            ;; Else, an option bundle.  Try to translate them into longnames.
            ((mv err longnames) (,parse-short->long-list aliases))
            ((when err)
             (mv err acc args))
            ((when explicit-value)
             (mv (msg "Option bundle ~s0 is not allowed (bundles can't have ~
                       arguments)." (car args))
                 acc args))

            ;; We can only bundle options if they are plain, so check for that
            ;; now.  The HIDE here is just to prevent case splits.
            (illegal-to-bundle (set-difference-equal longnames ',plain-longnames))
            ((when illegal-to-bundle)
             (mv (msg "Option bundle ~s0 is not allowed (--~s1 needs an argument)"
                      (car args)
                      (car illegal-to-bundle))
                 acc args))
            ((mv err acc seen rest)
             (,parse-bundle longnames (cdr args) acc seen))
            ((when err)
             (mv err acc rest)))
         (,parse-aux rest acc seen skipped)))))

(define make-parse ((basename symbolp) (pred symbolp))
  (b* ((parse-foo   (parser-name basename))
       (parse-aux   (parser-name-aux basename))
       (default-foo (default-name basename))
       (foop        (std::da-recognizer-name basename pred))
       (foop-link (b* ((acc (str::revappend-chars "<see topic='" nil))
                       (acc (xdoc::file-name-mangle foop acc))
                       (acc (str::revappend-chars "'>" acc))
                       (acc (xdoc::sym-mangle foop foop nil acc))
                       (acc (str::revappend-chars "</see>" acc)))
                    (str::rchars-to-string acc))))
    `(define ,parse-foo
       :parents (,foop)
       :short ,(str::cat "Parse arguments from the command line into a "
                         foop-link " aggregate.")
       ((args string-listp "The command line arguments to parse, which is
                            typically derived from @(see oslib::argv).")
        &key
        ((init ,foop ,(str::cat "An initial " foop-link " to start from, which
                                 gives the default values for each field."))
         ',default-foo))
       :returns
       (mv (errmsg "NIL on success, or an error message produced by @(see msg),
                    suitable for printing the @(see fmt) directive @('~@').")
           (result ,foop
                   :hyp (force (,foop init))
                   "An updated version of @('init') where the command-line
                    arguments have been applied.  On any error, this may be
                    only partially updated.")
           (extra  string-listp
                   :hyp (force (string-listp args))
                   "Any other arguments in @('args') that were not recognized
                    as options.  Typically this might include the \"main\"
                    arguments to a program, e.g., file names, etc., that aren't
                    associated with --options."))
       :long "<p>This is an ordinary command line parser, automatically
              produced by @(see getopt).</p>"
       (,parse-aux args init nil nil))))

(defsection defoption-lemmas
  (logic)

  (defthm defoptions-lemma-1
    (equal (string-listp (append x y))
           (and (string-listp (list-fix x))
                (string-listp y))))

  (defthm defoptions-lemma-2
    (equal (string-listp (acl2::rev x))
           (string-listp (list-fix x)))
    :hints(("Goal" :induct (len x))))

  (defthm defoptions-lemma-3
    (implies (string-listp x)
             (string-listp (list-fix x))))

  (defthm defoptions-lemma-4
    (implies (str::strprefixp "--" x)
             (<= 2 (len (explode x))))
    :rule-classes ((:rewrite) (:linear)))

  (defthm defoptions-lemma-5
    (implies (character-listp x)
             (equal (characterp (car x))
                    (consp x))))

  (defthm defoptions-lemma-6
    (implies (character-listp x)
             (equal (characterp (second x))
                    (consp (cdr x)))))

  (defthm defoptions-lemma-7
    (implies (character-listp x)
             (character-listp (cdr x))))

  (defthm defoptions-lemma-8
    (implies (str::strprefixp "-" x)
             (<= 1 (len (explode x))))
    :rule-classes ((:rewrite) (:linear)))

  (def-ruleset defoptions-lemmas
    '(defoptions-lemma-1
      defoptions-lemma-2
      defoptions-lemma-3
      defoptions-lemma-4
      defoptions-lemma-5
      defoptions-lemma-6
      defoptions-lemma-7
      acl2::revappend-removal
      acl2::append-to-nil
      acl2::list-fix-when-true-listp
      str::stringp-of-subseq))

  (in-theory (disable* defoptions-lemmas)))



(defconst *ind-col* 26)
(defconst *wrap-col* 72)

(define usage-message-part ((title  stringp)
                            (detail stringp)
                            (acc    character-listp))
  :returns (new-acc character-listp)
  (b* ((title (cat "    " title))
       (acc   (str::revappend-chars title acc))
       (acc
        (if (> (length title) (- *ind-col* 3))
            ;; Title is really long.  Give it its own line.
            (b* ((acc (cons #\Newline acc)))
              (make-list-ac *ind-col* #\Space acc))
          ;; Title fits nicely, space out to *ind-col*.
          (make-list-ac (- *ind-col* (length title))
                        #\Space acc)))
       (x   (xdoc::normalize-whitespace detail))
       (acc (xdoc::word-wrap-paragraph-aux x 0 (length x)
                                           *ind-col*
                                           *wrap-col*
                                           *ind-col*
                                           acc))
       (acc (xdoc::remove-spaces-from-front acc))
       (acc (cons #\Newline acc)))
    acc))

#||
(str::rchars-to-string
 (usage-message-part "-o,--output=FILE"
                     "Lorem ipsum blah blah.  This message has random newlines
                      in it, like something you might write in the middle of an
                      aggregate's documentation, etc."  nil))

(str::rchars-to-string
 (usage-message-part "--a-really-long-option=FILE"
                     "Lorem ipsum blah blah.  This message has random newlines
                      in it, like something you might write in the middle of an
                      aggregate's documentation, etc."
                     nil))
||#

(define make-usage-aux ((x     formal-p)
                        (world plist-worldp)
                        (acc   character-listp))
  (b* ((longname (formal->longname x))      ; e.g., "outfile"
       (alias    (formal->alias x))         ; e.g., #\o
       (argname  (formal->argname x world)) ; e.g., "FILE"
       (usage    (formal->usage x))         ; e.g., "where to write ..."

       (title (str::cat
               (if alias (implode (list #\- alias #\,)) "")
               "--"
               longname
               (if (equal argname "") "" "=")
               argname)))
    (usage-message-part title usage acc)))

(define make-usage-loop ((x     formallist-p)
                         (world plist-worldp)
                         (acc   character-listp))
  (if (atom x)
      acc
    (let ((acc (make-usage-aux (car x) world acc)))
      (make-usage-loop (cdr x) world acc))))

(define make-usage ((x     formallist-p)
                    (world plist-worldp))
  (str::rchars-to-string (make-usage-loop x world nil)))



(define defoptions-fn ((info  std::agginfo-p)
                       (world plist-worldp))
  (b* (((std::agginfo info) info)
       (visible      (drop-hidden-options info.efields))
       (- (sanity-check-formals info.name visible world))
       (foop         (std::da-recognizer-name info.name info.pred))
       (usage-const  (intern-in-package-of-symbol
                      (cat "*" (symbol-name info.name) "-USAGE*")
                      info.name))
       (usage-msg    (make-usage visible world))
       (usage-html   (b* ((acc (str::revappend-chars "<code>" nil))
                          (acc (xdoc::simple-html-encode-chars
                                (explode usage-msg) acc))
                          (acc (str::revappend-chars "</code>" acc)))
                       (str::rchars-to-string acc)))
       (events
        `(progn
           (local (in-theory (e/d* (defoptions-lemmas)
                                   (str::strprefixp
                                    set-difference-equal))))

           ,(make-parse-long info.name info.pred visible world)
           ,(make-parse-short->long info.name visible)
           ,(make-parse-bundle info.name info.pred)
           ,(make-parse-aux info.name info.pred visible world)
           ,(make-parse info.name info.pred)
           (defsection ,usage-const
             :parents (,foop)
             :short "Automatically generated usage message."
             :long ,usage-html
             (defconst ,usage-const ',usage-msg))
           (value-triple '(defoptions ,info.name)))))
    events))

(defmacro defoptions (name &rest args)
  (let ((default-foo (default-name name)))
    `(progn
       (defaggregate ,name
         :extra-field-keywords ,*extra-fields-for-defoptions*
         . ,args)
       (defconst ,default-foo (,(std::da-maker-name name)))
       (make-event
        (b* ((world   (w state))
             (agginfo (std::get-aggregate ',name world)))
          (value
           (defoptions-fn agginfo world)))))))
