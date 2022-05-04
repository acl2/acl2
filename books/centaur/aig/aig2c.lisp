; Centaur AIG Library
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "ACL2")
(include-book "std/util/top" :dir :system)
(include-book "centaur/vl/util/defs" :dir :system)
(include-book "centaur/vl/util/namedb" :dir :system)
(include-book "aig-base")
(include-book "aig-vars-ext")
(local (include-book "std/typed-lists/string-listp" :dir :system))

(local (defthm stringp-of-lookup-when-string-listp-of-alist-vals
         (implies (string-listp (alist-vals map))
                  (equal (stringp (cdr (hons-assoc-equal key map)))
                         (if (hons-assoc-equal key map)
                             t
                           nil)))
         :hints(("Goal" :induct (len map)))))


(defsection aig2c
  :parents (aig-other)
  :short "Naive compiler from Hons AIGs into C/C++ code fragments."

  :long "<p>The idea here is to be able to take an AIG and embed it in a C or
C++ program.  You can tweak various aspects of the code that gets generated,
but some basic example output is:</p>

@({
  const uint32_t n_8 = inputs.a;     // prologue: initializes temp variables
  const uint32_t n_2 = inputs.b;     //   you can control the rhs'es here
  const uint32_t n_4 = inputs.c;

  const uint32_t n_3 = ~n_4;         // main aig contents
  const uint32_t n_1 = n_2 & n_3;    //   never try to understand this
  const uint32_t n_7 = ~n_8;
  const uint32_t n_6 = n_4 & n_7;
  const uint32_t n_5 = n_6 & n_1;

  out1 = n_1;                        // epilogue: extracts aigs to outputs
  out2 = n_5;                        //   you can control the lhs'es here
})

<p>We try to make relatively few assumptions about how you might actually use
this code.  Toward that goal, you may <see topic='@(url
aig2c-config-p)'>configure</see>, e.g., the names and types of the temporary
variables, and the operators used to carry out each AND and NOT operation.</p>

<p>Some high level notes:</p>

<ul>

<li>We basically turn each AIG node into one line of C/C++ code.</li>

<li>We do at least take advantage of shared structure in the AIG, and avoid
recomputing an AND node just because it has multiple fanouts.</li>

<li>We don't even do basic optimizations like using @('|') or @('^') operators,
but doing so might be useful.</li>

<li>We do nothing to smartly collapse the AIG into vectors to take advantage
of, e.g., 32-bit bitwise ANDs, or anything like that.</li>

</ul>

<p>The top-level function is @(see aig2c-compile).</p>")


(define aig2c-boolean-sanity-check-p ((type   stringp)
                                      (op-and stringp)
                                      (op-not stringp))
  :parents (aig2c-config-p)
  (b* ((tokens (str::strtok type '(#\Space #\Newline #\Tab)))
       ((unless (or (equal tokens '("bool"))
                    (equal tokens '("const" "bool"))))
        t)
       ((unless (and (equal op-and "&&")
                     (equal op-not "!")))
        (raise "Insane AIG2C configuration.  You are trying to make an aig2c ~
                configuration using bool variables, but with operators other ~
                than && and !.  The bitwise operators won't work here.  See ~
                :xdoc aig2c-config-p for more information.")))
    t))

(std::defaggregate aig2c-config
  :parents (aig2c)
  :short "Configuration object that governs how we translate an AIG into C/C++."

  :long "<p>The default configuration generates code for carry out 32-bit wide
AIG simulations on @('uint32_t')s.  Changing to, e.g., 8-bit or 64-bit wide
simulations is trivial.</p>

<p>But the C++ @('bool') type is special.  If you want to use it, you need to
make sure to use @('&&') and @('!') instead of @('&') and @('~').  Consider for
instance this C++ program:</p>

@({
  int main() {
    bool b = true;
    cout << \"B is \" << (bool)b << endl;    // Prints 'B is 1'
    b = ~b;
    cout << \"~B is \" << (bool)b << endl;   // Prints '~B is 1' (!!!)
    return 0;
  }
})

<p>We try to at least do a rudimentary check for incorrect uses of @('bool'),
but it's not any sort of foolproof thing.</p>"

  :tag :aig2c-config

  ((prefix stringp
           :rule-classes :type-prescription
           :default "_temp"
           "The naming prefix to use for generating temporary variable
            names. Typically you just want this to be something that won't
            clash with other names in the rest of your C program.  By default
            we use @('\"_temp\"').")

   (type   stringp
           :rule-classes :type-prescription
           :default "const uint32_t"
           "The C/C++ data type to use for each temporary variable.  By default
            we use @('\"const uint32_t\"'), which might be appropriate for
            32-bit wide simulations.  For single-bit simulations, you could
            use, e.g., @('\"const bool\"') here, but <b>WARNING</b> if you use
            @('bool') or @('const bool') you need to also change the operators
            from @('&') and @('~') to @('&&') and @('!'), respectively.  See
            @(see aig2c) for more information.")

   (op-and stringp
           :rule-classes :type-prescription
           :default "&"
           "The C/C++ operator to use to AND expressions of this @('type').
            Typically this should be @('&') for integers or @('&&') for
            booleans.")

   (op-not stringp
           :rule-classes :type-prescription
           :default "~"
           "The C/C++ operator used to NOT expressions of this type.  Typically
            this should be @('~') for integers or @('!') for booleans."))

  :require
  ((aig2c-config-sanity-constraint
    (aig2c-boolean-sanity-check-p type op-and op-not)
    :rule-classes nil)))

(defconst *aig2c-default-config*
  (make-aig2c-config))


(define aig2c-maketemps
  :parents (aig2c)
  :short "Create the temporary C code variable names that will be used for each
each AIG node, for a single AIG."

  ((x       "The AIG to process.")
   (config  aig2c-config-p)
   (tempmap "Answer we are accumulating.  Fast alist assigning AIG nodes and
             variables to fresh, \"temporary\" names."
            (string-listp (alist-vals tempmap)))
   (db      "Name database to make sure the names we are generating are
             really unique."
            vl::vl-namedb-p))

  :returns
  (mv (new-map "Fast alist mapping AIG nodes to their newly assigned names.")
      (new-db  "Updated name database."
               vl::vl-namedb-p
               :hyp (and (force (vl::vl-namedb-p db))
                         (force (aig2c-config-p config)))))

  :verify-guards nil
  (b* (((when (hons-get x tempmap))
        ;; Already have a name for this node.
        (mv tempmap db))
       ((mv fresh-name db) (vl::vl-namedb-indexed-name
                            (aig2c-config->prefix config)
                            db))
       (tempmap            (hons-acons x fresh-name tempmap))
       ((when (atom x))
        (mv tempmap db))
       ((when (not (cdr x))) ;; NOT node
        (aig2c-maketemps (car x) config tempmap db))
       ((mv tempmap db) (aig2c-maketemps (car x) config tempmap db))
       ((mv tempmap db) (aig2c-maketemps (cdr x) config tempmap db)))
    (mv tempmap db))
  ///
  (defthm string-listp-of-alist-vals-of-aig2c-maketemps
    (b* (((mv new-map ?new-db)
          (aig2c-maketemps x config tempmap db)))
      (implies (and (force (string-listp (alist-vals tempmap)))
                    (force (vl::vl-namedb-p db))
                    (force (aig2c-config-p config)))
               (string-listp (alist-vals new-map)))))

  (defthm aig2c-maketemps-monotonic
    (b* (((mv new-map ?new-db)
          (aig2c-maketemps x config tempmap db)))
      (implies (subsetp-equal keys (alist-keys tempmap))
               (subsetp-equal keys (alist-keys new-map)))))

  (verify-guards aig2c-maketemps))


(define aig2c-maketemps-list
  :parents (aig2c)
  :short "Create the temporary C code variable names for a whole list of AIGs."
  :long "<p>This just extends @(see aig2c-maketemps) to an AIG list.</p>"

  ((x       "AIG list to process.")
   (config  aig2c-config-p)
   (tempmap (string-listp (alist-vals tempmap)))
   (db      vl::vl-namedb-p))

  :returns
  (mv (new-map)
      (new-db vl::vl-namedb-p :hyp (and (force (vl::vl-namedb-p db))
                                        (force (aig2c-config-p config)))))

  (b* (((when (atom x))
        (mv tempmap db))
       ((mv tempmap db)
        (aig2c-maketemps (car x) config tempmap db)))
    (aig2c-maketemps-list (cdr x) config tempmap db))
  ///
  (defthm string-listp-of-alist-vals-of-aig2c-maketemps-list
    (b* (((mv new-map ?new-db)
          (aig2c-maketemps-list x config tempmap db)))
      (implies (and (force (string-listp (alist-vals tempmap)))
                    (force (vl::vl-namedb-p db))
                    (force (aig2c-config-p config)))
               (string-listp (alist-vals new-map)))))

  (defthm aig2c-maketemps-list-monotonic
    (b* (((mv new-map ?new-db)
          (aig2c-maketemps-list x config tempmap db)))
      (implies (subsetp-equal keys (alist-keys tempmap))
               (subsetp-equal keys (alist-keys new-map)))))

  (verify-guards aig2c-maketemps-list))


(define aig2c-prologue
  :parents (aig2c)
  :short "Create the assignments for AIG constant and variable nodes."

  ((input-init "Mapping from every AIG variable to a C code fragment that
                should be used to initialize it."
               (string-listp (alist-vals input-init)))

   (tempmap    "Fast alist mapping every AIG variable (and other nodes) to
                the temporary variable name to use."
               (string-listp (alist-vals tempmap)))

   (config     aig2c-config-p)

   (code       "The C code fragment we are building, a character list in reverse
                order (e.g., for use with @(see str::revappend-chars))."
               character-listp))

  :returns (new-code character-listp
                     :hyp (force (character-listp code)))

  (b* (((when (atom input-init))
        code)
       ((when (atom (car input-init)))
        ;; Bad alist convention
        (aig2c-prologue (cdr input-init) tempmap config code))
       (var   (caar input-init))            ;; The AIG variable
       (c-rhs (cdar input-init))            ;; C code fragment to initialize this var
       (c-lhs (cdr (hons-get var tempmap))) ;; C variable name for this AIG var
       ((unless c-lhs)
        ;; I originally wanted to cause an error here, and say that the
        ;; variable isn't bound in the tempmap.  But it's not really an error.
        ;; The tempmap is constructed by walking over the AIG and assigning a
        ;; name for every node.  It's perfectly possible that an input variable
        ;; simply isn't used in the AIG.  So there's no reason to cause an
        ;; error: we just need to not try to initialize variables that don't
        ;; exist.
        (aig2c-prologue (cdr input-init) tempmap config code))

       ;; Now print, e.g., "int temp_123 = init;"
       (code (str::revappend-chars "  "  code))
       (code (str::revappend-chars (aig2c-config->type config) code))
       (code (str::revappend-chars " "   code))
       (code (str::revappend-chars c-lhs code))
       (code (str::revappend-chars " = " code))
       (code (str::revappend-chars c-rhs code))
       (code (list* #\Newline #\; code)))
    (aig2c-prologue (cdr input-init) tempmap config code)))

#||
;; Example:
(str::rchars-to-string
 (aig2c-prologue
  '((nil . "0")
    (t   . "~temp_false")
    (a . "inputs.a")
    (b . "inputs.b")
    (c . "inputs.c"))
  (make-fast-alist '((nil . "temp_false")
                     (t . "temp_true")
                     (a . "temp_123")
                     (b . "temp_124")
                     (c . "temp_125")))
  (make-aig2c-config)
  nil))
||#

(define aig2c-main
  :parents (aig2c)
  :short "Create the assignments for a single AIG."

  ((x          "The AIG we are compiling.")

   (seen       "Fast alist mapping AIG nodes we've already compiled to T.")

   (tempmap    "Fast alist mapping every AIG node to its C variable name."
               (string-listp (alist-vals tempmap)))

   (config     aig2c-config-p)

   (code       "The C code fragment we are building, a character list in reverse
                order (e.g., for use with @(see str::revappend-chars))."
               character-listp))

  :verify-guards nil
  :returns (mv (new-code character-listp
                         :hyp (force (character-listp code)))
               seen)

  (b* ((name (cdr (hons-get x tempmap)))

       ((unless name)
        ;; We shouldn't hit this if we've constructed the tempmap correctly.
        (raise "AIG node isn't bound!")
        (mv code seen))

       ((when (atom x))
        ;; We don't need to do anything in this case because we've dealt
        ;; with all the variables and constants in the prologue.
        (mv code seen))

       ((when (hons-get x seen))
        ;; We already initialized this variable so we don't need to process it
        ;; again.
        (mv code seen))

       (seen (hons-acons x t seen))

       ;; Recursively process fanins
       ((mv code seen)
        (aig2c-main (car x) seen tempmap config code))

       ((mv code seen)
        (if (cdr x)
            (aig2c-main (cdr x) seen tempmap config code)
          (mv code seen)))

       (code (list* #\Space #\Space code))
       (code (str::revappend-chars (aig2c-config->type config) code))
       (code (cons #\Space code))
       (code (str::revappend-chars name code))
       (code (list* #\Space #\= #\Space code))

       (car-name (cdr (hons-get (car x) tempmap)))
       ((unless car-name)
        (raise "AIG node for CAR isn't bound!")
        (mv code seen))

       ((unless (cdr x))
        (b* ((code (str::revappend-chars (aig2c-config->op-not config) code))
             (code (str::revappend-chars car-name code))
             (code (list* #\Newline #\; code)))
          (mv code seen)))

       ;; Else, an AND node.
       (cdr-name (cdr (hons-get (cdr x) tempmap)))
       ((unless cdr-name)
        (raise "AIG node for CDR isn't bound!")
        (mv code seen))

       (code (str::revappend-chars car-name code))
       (code (cons #\Space code))
       (code (str::revappend-chars (aig2c-config->op-and config) code))
       (code (cons #\Space code))
       (code (str::revappend-chars cdr-name code))
       (code (list* #\Newline #\; code)))
    (mv code seen))

  ///
  (verify-guards aig2c-main))


#||
;; Example:

(b* ((x0 'a)
     (x1 'b)
     (x2 'c)
     (x3 (aig-not x1))
     (x4 (aig-not x2))
     (x5 (aig-and x1 x4))
     (x6 (aig-and x0 x3))
     (x7 (aig-and x5 x6))
     (x8 (aig-and x7 x4))

     (tempmap `((,x0 . "_var0")
                (,x1 . "_var1")
                (,x2 . "_var2")
                (,x3 . "_foo3")
                (,x4 . "_foo4")
                (,x5 . "_foo5")
                (,x6 . "_foo6")
                (,x7 . "_foo7")
                (,x8 . "_foo8")))
     ((with-fast tempmap))
     ((mv code seen)
      (aig2c-main x8 'seen tempmap
                  (make-aig2c-config)
                  nil))
     ((mv code2 seen2)
      (aig2c-main x8 'seen2 tempmap
                  (make-aig2c-config :type "const bool"
                                     :op-and "&&"
                                     :op-not "!")
                  nil)))
  (fast-alist-free seen)
  (fast-alist-free seen2)
  (list :code (str::rchars-to-string code)
        :code2 (str::rchars-to-string code2)))

||#

(define aig2c-main-list
  :parents (aig2c)
  :short "Create the assignments for a list of AIGs."
  ((x "The AIG list to compile.")
   (seen)
   (tempmap (string-listp (alist-vals tempmap)))
   (config  aig2c-config-p)
   (code    character-listp))
  :returns (mv (new-code character-listp
                         :hyp (force (character-listp code)))
               seen)
  (b* (((when (atom x))
        (mv code seen))
       ((mv code seen)
        (aig2c-main (car x) seen tempmap config code)))
    (aig2c-main-list (cdr x) seen tempmap config code)))




(define aig2c-epilogue
  :parents (aig2c)
  :short "Create the assignments from AIG nodes to outputs."
  ((aig-alist "Alist binding names to AIGs."
              (string-listp (alist-keys aig-alist)))
   (tempmap   "Binds each AIG to its temporary C variable name."
              (string-listp (alist-vals tempmap)))
   (code      character-listp))
  :returns (new-code character-listp
                     :hyp (force (character-listp code)))
  (b* (((when (atom aig-alist))
        code)
       ((when (atom (car aig-alist)))
        ;; Bad alist convention
        (aig2c-epilogue (cdr aig-alist) tempmap code))
       ((cons c-out-name aig1) (car aig-alist))
       (c-temp-name (cdr (hons-get aig1 tempmap)))
       ((unless c-temp-name)
        (raise "AIG not bound in tempmap!")
        code)
       (code (list* #\Space #\Space code))
       (code (str::revappend-chars c-out-name code))
       (code (list* #\Space #\= #\Space code))
       (code (str::revappend-chars c-temp-name code))
       (code (list* #\Newline #\; code)))
    (aig2c-epilogue (cdr aig-alist) tempmap code)))


(define aig2c-compile
  :parents (aig2c)
  :short "Compile an alist of AIGs into a C code fragment."

  ((aig-alist   "Name &rarr; AIG Alist.  The names here must be strings and should
                 refer to proper lvalues in your C code, i.e., they might be
                 variables, or fields in a structure that you want to
                 initialize. For the C code to work, these names must be
                 compatible with the datatype you want to use."
                (string-listp (alist-keys aig-alist)))

   (input-names "AIG Variable &rarr; Name Alist.  This should bind every AIG
                 variable to a string that will be used as its initial value in
                 the C code.  Each name should be a C code fragment that
                 evaluates without side effects."
                (string-listp (alist-vals input-names)))

   &key
   ((config     "Controls names, types, and operators to use in the C code being
                 generated."
                aig2c-config-p)
    '*aig2c-default-config*))

  :returns (mv (err    "NIL on success, or an error @(see msg) on failure,
                        suitable for printing with @('~@').")

               (c-code "C code fragment that implements this AIG, on success,
                        or the empty string on failure."
                       stringp :rule-classes :type-prescription))

  (b* ((output-c-names (alist-keys aig-alist))
       (output-aigs    (alist-vals aig-alist))

       (input-vars     (alist-keys input-names))
       (input-c-names  (alist-vals input-names))

       (all-aig-vars   (aig-vars-1pass output-aigs))

       ((unless (uniquep input-vars))
        (mv (msg "Error: multiple bindings for input variables ~x0"
                 (duplicated-members input-vars))
            ""))

       ((unless (set::subset all-aig-vars (set::mergesort input-vars)))
        (mv (msg "Some AIG variables do not have C input names: ~x0"
                 (set::difference all-aig-vars (set::mergesort input-vars)))
            ""))

       (- (or (set::subset (set::mergesort input-vars) all-aig-vars)
              (cw "Note: Some inputs are never used: ~x0.~%"
                  (set::difference (set::mergesort input-vars) all-aig-vars))))

       ;; I originally thought I might check for unique input-c-names and
       ;; unique output-c-names.  This would be important if we were going to
       ;; avoid prologue and epilogue parts.  But by separating out the
       ;; prologue and epilogue, there's no danger of overwriting an input
       ;; before we use it again.  And, moreover, it might sometimes be useful
       ;; to write the same AIG to multiple places, or to read the same
       ;; location and feed it into several parts of the AIG.  So I no longer
       ;; have these checks.

       (all-c-names     (append input-c-names output-c-names))
       (db              (vl::vl-starting-namedb all-c-names))
       ((mv tempmap db) (aig2c-maketemps-list output-aigs config 'aig2c-tempmap db))
       (-               (vl::vl-free-namedb db))

       ;; Most AIGs, built with things like AIG-AND and AIG-NOT, won't include
       ;; NIL or T because it can get constant-propagated.  But if these do
       ;; occur, they will show up in the tempmap.  We'll hack the
       ;; input-c-names list to handle these in the prologue.
       (input-names
        (if (hons-get nil tempmap)
            (cons (cons nil "0") input-names)
          input-names))

       (input-names
        (if (hons-get t tempmap)
            (cons (cons t (str::cat (aig2c-config->op-not config)
                                    "((" (aig2c-config->type config) ")0)"))
                  input-names)
          input-names))

       ;; Assign C expressions to each input variable
       (code nil)
       (code (aig2c-prologue input-names tempmap config code))
       ((mv code seen)
        (aig2c-main-list output-aigs 'aig2c-seen tempmap config code))
       (- (fast-alist-free seen))
       (code (aig2c-epilogue aig-alist tempmap code))
       (- (fast-alist-free tempmap)))

    (mv nil (str::rchars-to-string code))))


#||

(defconst *bool-config*
  (make-aig2c-config :type "bool" :op-and "&&" :op-not "!"))

(aig2c-compile '(("foo" . nil)) nil)
(aig2c-compile '(("foo" . t)) nil)

(aig2c-compile '(("foo" . nil)) nil :config *bool-config*)
(aig2c-compile '(("foo" . t)) nil :config *bool-config*)

(aig2c-compile '(("foo" . (t . nil))) nil)
(aig2c-compile '(("foo" . (nil . nil))) nil)

(aig2c-compile '(("foo" . (t . nil))) nil :config *bool-config*)
(aig2c-compile '(("foo" . (nil . nil))) nil :config *bool-config*))

(aig2c-compile '(("foo" . t)) nil)
(aig2c-compile '(("foo" . t)) nil
               :config (change-aig2c-config *aig2c-default-config*
                                            :prefix "xyz"
                                            :type "vector"))

(aig2c-compile `(("foo" . ,(aig-and 'a 'b)))
               `((a . "inputs.a")
                 (b . "inputs.b")
                 (c . "inputs.c"))
               :config (make-aig2c-config))


(let* ((line1 'a)
       (line2 'b)
       (line3 'c)
       (line4 (aig-not line3))
       (line5 (aig-and line2 line4))
       (line6 (aig-not line1))
       (line7 (aig-and line3 line6))
       (line8 (aig-and line7 line5)))
  (aig2c-compile `(("out1" . ,line5)
                   ("out2" . ,line8))
                 `((a . "inputs.a")
                   (b . "inputs.b")
                   (c . "inputs.c"))))

||#


