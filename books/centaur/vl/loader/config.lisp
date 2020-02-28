; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "VL")
(include-book "preprocessor/defines")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(include-book "std/testing/assert" :dir :system)

(local (defthm string-listp-of-remove-equal
         (implies (force (string-listp x))
                  (string-listp (remove-equal a x)))))

(local (defthm string-listp-of-remove-duplicates-equal
         (implies (force (string-listp x))
                  (string-listp (remove-duplicates-equal x)))))

(define mintime-p (x)
  (or (not x)
      (rationalp x))
  ///
  (defthm mintime-p-compound-recognizer
    (equal (mintime-p x)
           (or (rationalp x)
               (not x)))
    :rule-classes :compound-recognizer))

(define mintime-fix ((x mintime-p))
  :inline t
  :returns (x-fix mintime-p)
  :prepwork ((local (in-theory (enable mintime-p))))
  (and x
       (rfix x))
  ///
  (defthm mintime-fix-when-mintime-p
    (implies (mintime-p x)
             (equal (mintime-fix x)
                    x))))

(deffixtype mintime
  :pred mintime-p
  :fix mintime-fix
  :equiv mintime-equiv
  :define t
  :forward t)


(defprod vl-loadconfig
  :parents (loader)
  :short "Options for how to load Verilog modules."
  :tag :vl-loadconfig
  ((edition        vl-edition-p
                   :default :system-verilog-2012
                   "Which standard are we implementing, e.g., IEEE Std
                    1364-2005 (Verilog) or IEEE Std
                    1800-2012 (SystemVerilog).")

   (strictp        booleanp
                   :rule-classes :type-prescription
                   :default nil
                   "VL normally implements certain extensions of the Verilog
                    standard like @('//+VL') comments.  Turning on strict mode
                    will disable these extensions and instruct VL to implement
                    the standard more strictly.")

   (start-files    string-listp
                   "A list of file names (not module names) that you want to
                    load; @(see vl-load) begins by trying to read, preprocess,
                    lex, and parse the contents of these files.")

   (start-names    string-listp
                   "Instead of (or in addition to) explicitly providing the
                    @('start-files'), you can also provide a list of
                    description names that you want to load (e.g., names of
                    modules, packages, interfaces, programs, etc.).  @(see
                    vl-load) will look for these descriptions in the search
                    path, unless they happen to get loaded while processing the
                    @('start-files').")

   (search-path    string-listp
                   "A list of directories to search (in order) for descriptions
                    in @('start-modnames') that were in the @('start-files'),
                    and for missing modules.  This is similar to \"library
                    directories\" in tools like Verilog-XL and NCVerilog.")

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

   (plusargs       string-listp
                   "List of plusargs for functions like @('$test$plusargs').
                    These should have no leading @('+') characters.  For
                    instance, using @(':plusargs (list \"foo\" \"bar\")') is
                    intended to be equivalent to passing @('+foo +bar') to a
                    Verilog simulator as command-line options.")

   (filemapp       booleanp
                   :rule-classes :type-prescription
                   :default t
                   "This flag controls whether a @(see vl-filemap-p) will be
                    constructed for the files we have loaded.  You may wish to
                    turn this off to save some memory.")

   (debugp         booleanp
                   :rule-classes :type-prescription
                   "Enable high-level loader debugging features that may be
                    expensive.")

   (flush-tries    posp
                   :rule-classes :type-prescription
                   :default 10000
                   "How many rounds of @(see vl-flush-out-descriptions) are
                    allowed.")

   (mintime        mintime-p
                   :rule-classes :type-prescription
                   :default 1
                   "Minimum time threshold for performance messages.")))

(defconst *vl-default-loadconfig*
  (make-vl-loadconfig))

(local (xdoc::set-default-parents vl-loadconfig-clean))


(define vl-clean-search-extension ((searchext stringp))
  :short "Normalize search extensions so that they don't have leading dots."
  :long "<p>This is a DWIM feature so that we can just do the right thing
regardless of whether you say the search extensions are, e.g., @('\".sv\"') or
just @('\"sv\"').</p>"
  :returns (new-searchext stringp :rule-classes :type-prescription)
  (b* ((searchext (string-fix searchext))
       (len (length searchext))
       ((when (and (< 0 len)
                   (eql (char searchext 0) #\.)))
        (subseq searchext 1 nil)))
    searchext)
  ///
  (assert! (equal (vl-clean-search-extension "sv") "sv"))
  (assert! (equal (vl-clean-search-extension ".sv") "sv")))

(defprojection vl-clean-search-extensions-aux ((x string-listp))
  :returns (new-x string-listp)
  (vl-clean-search-extension x))

(define vl-clean-search-extensions ((search-exts string-listp))
  :returns (search-exts string-listp)
  (remove-duplicates-equal (remove-equal "" (vl-clean-search-extensions-aux search-exts)))
  ///
  (assert! (equal (vl-clean-search-extensions '("v" "v" ".v" "sv")) '("v" "sv")))
  (assert! (equal (vl-clean-search-extensions '(".v" "v")) '("v")))
  (assert! (equal (vl-clean-search-extensions '(".sv" "v" "sv" "v")) '("sv" "v"))))

(define vl-loadconfig-clean
  :parents (vl-loadconfig)
  :short "Normalize a load configuration to avoid, e.g., redundant search paths
  and extensions."
  ((config vl-loadconfig-p))
  :returns (new-config vl-loadconfig-p)
  :long "<p>We clean up the load configuration in a couple of ways.  This is
partially an optimization that will help us to avoid looking in the same
directories multiple times.  It also helps to prevent spurious \"ambiguous
load\" warnings that could arise if someone gives the same search extensions
multiple times.</p>"
  (b* (((vl-loadconfig config)))
    (change-vl-loadconfig config
                          ;; Don't sort start-files in case the user wants to process
                          ;; them multiple times.
                          :start-names (mergesort config.start-names)
                          ;; We use remove-duplicates-equal instead of
                          ;; mergesort, even though it is generally slow,
                          ;; because it preserves the original order, which
                          ;; matters for priority-ordered search paths/exts.
                          :search-path (remove-duplicates-equal config.search-path)
                          :search-exts (vl-clean-search-extensions config.search-exts)
                          :include-dirs (remove-duplicates-equal config.include-dirs))))
