; VL Verilog Toolkit
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

(in-package "VL")
(include-book "../loader/top")
(include-book "../mlib/hierarchy")
(include-book "centaur/getopt/top" :dir :system)
(include-book "std/io/read-file-characters" :dir :system)
(include-book "progutils")
(include-book "oslib/catpath" :dir :system)
(local (include-book "xdoc/display" :dir :system))
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))

(defxdoc vl-gather
  :parents (kit)
  :short "Collect SystemVerilog files from across your design into a single
file."

  :long "<p>You can use the @('vl gather') command to collect up Verilog
designs, which might be split across several files in many directories, into a
single file that is otherwise unsimplified.</p>

<p>This kind of consolidation may be useful for a number of reasons, e.g., it
may allow you to quickly do things like grepping through the entire design,
grab a snapshot of the entire design, etc.</p>

<p>Note that if you just want to process designs with VL, there's normally no
reason that you need to use this command.  VL's @(see loader) can be given
@(see vl-loadconfig) options like @('search-path') and @('include-dirs') to
allow it to find modules from many directories.</p>

<p>For usage information, run @('vl gather --help') or see @(see
*vl-gather-help*).</p>")

(local (xdoc::set-default-parents vl-gather))

(defoptions vl-gather-opts
  :parents (vl-gather)
  :short "Options for running @('vl gather')."
  :tag :vl-model-opts

  ((help        booleanp
                :alias #\h
                "Show a brief usage message and exit."
                :rule-classes :type-prescription)

   (readme      booleanp
                "Show a more elaborate README and exit."
                :rule-classes :type-prescription)

   (output      stringp
                :alias #\o
                :argname "FILE"
                "Default is \"vl_gather.v\".  Where to write the collected up
                 modules."
                :default "vl_gather.v"
                :rule-classes :type-prescription)

   (start-files string-listp
                "The list of files to parse. (Not options; this is the rest of
                 the command line, hence :hide t)"
                :hide t)

   (plusargs    string-listp
                "Plusargs with plusses removed."
                :hide t)

   (search-path string-listp
                :longname "search"
                :alias #\s
                :argname "DIR"
                "Control the search path for finding modules.  You can give
                 this switch multiple times, to set up multiple search paths in
                 priority order."
                :parser getopt::parse-string
                :merge acl2::rcons)

   (include-dirs string-listp
                 :longname "incdir"
                 :alias #\I
                 :argname "DIR"
                 "Control the list of directories for `include files.  You can
                  give this switch multiple times.  By default, we look only in
                  the current directory."
                 :parser getopt::parse-string
                 :merge acl2::rcons
                 :default '("."))

   (search-exts string-listp
                :longname "searchext"
                :argname "EXT"
                "Control the search extensions for finding modules.  You can
                 give this switch multiple times.  By default we just look for
                 files named \"foo.v\" in the --search directories.  But if you
                 have Verilog files with different extensions, this won't work,
                 so you can add these extensions here.  EXT should not include
                 the period, e.g., use \"--searchext vv\" to consider files
                 like \"foo.vv\", etc."
                :parser getopt::parse-string
                :merge acl2::rcons
                :default '("v"))

   (defines    string-listp
               :longname "define"
               :alias #\D
               :argname "VAR"
               "Set up definitions to use before parsing begins.  For instance,
                \"--define foo\" is similar to \"`define foo\" and \"--define
                foo=3\" is similar to \"`define foo 3\".  Note: these defines
                are \"sticky\" and will override subsequent `defines in your
                Verilog files unless your Verilog explicitly uses `undef.  You
                can give this option multiple times."
               :parser getopt::parse-string
               :merge cons)

   (edition     vl-edition-p
                :argname "EDITION"
                "Which edition of the Verilog standard to implement?
                 Default: \"SystemVerilog\" (IEEE 1800-2012).  You can
                 alternately use \"Verilog\" for IEEE 1364-2005, i.e.,
                 Verilog-2005."
                :default :system-verilog-2012)

   (strict      booleanp
                :rule-classes :type-prescription
                "Disable VL extensions to Verilog.")

   (mem         posp
                :alias #\m
                :argname "GB"
                "How much memory to try to use.  Default: 4 GB.  Raising this
                 may improve performance by avoiding garbage collection.  To
                 avoid swapping, keep this below (physical_memory - 2 GB)."
                :default 4
                :rule-classes :type-prescription)
   ))

(defval *vl-gather-help*
  :showdef nil
  :showval t
  (str::cat "
vl gather:  Collect Verilog files into a single file.

Example:  vl gather engine.v wrapper.v core.v \\
              --search ./simlibs \\
              --search ./baselibs \\
              --output all-modules.v

Usage:    vl gather [OPTIONS] file.v [file2.v ...]

Options:" *nls* *nls* *vl-gather-opts-usage* *nls*))


(define vl-module-original-source ((mod     vl-module-p)
                                   (filemap vl-filemap-p))
  :returns (original-source stringp :rule-classes :type-prescription)
  (b* (((vl-module mod) mod)
       (minloc mod.minloc)
       (maxloc mod.maxloc)
       ((vl-location minloc) minloc)
       ((vl-location maxloc) maxloc)
       ((unless (equal minloc.filename maxloc.filename))
        (raise "Expected modules to begin/end in the same file, but ~s0 ~
                starts at ~s1 and ends at ~s2."
               mod.name
               (vl-location-string minloc)
               (vl-location-string maxloc))
        "")
       (file (cdr (hons-assoc-equal minloc.filename filemap)))
       ((unless file)
        (raise "File not found in the file map: ~s0" minloc.filename)
        "")
       (maxloc
        ;; awful hack to get all of "endmodule"
        (change-vl-location maxloc
                            :col (+ maxloc.col (length "endmodule"))))
       (lines (vl-string-between-locs file minloc maxloc))
       ((unless lines)
        (raise "Error extracting module contents for ~s0" mod.name)
        ""))
    (str::cat "// " mod.name " from " minloc.filename ":" (natstr minloc.line)
              *nls* lines)))

(defprojection vl-modulelist-original-sources (x filemap)
  (vl-module-original-source x filemap)
  :guard (and (vl-modulelist-p x)
              (vl-filemap-p filemap))
  ///
  (defthm string-listp-of-vl-modulelist-original-sources
    (string-listp (vl-modulelist-original-sources x filemap))))


(define vl-design-original-source ((x       vl-design-p)
                                   (filemap vl-filemap-p))
  :returns (original-source stringp :rule-classes :type-prescription)
  (b* ((x    (vl-design-fix x))
       (mods (vl-design->mods x)))
    ;; BOZO this probably needs to get updated for SystemVerilog-2012.  We'll want
    ;; to go get other things from the design, like the interfaces, programs, and
    ;; also top-level parameters, etc.
    (str::join (vl-modulelist-original-sources mods filemap)
               (implode '(#\Newline #\Newline)))))

;; (define vl-gather-reorder ((x vl-design-p))
;;   :returns (new-x vl-design-p)
;;   (b* ((x    (vl-design-fix x))
;;        (mods (vl-design->mods x))
;;        (missing (vl-modulelist-missing mods))
;;        ((when missing)
;;         (raise "Error: did not find definitions for ~&0." missing)
;;         x)
;;        (mods (cwtime (vl-deporder-sort mods))))
;;     (change-vl-design x :mods mods)))

(define vl-gather-main ((opts vl-gather-opts-p)
                        &key (state 'state))

  (b* (((vl-gather-opts opts) opts)


       ((mv ?cmdline-warnings defines)
        (vl-parse-cmdline-defines opts.defines
                                  (make-vl-location :filename "vl cmdline"
                                                    :line 1
                                                    :col 0)
                                  ;; Command line defines are sticky
                                  t))

       (- (or (not cmdline-warnings)
              (vl-cw-ps-seq (vl-print-warnings cmdline-warnings))))

       (loadconfig (make-vl-loadconfig
                    :edition       opts.edition
                    :strictp       opts.strict
                    :start-files   opts.start-files
                    :plusargs      opts.plusargs
                    :search-path   opts.search-path
                    :search-exts   opts.search-exts
                    :include-dirs  opts.include-dirs
                    :defines       defines
                    :filemapp      t))

       ((mv result state) (vl-load loadconfig))
       ((vl-loadresult result) result)
       ((mv ?okp design) (vl-design-deporder-modules result.design))
       (orig    (vl-design-original-source design result.filemap))
       (- (cw "Writing output file ~x0~%" opts.output))
       (state   (with-ps-file opts.output (vl-print orig)))
       (- (cw "All done gathering files.~%")))
    state))

(defconsts (*vl-gather-readme* state)
  (b* ((topic (xdoc::find-topic 'vl::vl-gather (xdoc::get-xdoc-table (w state))))
       ((mv text state) (xdoc::topic-to-text topic nil state)))
    (mv text state)))

(define vl-gather-top ((argv string-listp) &key (state 'state))
  :short "Top-level @('vl gather') command."
  (b* (((mv errmsg opts start-files-and-plusargs)
        (parse-vl-gather-opts argv))
       ((when errmsg)
        (die "~@0~%" errmsg)
        state)
       ((mv start-files plusargs) (split-plusargs start-files-and-plusargs))
       (opts (change-vl-gather-opts opts
                                    :plusargs plusargs
                                    :start-files start-files))
       ((vl-gather-opts opts) opts)

       ((when opts.help)
        (vl-cw-ps-seq (vl-print *vl-gather-help*))
        (exit-ok)
        state)

       ((when opts.readme)
        (vl-cw-ps-seq (vl-print *vl-gather-readme*))
        (exit-ok)
        state)

       ((unless (consp opts.start-files))
        (die "No files to process.")
        state)

       (- (cw "VL Gather Configuration:~%"))

       (- (cw " - start files: ~x0~%" opts.start-files))
       (state (must-be-regular-files! opts.start-files))

       (- (cw " - search path: ~x0~%" opts.search-path))
       (state (must-be-directories! opts.search-path))

       (- (cw " - include directories: ~x0~%" opts.include-dirs))
       (state (must-be-directories! opts.include-dirs))

       (- (and opts.defines (cw "; defines: ~x0~%" opts.defines)))

       (- (cw " - output file: ~x0~%" opts.output))

       (- (cw "; Soft heap size ceiling: ~x0 GB~%" opts.mem))
       (- (acl2::set-max-mem ;; newline to appease cert.pl's scanner
           (* (expt 2 30) opts.mem)))

       (state (vl-gather-main opts)))
    (exit-ok)
    state))


