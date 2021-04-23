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
(include-book "../mlib/json")
(include-book "../loader/top")
(include-book "centaur/getopt/top" :dir :system)
(include-book "std/io/read-file-characters" :dir :system)
(include-book "progutils")
(include-book "oslib/catpath" :dir :system)
(include-book "oslib/dirname" :dir :system)
(include-book "oslib/date" :dir :system)
(local (include-book "xdoc/display" :dir :system))
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))

(defxdoc vl-json
  :parents (kit)
  :short "Parse a SystemVerilog design and save it as a @('.json') file."

  :long "<p>The VL @(see kit) provides a @('json') command that you can use to
parse a Verilog/SystemVerilog design and then write it out into a @('.json')
file.  These files are complete(?) snapshots of what VL has parsed.</p>

<p>For detailed usage information, run @('vl json --readme') or see @(see
*vl-json-readme*).</p>")

(local (xdoc::set-default-parents vl-json))




(defoptions vl-json-opts
  :short "Options for running @('vl json')."
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
                "Write output to FILE.  Default: \"foo.v.json\", where
                 \"foo.v\" is the basename of the first Verilog file provided."
                :rule-classes :type-prescription
                :default "")

   (start-files string-listp
                "The list of files to parse. (Not options; this is the rest of
                 the command line, hence :hide t)"
                :hide t)

   (plusargs    string-listp
                "The list of plusargs without plusses."
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
                 files named \"foo.sv\" and \"foo.v\" in the --search
                 directories.  If you have Verilog files with different
                 extensions, this won't work, so you can add these extensions
                 here."
                :parser getopt::parse-string
                :merge acl2::rcons
                :default '("sv" "v"))

   (defines     string-listp
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
                :merge acl2::cons)

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

(defval *vl-json-readme*
  :short "Detailed usage information for the @('vl json') command."
  :showval t
  :showdef nil
  (str::cat "
vl json:  Parse Verilog files and write it out as a .json file.

Example:  vl json engine.v wrapper.v core.v \\
              --search ./simlibs \\
              --search ./baselibs \\
              --output my-design.json

Usage:    vl json [OPTIONS] file.v [file2.v ...]

Options:" *nls* *nls* *vl-json-opts-usage* *nls*))



(define vl-json-main ((opts vl-json-opts-p)
                     &key (state 'state))
  :guard (consp (vl-json-opts->start-files opts))
  (b* (((vl-json-opts opts) opts)

       ((mv cmdline-warnings defines)
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
       ; ((mv date state) (oslib::date))
       ; ((mv ltime state) (oslib::universal-time))

       (design (change-vl-design result.design
                :warnings
                (append-without-guard cmdline-warnings
                                      (vl-design->warnings result.design))))

       ((mv outfile state)
        (if (equal opts.output "")
            (oslib::basename! (cat (car opts.start-files) ".json"))
          (mv opts.output state)))

       (- (cw "Writing output to file ~x0~%" outfile))
       (state
        (cwtime
         (with-ps-file outfile
           (vl-ps-seq
            (vl-ps-update-autowrap-col 120)
            (vl-ps-update-autowrap-ind 10)
            (cwtime (vl-jp-design design))))))
       (- (cw "Done~%")))
    state))


(defconsts (*vl-json-help* state)
  (b* ((topic (xdoc::find-topic 'vl::vl-json (xdoc::get-xdoc-table (w state))))
       ((mv text state) (xdoc::topic-to-text topic nil state)))
    (mv text state)))



(define vl-json-top ((argv string-listp) &key (state 'state))
  :short "Top-level @('vl json') command."

  (b* (((mv errmsg opts start-files-and-plusargs)
        (parse-vl-json-opts argv))
       ((when errmsg)
        (die "~@0~%" errmsg)
        state)
       ((mv start-files plusargs) (split-plusargs start-files-and-plusargs))
       (opts (change-vl-json-opts opts
                                 :plusargs plusargs
                                 :start-files start-files))
       ((vl-json-opts opts) opts)

       ((when opts.help)
        (vl-cw-ps-seq (vl-print *vl-json-help*))
        (exit-ok)
        state)

       ((when opts.readme)
        (vl-cw-ps-seq (vl-print *vl-json-readme*))
        (exit-ok)
        state)

       ((unless (consp opts.start-files))
        (die "No files to process.")
        state)

       (- (cw "VL Json Configuration:~%"))

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

       (state (vl-json-main opts)))
    (exit-ok)
    state))
