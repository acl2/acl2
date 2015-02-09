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
(include-book "../loader/top")
(include-book "../mlib/json")
(include-book "centaur/getopt/top" :dir :system)
(include-book "std/io/read-file-characters" :dir :system)
(include-book "progutils")
(local (include-book "../util/arithmetic"))

(defoptions vl-json-opts
  :parents (vl-json)
  :short "Options for running @('vl json')."
  :tag :vl-json-opts

  ((help        booleanp
                "Show a brief usage message and exit."
                :rule-classes :type-prescription
                :alias #\h)

   (readme      booleanp
                "Show a more elaborate README and exit."
                :rule-classes :type-prescription)

   (outfile     (stringp outfile)
                :argname "FILE"
                :alias #\o
                "Write output to FILE.  Default: \"foo.v.json\", where
                 \"foo.v\" is the first Verilog file provided."
                :rule-classes :type-prescription
                :default "")

   (search-path string-listp
                :longname "search"
                :alias #\s
                :argname "DIR"
                "Search path for finding modules.  You can give this switch
                 multiple times, to set up multiple search paths in priority
                 order."
                :parser getopt::parse-string
                :merge acl2::rcons)

   (separate    booleanp
                "Write modules as separate, independent JSON objects instead of
                 as a single, monolithic object."
                :rule-classes :type-prescription)

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

   (debug       booleanp
                "Print extra information for debugging."
                :rule-classes :type-prescription)))

(defconst *vl-json-help* (str::cat "
vl json:  Converts Verilog into JSON, a format that can be easily loaded into
          scripting languages like Ruby, Perl, etc.

Example:  vl json engine.v wrapper.v core.v \\
              --search ./simlibs \\
              --search ./baselibs

Usage:    vl json [OPTIONS] file.v [file2.v ...]

Options:" *nls* *nls* *vl-json-opts-usage* *nls*))

(defconsts (*vl-json-readme* state)
  (b* (((mv contents state) (acl2::read-file-characters "json.readme" state))
       ((when (stringp contents))
        (raise contents)
        (mv "" state)))
    (mv (implode contents) state)))

(define vl-json ((cmdargs string-listp) &optional (state 'state))
  :parents (kit)
  :short "The @('vl json') command."

  (b* (((mv errmsg opts start-files)
        (parse-vl-json-opts cmdargs))
       ((when errmsg)
        (die "~@0~%" errmsg)
        state)

       ((vl-json-opts opts) opts)
       (- (acl2::set-max-mem ;; newline to appease cert.pl's scanner
           (* (expt 2 30) opts.mem)))

       ((when opts.help)
        (vl-cw-ps-seq (vl-print *vl-json-help*))
        (exit-ok)
        state)

       ((when opts.readme)
        (vl-cw-ps-seq (vl-print *vl-json-readme*))
        (exit-ok)
        state)

       ((unless (consp start-files))
        (die "No files to process.")
        state)
       (outfile (if (equal opts.outfile "")
                    (cat (car start-files) ".json")
                  opts.outfile))

       (- (or (not opts.debug)
              (cw "vl json options: ~x0~%" opts)))

       (state (must-be-regular-files! start-files))
       (state (must-be-directories! opts.search-path))

       (- (cw "Parsing Verilog sources...~%"))
       (loadconfig (make-vl-loadconfig
                          :edition opts.edition
                          :strictp opts.strict
                          :start-files start-files
                          :search-path opts.search-path
                          :filemapp nil))
       (- (or (not opts.debug)
              (cw "vl load configuration: ~x0~%" loadconfig)))
       ((mv (vl-loadresult res) state)
        (cwtime (vl-load loadconfig)))

       (- (cw "JSON-Encoding Modules...~%"))

       ;; BOZO, Eventually we can change this to output the whole design, but
       ;; for now continue to just print only the modules.

       (mods (vl-design->mods res.design))
       (state
        (cwtime
         (with-ps-file outfile
                       (vl-ps-update-autowrap-col 120)
                       (vl-ps-update-autowrap-ind 10)
                       (cwtime (if opts.separate
                                   (vl-jp-individual-modules mods)
                                 (vl-jp-modalist (vl-modalist mods)))
                               :name vl-json-encode))
         :name vl-json-export)))
    (exit-ok)
    state))
