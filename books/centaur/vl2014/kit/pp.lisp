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
(include-book "progutils")
(include-book "../util/print")
(include-book "../loader/preprocessor/preprocessor")
(include-book "centaur/getopt/top" :dir :system)
(include-book "centaur/misc/memory-mgmt" :dir :system)
(include-book "std/io/read-file-characters" :dir :system)
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))

(defoptions vl-pp-opts
  :parents (vl-pp)
  :short "Options for running @('vl pp')."
  :tag :vl-pp-opts

  ((help        booleanp
                :alias #\h
                "Show a brief usage message and exit."
                :rule-classes :type-prescription)

   (readme      booleanp
                "Show a more elaborate README and exit."
                :rule-classes :type-prescription)

   (output      stringp
                :argname "FILE"
                :alias #\o
                "Controls where the output of preprocessing (i.e., post-
                 preprocessing Verilog or SystemVerilog code) should be
                 written.  Default: vl-pp.out."
                :default "vl-pp.out"
                :rule-classes :type-prescription)

   (outdefs     stringp
                :argname "FILE"
                "Controls where the collected `defines should be written.
                 Default: vl-pp.defs."
                :default "vl-pp.defs"
                :rule-classes :type-prescription)

   (start-files string-listp
                "The list of files to parse. (Not options; this is the rest of
                 the command line, hence :hide t)"
                :hide t)

   (include-dirs string-listp
                 :longname "include"
                 :alias #\I
                 :argname "DIR"
                 "Control the include directories for `include directives.  You
                  can give this switch multiple times, to set up multiple
                  include directories in priority order."
                :parser getopt::parse-string
                :merge acl2::rcons)

   (defines     string-listp
                :longname "define"
                :alias #\D
                :argname "VAR"
                "Set up definitions to use before parsing begins.  Equivalent
                 to putting `define VAR 1 at the top of your Verilog file.
                 You can give this option multiple times."
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
                :rule-classes :type-prescription)))

(defconst *vl-pp-help* (str::cat "
vl pp:  Preprocess a Verilog design

Example:  vl pp engine.v wrapper.v core.v \\
              --include ./simlibs \\
              --include ./baselibs

Usage:    vl pp [OPTIONS] file.v [file2.v ...]

Options:" *nls* *nls* *vl-pp-opts-usage* *nls*))

(defconsts (*vl-pp-readme* state)
  (b* (((mv contents state) (acl2::read-file-characters "pp.readme" state))
       ((when (stringp contents))
        (raise contents)
        (mv "" state)))
    (mv (implode contents) state)))

(define vl-pp-main ((opts vl-pp-opts-p) &key (state 'state))

  (b* (((vl-pp-opts opts) opts)

       (loadconfig (make-vl-loadconfig
                    :edition      opts.edition
                    :strictp      opts.strict
                    :include-dirs opts.include-dirs
                    :defines      (vl-make-initial-defines opts.defines)
                    :filemapp     nil))
       ((mv errmsg echars state)
        (cwtime (vl-read-files opts.start-files)))
       ((when errmsg)
        (die "~@0~%" errmsg)
        state)

       ((mv okp defines ?filemap echars state)
        (cwtime (vl-preprocess echars
                               :defines (vl-loadconfig->defines loadconfig)
                               :config loadconfig)))
       ((unless okp)
        (die "Preprocessing failed")
        state)

       (state
        (if (equal opts.output "")
            state
          (cwtime
           (with-ps-file opts.output
                         (vl-print-str (vl-echarlist->string echars)))
           :name write-output)))

       (state
        (if (equal opts.outdefs "")
            state
          (cwtime
           (with-ps-file opts.outdefs (vl-pp-defines defines))
           :name write-defines))))
    state))


(define vl-pp ((argv string-listp) &key (state 'state))
  :parents (kit)
  :short "The @('vl pp') command."
  (b* (((mv errmsg opts start-files)
        (parse-vl-pp-opts argv))
       ((when errmsg)
        (die "~@0~%" errmsg)
        state)
       (opts (change-vl-pp-opts opts
                                :start-files start-files))
       ((vl-pp-opts opts) opts)
       ((when opts.help)
        (vl-cw-ps-seq (vl-print *vl-pp-help*))
        (exit-ok)
        state)
       ((when opts.readme)
        (vl-cw-ps-seq (vl-print *vl-pp-readme*))
        (exit-ok)
        state)
       ((unless (consp opts.start-files))
        (die "No files to process.")
        state)

       (- (cw "Starting VL Preprocessor:~%"))

       (- (cw " - start files: ~x0~%" opts.start-files))
       (state (must-be-regular-files! opts.start-files))

       (- (cw " - include dirs: ~x0~%" opts.include-dirs))
       (state (must-be-directories! opts.include-dirs))

       (- (cw " - writing output to ~x0:~%" opts.output))

       (- (cw " - soft heap size ceiling: ~x0 GB~%" opts.mem))
       (- (acl2::set-max-mem ;; newline to appease cert.pl's scanner
           (* (expt 2 30) opts.mem)))

       (state (vl-pp-main opts)))
    (exit-ok)
    state))
