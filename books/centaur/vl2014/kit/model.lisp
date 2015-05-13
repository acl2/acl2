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

; Added by Matt K., May 2015.  Improvement observed when certification used
; the :delay strategy:
; 109.95 sec. vs. 116.03 sec.
(value-triple (set-gc-strategy :delay))

(include-book "centaur/esim/defmodules" :dir :system)
(include-book "centaur/getopt/top" :dir :system)
(include-book "std/io/read-file-characters" :dir :system)
(include-book "progutils")
(include-book "oslib/catpath" :dir :system)
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))


; I don't think we care about emaps anymore.  It looks like they still may be
; supported in the VCD dumping code, but I'm pretty sure we don't actually use
; them.  So, I'm not going to build them in here.

(defoptions vl-model-opts
  :parents (vl-model)
  :short "Options for running @('vl model')."
  :tag :vl-model-opts

  ((help        booleanp
                :alias #\h
                "Show a brief usage message and exit."
                :rule-classes :type-prescription)

   (readme      booleanp
                "Show a more elaborate README and exit."
                :rule-classes :type-prescription)

   (outdir      stringp
                :argname "DIR"
                "Default is \".\".  Controls where the translation files should
                 be written."
                :default "."
                :rule-classes :type-prescription)

   (model-file  stringp
                :argname "NAME"
                :default "model.sao"
                "Default is \"model.sao\".  Contains the main vl-translation-p
                 object with E modules as well as copious other information
                 about from the translation.  See the readme for details.  To
                 avoid writing this file, you can use the empty string, i.e.,
                 --model-file ''."
                :rule-classes :type-prescription)

   (esims-file  stringp
                :argname "NAME"
                :default "esims.sao"
                "Default is \"esims.sao\".  Contains just the E modules, and is
                 typically much smaller than model.sao.  To avoid writing this
                 file, you can use the empty string, i.e., --esims-file ''."
                :rule-classes :type-prescription)

   (verilog-file stringp
                 :argname "NAME"
                 :default "vl_model.v"
                 "Default is \"vl_model.v\".  Contains a \"simplified\" version
                  of some subset of the input Verilog modules.  To avoid writing
                  this file, use the empty string, i.e., --verilog-file ''."
                 :rule-classes :type-prescription)

   (start-files string-listp
                "The list of files to parse. (Not options; this is the rest of
                 the command line, hence :hide t)"
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

   (defines     string-listp
                :longname "define"
                :alias #\D
                :argname "VAR"
                "Set up definitions to use before parsing begins.  Equivalent
                 to putting `define VAR 1 at the top of your Verilog file.
                 You can give this option multiple times."
                :parser getopt::parse-string
                :merge acl2::cons)

   (unroll-limit natp
                 :longname "unroll"
                 :argname "LIMIT"
                 "Set the maximum number of times to unroll loops to LIMIT.
                  Default: 100."
                 :default 100)

   (dropmods   string-listp
               :longname "drop"
               :argname "MOD"
               "Delete MOD from the module hierarchy before doing any simplification.
                This is a gross (but effective) way to work through any bugs in
                VL that cause hard errors and are triggered by certain modules.
                We will fail to model anything that depends on the dropped
                modules."
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

   (mustfail    string-listp
                :argname "MOD"
                "Print a failure message and exit with status 1 if MOD is
                 translated successfully.  This option is mainly meant for
                 running tests to ensure that VL is properly rejecting bad
                 constructs.  You can give this option multiple times."
                :parser getopt::parse-string
                :merge acl2::rcons)

   (mustget     string-listp
                :argname "MOD"
                "Print a failure message and exit with status 1 if MOD is
                 not translated successfully.  You can give this option
                 multiple times."
                :parser getopt::parse-string
                :merge acl2::rcons)
   ))


(defconst *vl-model-help* (str::cat "
vl model:  Make an ACL2 model of a Verilog design.

Example:  vl model engine.v wrapper.v core.v \\
              --search ./simlibs \\
              --search ./baselibs

Usage:    vl model [OPTIONS] file.v [file2.v ...]

Options:" *nls* *nls* *vl-model-opts-usage* *nls*))


(define vl-model-check-must-fail ((mustfail string-listp)
                                  (design   vl-design-p))
  (b* ((okmods (vl-modulelist->names (vl-design->mods design)))
       (oops   (intersect (mergesort mustfail)
                          (mergesort okmods)))
       ((when oops)
        (cw "Oops, modules were translated successfully that are supposed to ~
             have failed: ~x0.~%" oops)
        (exit-fail)))
    nil))

(define vl-model-check-must-get ((mustget string-listp)
                                 (design  vl-design-p))
  (b* ((okmods (vl-modulelist->names (vl-design->mods design)))
       (oops   (difference (mergesort mustget)
                           (mergesort okmods)))
       ((when oops)
        (cw "Oops, required modules were not translated successfully: ~x0.~%"
            oops)
        (exit-fail)))
    nil))

(define vl-model-main ((opts vl-model-opts-p)
                       &key (state 'state))

  (b* (((vl-model-opts opts) opts)

       (want-translation-p (not (equal opts.model-file "")))

       (loadconfig (make-vl-loadconfig
                    :edition       opts.edition
                    :strictp       opts.strict
                    :start-files   opts.start-files
                    :search-path   opts.search-path
                    :search-exts   opts.search-exts
                    :include-dirs  opts.include-dirs
                    :defines       (vl-make-initial-defines opts.defines)
                    :filemapp      want-translation-p))

       (simpconfig (make-vl-simpconfig
                    :problem-mods opts.dropmods
                    :unroll-limit opts.unroll-limit
                    :compress-p   want-translation-p))

       ((mv translation state)
        (cwtime (defmodules-fn loadconfig simpconfig)))

       (good (vl-translation->good translation))
       (- (vl-model-check-must-get opts.mustget good))
       (- (vl-model-check-must-fail opts.mustfail good))

       (state
        (b* (((when (equal opts.model-file ""))
              state)
             (path (oslib::catpath opts.outdir opts.model-file))
             (- (cw "; vl-model: writing ~s0~%" path))
             (state (serialize-write path translation))
             (state (with-ps-file
                      (oslib::catpath opts.outdir (cat opts.model-file ".ver"))
                      (vl-println *vl-current-syntax-version*))))
          state))

       (state
        (b* (((when (equal opts.esims-file ""))
              state)
             (path (oslib::catpath opts.outdir opts.esims-file))
             (- (cw "; vl-model: writing ~s0~%" path)))
          (serialize-write path
                           (vl-modulelist->esims
                            (vl-design->mods
                             (vl-translation->good translation))))))

       (good (vl-translation->good translation))
       (state
        (b* (((when (equal opts.verilog-file ""))
              state)
             (path opts.verilog-file)
             (- (cw "; vl-model: writing ~s0~%" path)))
          (with-ps-file path
                        (vl-ps-update-show-atts nil)
                        (vl-pp-modulelist (vl-design->mods good)
                                          (vl-scopestack-init good))))))
    state))

(defconsts (*vl-model-readme* state)
  (b* (((mv contents state) (acl2::read-file-characters "model.readme" state))
       ((when (stringp contents))
        (raise contents)
        (mv "" state)))
    (mv (implode contents) state)))


(define vl-model ((argv string-listp) &key (state 'state))
  :parents (kit)
  :short "The @('vl model') command."
  (b* (((mv errmsg opts start-files)
        (parse-vl-model-opts argv))
       ((when errmsg)
        (die "~@0~%" errmsg)
        state)
       (opts (change-vl-model-opts opts
                                   :start-files start-files))
       ((vl-model-opts opts) opts)

       ((when opts.help)
        (vl-cw-ps-seq (vl-print *vl-model-help*))
        (exit-ok)
        state)

       ((when opts.readme)
        (vl-cw-ps-seq (vl-print *vl-model-readme*))
        (exit-ok)
        state)

       ((unless (consp opts.start-files))
        (die "No files to process.")
        state)

       (- (cw "Building ACL2 model for:~%"))

       (- (cw " - start files: ~x0~%" opts.start-files))
       (state (must-be-regular-files! opts.start-files))

       (- (cw " - search path: ~x0~%" opts.search-path))
       (state (must-be-directories! opts.search-path))

       (- (cw " - include directories: ~x0~%" opts.include-dirs))
       (state (must-be-directories! opts.include-dirs))

       (- (and opts.defines (cw "; defines: ~x0~%" opts.defines)))

       (- (cw "Writing output to ~x0:~%" opts.outdir))
       (state (must-be-directories! (list opts.outdir)))

       ((when (and (equal opts.model-file "")
                   (equal opts.esims-file "")
                   (equal opts.verilog-file "")
                   ))
        (die "No model file or esims file, so nothing to do?")
        state)

       (- (or (equal opts.model-file "")
              (cw " - model file: ~x0~%" opts.model-file)))

       (- (or (equal opts.esims-file "")
              (cw " - esims file: ~x0~%" opts.esims-file)))

       (- (or (equal opts.verilog-file "")
              (cw " - verilog file: ~x0~%" opts.verilog-file)))

       (- (cw "Soft heap size ceiling: ~x0 GB~%" opts.mem))
       (- (acl2::set-max-mem ;; newline to appease cert.pl's scanner
           (* (expt 2 30) opts.mem)))

       (state (vl-model-main opts)))
    (exit-ok)
    state))
