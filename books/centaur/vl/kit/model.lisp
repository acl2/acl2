; VL Verilog Toolkit
; Copyright (C) 2008-2013 Centaur Technology
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
(include-book "../top")
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

   (overrides   string-listp
                :longname "override"
                :argname "DIR"
                "(Advanced) Set up VL override directories.  You can give this
                 switch multiple times.  By default there are no override
                 directories.  See the VL documentation on overrides (under
                 loader) for more information."
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
   ))


(defconst *vl-model-help* (str::cat "
vl model:  Make an ACL2 model of a Verilog design.

Example:  vl model engine.v wrapper.v core.v \\
              --search ./simlibs \\
              --search ./baselibs

Usage:    vl model [OPTIONS] file.v [file2.v ...]

Options:" *nls* *nls* *vl-model-opts-usage* *nls*))


(define vl-model-main ((opts vl-model-opts-p)
                       &key (state 'state))

  (b* (((vl-model-opts opts) opts)

       (want-translation-p (not (equal opts.model-file "")))

       (loadconfig (make-vl-loadconfig
                    :edition       opts.edition
                    :strictp       opts.strict
                    :override-dirs opts.overrides
                    :start-files   opts.start-files
                    :search-path   opts.search-path
                    :search-exts   opts.search-exts
                    :defines       (vl-make-initial-defines opts.defines)
                    :filemapp      want-translation-p))

       (simpconfig (make-vl-simpconfig
                    :problem-mods opts.dropmods
                    :unroll-limit opts.unroll-limit
                    :compress-p   want-translation-p))

       ((mv translation state)
        (defmodules-fn loadconfig simpconfig))

       (state
        (if (equal opts.model-file "")
            state
          (serialize-write (oslib::catpath opts.outdir opts.model-file)
                           translation
                           :verbosep t)))

       (state
        (if (equal opts.esims-file "")
            state
          (serialize-write (oslib::catpath opts.outdir opts.esims-file)
                           (vl-modulelist->esims
                            (vl-design->mods
                             (vl-translation->good translation)))
                           :verbosep t))))
    state))

(defconsts (*vl-model-readme* state)
  (b* (((mv contents state) (acl2::read-file-characters "model.readme" state))
       ((when (stringp contents))
        (raise contents)
        (mv "" state)))
    (mv (implode contents) state)))


(define vl-model ((argv string-listp) &key (state 'state))
  :parents (kit lint)
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

       (- (and opts.overrides
               (cw " - overrides: ~x0~%" opts.overrides)))
       (state (must-be-directories! opts.overrides))

       (- (and opts.defines (cw "; defines: ~x0~%" opts.defines)))

       (- (cw "Writing output to ~x0:~%" opts.outdir))
       (state (must-be-directories! (list opts.outdir)))

       ((when (and (equal opts.model-file "")
                   (equal opts.esims-file "")))
        (die "No model file or esims file, so nothing to do?")
        state)

       (- (or (equal opts.model-file "")
              (cw " - model file: ~x0" opts.model-file)))

       (- (or (equal opts.esims-file "")
              (cw " - esims file: ~x0" opts.esims-file)))

       (- (cw "Soft heap size ceiling: ~x0 GB~%" opts.mem))
       (- (acl2::set-max-mem ;; newline to appease cert.pl's scanner
           (* (expt 2 30) opts.mem)))

       (state (vl-model-main opts)))
    (exit-ok)
    state))
