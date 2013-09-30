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
(include-book "../loader/loader")
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
       ((mv (vl-loadresult res) state)
        (cwtime (vl-load (make-vl-loadconfig :start-files start-files
                                             :search-path opts.search-path
                                             :filemapp nil))))

       (- (cw "JSON-Encoding Modules...~%"))
       (state
        (cwtime
         (with-ps-file outfile
                       (vl-ps-update-autowrap-col 120)
                       (vl-ps-update-autowrap-ind 10)
                       (cwtime (if opts.separate
                                   (vl-jp-individual-modules res.mods)
                                 (vl-jp-modalist (vl-modalist res.mods)))
                               :name vl-json-encode))
         :name vl-json-export)))
    (exit-ok)
    state))
