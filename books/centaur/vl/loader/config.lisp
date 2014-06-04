; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
(include-book "preprocessor/defines")

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
                    and for <see topic=\"@(url vl-modulelist-missing)\">missing
                    modules</see>.  This is similar to \"library directories\"
                    in tools like Verilog-XL and NCVerilog.")

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

   (filemapp       booleanp
                   :rule-classes :type-prescription
                   :default t
                   "This flag controls whether a @(see vl-filemap-p) will be
                    constructed for the files we have loaded.  You may wish to
                    turn this off to save some memory.")

   (override-dirs  string-listp
                   "Directories to scan for any @(see overrides).")

   (flush-tries    posp
                   :rule-classes :type-prescription
                   :default 10000
                   "How many rounds of @(see vl-flush-out-modules) are
                    allowed.")

   (mintime        mintime-p
                   :rule-classes :type-prescription
                   :default 1
                   "Minimum time threshold for performance messages.")))

(defconst *vl-default-loadconfig*
  (make-vl-loadconfig))

