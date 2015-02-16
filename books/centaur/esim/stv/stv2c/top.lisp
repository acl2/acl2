; ESIM Symbolic Hardware Simulator
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


; stv2c/top.lisp -- command line tool for STV => C++ conversion
;
; Original author: Jared Davis

(in-package "ACL2")
(include-book "../stv-top")
(include-book "centaur/esim/defmodules" :dir :system)
(include-book "stv2c")
(include-book "centaur/getopt/top" :dir :system)
(include-book "centaur/vl2014/kit/progutils" :dir :system)
(include-book "oslib/argv" :dir :system)
(include-book "std/io/read-file-objects" :dir :system)
(local (include-book "std/typed-lists/string-listp" :dir :system))
(local (in-theory (disable state-p1-forward)))

#||
For debugging, so the program doesn't quit on you at random.

#!VL2014
(with-redef
 (progn
   (define exit-ok ()
     (raise "~%~%*** EXIT OK***~%~%"))
   (define exit-fail ()
     (raise "~%~%*** EXIT FAIL***~%~%"))))

||#

(defmacro die (&rest args)
  `(vl2014::die . ,args))

(defmacro exit-ok (&rest args)
  `(vl2014::exit-ok . ,args))


(defoptions stv2c-opts
  :parents (stv2c)
  :short "Command line options for the stv2c tool."
  :tag :stv2c-opts

  ((help        booleanp
                "Show a brief usage message and exit."
                :rule-classes :type-prescription
                :alias #\h)

   (readme      booleanp
                "Show a more elaborate README message and exit."
                :rule-classes :type-prescription
                :alias #\r)

   (stv         stringp
                :argname "FILE"
                "The symbolic test vector that will be used to run the module."
                :rule-classes :type-prescription
                :default "")

   ;; Ordinary sorts of VL options...

   (start-files string-listp
                "Verilog files to parse. (Not options; this is the rest of
                 the command line, hence :hide t)"
                :hide t)

   (search-path string-listp
                :longname "search"
                :alias #\s
                :argname "DIR"
                "Search path for finding modules.  You can give this switch
                 multiple times, to set up multiple search paths in priority
                 order."
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

   (defines     string-listp
                :longname "define"
                :alias #\D
                :argname "VAR"
                "Set up definitions to use before parsing begins.  Equivalent
                 to putting `define VAR 1 at the top of your Verilog file.
                 You can give this option multiple times."
                :parser getopt::parse-string
                :merge acl2::cons)

   (edition     vl2014::vl-edition-p
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

(defconst *stv2c-help* (str::cat "
vl stv2c: Convert a symbolic run of a Verilog design into C++ code.

Example:  vl stv2c engine.v wrapper.v core.v \\
               --search ./simlibs \\
               --search ./baselibs \\
               --stv basic-run.stv

Usage:    vl stv2c [OPTIONS] file.v [file2.v ...] --stv [file.stv]

Options:

" *stv2c-opts-usage* "
"))

(defconst *stv2c-readme* (str::cat "
-------------------------------------------------------------------------------

                                STV2C README

-------------------------------------------------------------------------------

STV2C is a program for compiling certain \"symbolic runs\" of Verilog designs
into C++ code.


Representing Verilog Wires

  In Verilog, wires can have arbitrary width and each bit of a wire can have
  one of four values:

    0 - false
    1 - true
    X - unknown
    Z - undriven

  Actually, in transistor-level designs other values are possible, e.g., some
  bit could be a 'strong 1' or a 'weak 0.'  But STV2C only handles RTL designs,
  so we'll ignore this, and assume these four values are the only
  possibilities.

  To represent Verilog wires in C++, then, we need to decide:

   (a) How to encode the four possible values for a bit of a wire
   (b) How to encode arbitrary-width wires

  For (a) we use a typical onset/offset encoding.  A pair of C++ bits, named
  the ONSET and OFFSET, are used to encode the four Verilog values, as follows:

      ONSET        OFFSET         Meaning
      (C++ bit)    (C++ bit)      (Verilog value)
    ------------------------------------------------
        1            1              X
        1            0              1
        0            1              0
        0            0              Z
    ------------------------------------------------

  For (b) we use a fancy C++-11 template that lets us efficiently store the
  onset and offset bits together.  The template looks like this:

    fourval<N> {
       bit<N> onset;
       bit<N> offset
    }

  This encoding has some nice properties, e.g., there are fast bit operations
  for

   - promoting good Boolean vectors (i.e., bit<N>) into fourval<N> objects,
   - checking if a fourval<N> contains only good Boolean values,
   - getting masks for non-Boolean bits, etc.


Symbolic Test Vectors

  A symbolic test vector (STV) describes how to run a Verilog module, often
  over several clock phases.  STVs are used to prove theorems about hardware
  designs in the ACL2 theorem prover, and general documentation about STVs can
  be found at the following URLs:

     http://fv.centtech.com/acl2/latest/doc/?topic=ACL2____SYMBOLIC-TEST-VECTOR-FORMAT
     http://fv.centtech.com/acl2/latest/doc/?topic=ACL2____SYMBOLIC-TEST-VECTORS


BOZO finish this readme

-------------------------------------------------------------------------------
"))


(std::defaggregate stv-spec
  ((mod        stringp
               "Name of the top-level Verilog module to simulate."
               :rule-classes :type-prescription
               :default "")
   (inputs     "Input lines, if any.")
   (outputs    "Output lines, if any.")
   (internals  "Internal lines, if any.")
   (overrides  "Override lines, if any."))
  :tag :stv-spec-p)

(define parse-stv-file1
  ((lines "objects read from the .stv file")
   (spec  stv-spec-p "spec we're updating."))
  :returns (new-spec (equal (stv-spec-p new-spec)
                            (if new-spec t nil))
                     :hyp :guard)
  (b* (((when (atom lines))
        spec)
       ((when (atom (cdr lines)))
        ;; Everything must come in pairs.
        (raise "Stray ~x0 in stv file?" (car lines)))
       ((list* kwd value rest) lines)

       ((when (eq kwd :mod))
        (b* (((unless (stringp value))
              (raise ":mod followed by non-string?  ~x0." value))
             ((unless (equal (stv-spec->mod spec) ""))
              (raise ":mod given multiple times?")))
          (parse-stv-file1 rest
                           (change-stv-spec spec :mod value))))

       ((when (eq kwd :inputs))
        (b* (((when (stv-spec->inputs spec))
              (raise ":inputs given multiple times?")))
          (parse-stv-file1 rest
                           (change-stv-spec spec :inputs value))))

       ((when (eq kwd :outputs))
        (b* (((when (stv-spec->outputs spec))
              (raise ":outputs given multiple times?")))
          (parse-stv-file1 rest
                           (change-stv-spec spec :outputs value))))

       ((when (eq kwd :internals))
        (b* (((when (stv-spec->internals spec))
              (raise ":internals given multiple times?")))
          (parse-stv-file1 rest
                           (change-stv-spec spec :internals value))))

       ((when (eq kwd :overrides))
        (b* (((when (stv-spec->overrides spec))
              (raise ":overrides given multiple times?")))
          (parse-stv-file1 rest
                           (change-stv-spec spec :overrides value)))))

    (raise "Expected :mod, :inputs, :outputs, :internals, or :overrides.~%~
            Found ~x0." kwd)))

(define parse-stv-file ((filename stringp)
                        &key (state 'state))
  :returns (mv (spec stv-spec-p)
               (state state-p1 :hyp (state-p1 state)))
  (b* (((mv lines state)
        (read-file-objects filename state))
       (spec  (parse-stv-file1 lines (make-stv-spec)))
       ((unless spec)
        (raise "Parsing stv file failed.")
        (mv (make-stv-spec) state))
       ((when (equal (stv-spec->mod spec) ""))
        (raise "STV file doesn't say which :mod to simulate.")
        (mv (make-stv-spec) state)))
    (mv spec state)))

(define stv2c-program ((opts stv2c-opts-p)
                       &key (state 'state))

  (b* (((stv2c-opts opts) opts)

       (- (cw "stv2c: parsing stv file ~s0.~%" opts.stv))
       ((mv (stv-spec stv-spec) state)
        (parse-stv-file opts.stv))

       (loadconfig (vl2014::make-vl-loadconfig
                    :edition     opts.edition
                    :strictp     opts.strict
                    :start-files opts.start-files
                    :search-path opts.search-path
                    :search-exts opts.search-exts
                    :defines (vl2014::vl-make-initial-defines opts.defines)
                    :filemapp nil))
       (simpconfig (vl2014::make-vl-simpconfig))

       (- (cw "stv2c: loading Verilog files~%   ~x0~%" loadconfig))
       ((mv translation state)
        (vl2014::defmodules-fn loadconfig simpconfig))

       (mods   (vl2014::vl-design->mods (vl2014::vl-translation->good translation)))
       (vl-mod (vl2014::vl-find-module stv-spec.mod mods))
       ((unless vl-mod)
        (die "The Verilog module ~s0 (requested by ~s1) wasn't loaded?"
             stv-spec.mod opts.stv)
        state)

       (- (cw "stv2c: found requested module ~s0.~%" stv-spec.mod))
       (esim (vl2014::vl-module->esim vl-mod))
       ((unless esim)
        (die "The Verilog module ~s0 wasn't translated successfully.")
        state)
       ((unless (good-esim-modulep esim))
        (die "Strange problem with esim module.  ~@0"
             (bad-esim-modulep esim))
        state)

       (name (str::strsubst ".stv" "" opts.stv))

       (- (cw "stv2c: compiling stv ~s0.~%" name))
       (pstv (defstv-main
               :mod esim
               :name (intern$ name "ACL2")
               :inputs stv-spec.inputs
               :outputs stv-spec.outputs
               :internals stv-spec.internals
               :overrides stv-spec.overrides))

       ((unless pstv)
        (die "Failed to compile stv.")
        state)

       (- (cw "stv2c: compiling stv into c++~%"))
       (state (stv2c-main pstv)))
    state))


(define stv2c ((argv string-listp) &key (state 'state))
  :parents (symbolic-test-vectors)
  :short "Naive compiler from symbolic test vectors into C++ code."

  :long "<p>This is a tool for converting symbolic test vectors into C++
programs.  Practically speaking, this is just a way to incorporate a Verilog
design into some other program.</p>

<p>Our translation is naive in several ways, and we generally don't try to
optimize much of anything.  In the future, we may work to try to improve
performance.</p>"

  (b* (((mv errmsg opts start-files)
        (parse-stv2c-opts argv))
       ((when errmsg)
        (die "~@0~%" errmsg)
        state)

       (opts (change-stv2c-opts opts :start-files start-files))
       ((stv2c-opts opts) opts)

       ((when opts.help)
        (vl2014::vl-cw-ps-seq (vl2014::vl-print *stv2c-help*))
        (exit-ok)
        state)

       ((when opts.readme)
        (vl2014::vl-cw-ps-seq (vl2014::vl-print *stv2c-readme*))
        (exit-ok)
        state)

       ((when (equal opts.stv ""))
        (die "stv2c: --stv is required.")
        state)

       ((unless (consp opts.start-files))
        (die "stv2c: no Verilog files to process.")
        state)

       (- (cw "stv2c: starting up: ~%"))

       (- (cw " - start files: ~x0~%" opts.start-files))
       (state (vl2014::must-be-regular-files! opts.start-files))

       (- (cw " - stv file: ~x0.~%" opts.stv))
       (state (vl2014::must-be-regular-files! (list opts.stv)))

       (- (cw " - soft heap size ceiling: ~x0 GB~%" opts.mem))
       (- (acl2::set-max-mem ;; newline to appease cert.pl's scanner
           (* (expt 2 30) opts.mem)))

       (state (stv2c-program opts)))

    (exit-ok)
    state))

#||

(stv2c (list "--help"))

(stv2c (list "../../tutorial/alu16.v"))

(stv2c (list "../../tutorial/alu16.v" "--stv" "my_run.stv"))

(parse-stv-file "my-run.stv")

||#
