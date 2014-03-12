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
(include-book "oslib/file-types" :dir :system)
(include-book "centaur/getopt/parsers" :dir :system)
(include-book "../util/defs")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))

(in-theory (disable (:executable-counterpart acl2::good-bye-fn)))

(define exit-ok ()
  (exit 0))

(define exit-fail ()
  (exit 1))

(in-theory (disable (:executable-counterpart exit-ok)
                    (:executable-counterpart exit-fail)))

(defmacro die (&rest args)
  `(progn$ (cw . ,args)
           (exit-fail)))


(define must-be-regular-files! ((files string-listp) &key (state 'state))
  :returns (state state-p1 :hyp (force (state-p1 state)))
  (b* ((files (mergesort files))
       ((mv err missing-files state) (oslib::missing-paths files))
       ((when err)
        (die "Error checking existence of ~&0:~%~@1~%" files err)
        state)
       (missing-files (mergesort missing-files))
       ((when missing-files)
        (die "File~s0 not found: ~&1~%"
             (if (vl-plural-p missing-files) "s" "")
             missing-files)
        state)
       ((mv err regular-files state) (oslib::regular-files files))
       ((when err)
        (die "Error checking file types of ~&0:~%~@1~%" files err)
        state)
       (irregular-files (difference files (mergesort regular-files)))
       ((when irregular-files)
        (die "File~s0 not regular: ~&1~%"
             (if (vl-plural-p irregular-files) "s are" " is")
             irregular-files)
        state))
    state))


(define must-be-directories! ((dirs string-listp) &key (state 'state))
  :returns (state state-p1 :hyp (force (state-p1 state)))
  (b* ((dirs (mergesort dirs))
       ((mv err missing-dirs state) (oslib::missing-paths dirs))
       ((when err)
        (die "Error checking existence of ~&0:~%~@1~%" dirs err)
        state)
       (missing-dirs (mergesort missing-dirs))
       ((when missing-dirs)
        (die "~s0 not found: ~&1~%"
             (if (vl-plural-p missing-dirs) "Directories" "Directory")
             missing-dirs)
        state)
       ((mv err regular-dirs state) (oslib::directories dirs))
       ((when err)
        (die "Error checking file types of ~&0:~%~@1~%" dirs err)
        state)
       (irregular-dirs (difference dirs (mergesort regular-dirs)))
       ((when irregular-dirs)
        (die "~s0: ~&1~%"
             (if (vl-plural-p irregular-dirs)
                 "Paths are not directories"
               "Path is not a directory")
             irregular-dirs)
        state))
    state))



(define vl-parse-edition
  :parents (vl-edition-p)
  :short "@(see Getopt) option parser for Verilog editions."
  ((name stringp)
   (explicit-value (or (not explicit-value)
                       (stringp explicit-value)))
   (args string-listp))
  :returns (mv err
               (value vl-edition-p)
               (rest-args string-listp :hyp (force (string-listp args))))
  (b* (((mv err val args) (getopt::parse-string name explicit-value args))
       ((when err)
        ;; Propagate error, fix up default value for unconditional return type
        (mv err :system-verilog-2012 args))
       ((when (str::istreqv val "Verilog"))
        (mv nil :verilog-2005 args))
       ((when (str::istreqv val "SystemVerilog"))
        (mv nil :system-verilog-2012 args)))
    (mv (msg "Option ~s0 must be 'Verilog' or 'SystemVerilog', but got ~x1"
             name val)
        :system-verilog-2012 args))
  ///
  (getopt::defparser vl-parse-edition :predicate vl-edition-p))