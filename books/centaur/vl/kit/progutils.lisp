; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
(include-book "oslib/file-types-logic" :dir :system)
(include-book "centaur/getopt/parsers" :dir :system)
(include-book "../util/defs")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(include-book "std/testing/assert" :dir :system)

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


(define split-plusargs-exec ((args    string-listp)
                             (acc     string-listp)
                             (plusacc string-listp))
  :parents (split-plusargs)
  :returns (mv (acc     string-listp)
               (plusacc string-listp))
  (b* (((when (atom args))
        (mv (string-list-fix acc)
            (string-list-fix plusacc)))
       ((cons first rest) args)
       ((mv acc plusacc)
        (if (and (< 0 (length first))
                 (eql (char first 0) #\+))
            (mv acc (cons (subseq first 1 nil) plusacc))
          (mv (cons first acc) plusacc))))
    (split-plusargs-exec rest acc plusacc)))

(define split-plusargs ((args string-listp))
  :parents (kit)
  :short "Split command line arguments into plusargs and non-plusargs."
  :returns
  (mv (normal string-listp "Non-plusargs, in order.")
      (plusargs string-listp "Plusargs, in order, with the leading plus
                              characters removed."))
  (b* (((mv acc plusacc) (split-plusargs-exec args nil nil)))
    (mv (reverse acc) (reverse plusacc)))
  ///
  (assert!
   (b* (((mv normal plusargs)
         (split-plusargs (list "foo.v" "bar.v" "+xxx" "+yyy"))))
     (and (equal normal (list "foo.v" "bar.v"))
          (equal plusargs (list "xxx" "yyy"))))))
