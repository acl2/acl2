; ACL2 Getopt Library
; Copyright (C) 2013 Centaur Technology
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

(in-package "GETOPT-DEMO")
(include-book "top")
(include-book "std/strings/top" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)
(local (include-book "std/typed-lists/string-listp" :dir :system))

(defoptions demo
  :parents (getopt)
  :short "A basic demo of using @(see getopt) to parse command-line options."

  :long "<p>This is a basic demo of how to use getopt, and a collection of unit
tests to make sure getopt is working correctly.</p>

<p>Note: our focus in this demo is just on the command-line parsing piece.  We
illustrate illustrates a lot of the things you can do with getopt, e.g., short
aliases, long names, default values, validating inputs, and accumulating
arguments.  But we <b>don't</b> turn it into a working program.  If you want to
understand how @(see getopt) and @(see argv) and @(see save-exec) fit together,
see @(see demo2).</p>

<p>This @('defoptions') call does two things:</p>

<ul>

<li>It introduces @('demo-p'), an ordinary @(see std::defaggregate) with
various fields and well-formedness conditions.  These @('demo-p') structures
can be passed around throughout your program just like any ordinary ACL2
object.</li>

<li>It introduces @(see parse-demo), a function that can parse a command-line
into a @('demo-p').  The command-line is represented as a list of strings; see
for instance @(see oslib::argv) to understand how to get the command-line
arguments given to ACL2.</li>

</ul>"

  ;; GETOPT::DEFOPTIONS is a strict superset of defaggregate.  So, everything
  ;; here should look very familiar if you have created aggregates:

  :tag :demo

  ((help    "Print a help message and exit with status 0."
            booleanp
            :rule-classes :type-prescription

            ;; Because this field is a Boolean, defoptions automatically
            ;; "knows" to treat it as a plain option, i.e., it knows that
            ;; --help takes no extra argument.

            ;; You don't have to tell it to use --help, either, because it
            ;; just figures that out from the field name.

            ;; However, if we want to also support -h, we need to tell it
            ;; to treat the letter #\h as an alias for help:
            :alias #\h)

   (verbose "Turn on excessive debugging information."
            booleanp
            :rule-classes :type-prescription

            ;; As with --help, there's little "extra" work to do here.  We
            ;; won't create an alias, because we'll use -v for --version.
            )

   (version "Print version information and exit with status 0."
            booleanp
            :rule-classes :type-prescription
            :alias #\v)

   (username "Change the username to something else."
             stringp
             :rule-classes :type-prescription
             :default ""
             :alias #\u
             :argname "NAME"
             ;; This option is more interesting.  By default, a stringp option
             ;; takes an argument.  The ARGNAME affects how its printed in the
             ;; usage message.
             )

   (port     "Port to connect to."
             natp
             :rule-classes :type-prescription
             :default 55432
             :alias #\p
             :argname "PORT"
             ;; Support for numeric arguments is built into defoptions, so it
             ;; can automatically parse the option into a number for you.  We
             ;; don't need to put in a :parser option here because parse-nat is
             ;; the default for natp fields, but just to make this demo more
             ;; complete I include it.
             :parser getopt::parse-nat)

   (dirs    "Directory list"
            string-listp

            ;; This option is more interesting in several ways.  The idea here
            ;; is that the user can say, e.g.,
            ;;
            ;;   --dir /usr --dir /home --dir /bin
            ;;
            ;; And these options should all get bundled up together into a
            ;; single list.

            ;; Well, internally in our program, we want to think of this as a
            ;; list of dirs.  So, we want to call the field "dirs".  But the
            ;; user enters one dir at a time, so we want the user-visible
            ;; option name to be different.  We can do that by overriding the
            ;; longname that defoptions generates by default:
            :longname "dir"

            ;; Now, defoptions has no default way to parse in a string-listp.
            ;; But it does have a built-in string parser, which we can reuse.
            ;; So, first, tell it to use the string parser:
            :parser getopt::parse-string

            ;; But that wouldn't be enough on its own, because if we just set
            ;; it to use parse-string, then that produces a stringp instead of
            ;; a string-listp, and our proofs would fail.  Instead, we need to
            ;; tell defoptions how to merge the results of the parser with the
            ;; previous value.  Using CONS would actually reverse the order of
            ;; the dirs, because the options are processed in order.  So we
            ;; avoid that by using rcons, to push the strings on the end.
            :merge rcons)

   (extra-stuff "Hidden option that the user never sees, but that is part of
                 our aggregate."
                :hide t)

   (extra-stuff2 stringp
                 "Hidden option that the user never sees, but that is part of
                 our aggregate."
                 :hide t
                 :default "")))


#||

;; Some good things to try:

(xdoc::xdoc 'parse-demo)

(princ$ *demo-usage* *standard-co* state)

||#


;; Here are some basic tests to make sure it's working.

(defun run-parse-demo (input)
  (let ((tokens (str::strtok input '(#\Space))))
    (mv-let (err result extra)
      (parse-demo tokens)
      (if err
          (prog2$ (cw "~@0~%" err)
                  (list :err err))
        (let ((res (list :result result
                         :extra extra)))
          (prog2$ (cw "Success: ~x0~%" res)
                  res))))))

(defmacro check (input result extra)
  `(acl2::assert! (equal (run-parse-demo ,input)
                         (list :result ,result :extra ,extra))))

(defmacro fail (input)
  `(acl2::assert! (equal (car (run-parse-demo ,input))
                         :err)))

(check "" (make-demo) nil)

(check "--help --version"
       (make-demo :help t :version t)
       nil)

(check "--version --help"
       (make-demo :help t :version t)
       nil)

(fail "--help=123")
(fail "--help --help")
(fail "--hlep")


(fail "--port")
(fail "--port abc")

(check "--port 123"
       (make-demo :port 123)
       nil)

(check "--port=123"
       (make-demo :port 123)
       nil)

(check "--dir= --dir=abc --dir= --dir=xyz"
       (make-demo :dirs '("" "abc" "" "xyz"))
       nil)

(check "-h -v"
       (make-demo :help t :version t)
       nil)

(check "-h --version"
       (make-demo :help t :version t)
       nil)

(check "-hv"
       (make-demo :help t :version t)
       nil)

(fail "-huv")
(fail "-hxv")
(fail "-u")

(check "-hv"
       (make-demo :help t :version t)
       nil)

(fail "-p")
(fail "-p abc")

(check "-p 123"
       (make-demo :port 123)
       nil)

(check "-p=123"
       (make-demo :port 123)
       nil)

(check "a b c d"
       (make-demo)
       '("a" "b" "c" "d"))

(check "a -u b c d"
       (make-demo :username "b")
       '("a" "c" "d"))

(check "a -u=b c d"
       (make-demo :username "b")
       '("a" "c" "d"))

(check "a -u b c -p=12 d"
       (make-demo :username "b"
                  :port 12)
       '("a" "c" "d"))

(check "a b c --dir dir1 d e f"
       (make-demo :dirs '("dir1"))
       '("a" "b" "c" "d" "e" "f"))

(check "a b c --dir dir1 --dir dir2 d e f"
       (make-demo :dirs '("dir1" "dir2"))
       '("a" "b" "c" "d" "e" "f"))

(check "a b c --dir=dir1 --dir dir2 d e f"
       (make-demo :dirs '("dir1" "dir2"))
       '("a" "b" "c" "d" "e" "f"))

(check "a b c --dir=dir1 --dir=dir2 d e f"
       (make-demo :dirs '("dir1" "dir2"))
       '("a" "b" "c" "d" "e" "f"))

(check "a b c --dir dir1 --help --dir dir2 d e f"
       (make-demo :help t
                  :dirs '("dir1" "dir2"))
       '("a" "b" "c" "d" "e" "f"))

(check "a b c --dir dir1 --help x y z --dir dir2 d e f"
       (make-demo :help t
                  :dirs '("dir1" "dir2"))
       '("a" "b" "c" "x" "y" "z" "d" "e" "f"))

(check "a b c --dir dir1 --help x y z --dir=dir2 d e f --dir dir3"
       (make-demo :help t
                  :dirs '("dir1" "dir2" "dir3"))
       '("a" "b" "c" "x" "y" "z" "d" "e" "f"))

(fail "a b c --dir")

(fail "a b c --dir dir1 --dir")


(check "--"
       (make-demo)
       '("--"))


(check "-- --help"
       (make-demo)
       '("--" "--help"))

(check "-- -x -y -z"
       (make-demo)
       '("--" "-x" "-y" "-z"))

(check "--verbose -- --help"
       (make-demo :verbose t)
       '("--" "--help"))
