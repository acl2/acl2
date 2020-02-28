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
(include-book "data")
(include-book "../mlib/fmt")
(include-book "centaur/bridge/to-json" :dir :system)
(local (include-book "../util/arithmetic"))
(include-book "std/testing/assert" :dir :system)

(defsection vls-commands
  :parents (vl-server)
  :short "A simple command format for interfacing between Lisp and Javascript."

  :long #{"""<h3>Introduction</h3>

<p>The @(see vl-server) makes many Lisp functions available for use by the
Javascript code that runs the module browser.  To make interfacing between
Javascript and Lisp simpler, we adopt certain conventions for how these
commands work.</p>

<p>A few of VL server operations, such as those for selecting models, are
special and do not follow the normal conventions.  However, for the most part,
we are generally wanting to deal with commands where:</p>

<ul>

<li>The command is a @('get') operation that affects no state except perhaps
for implicit state like memoization tables, hons spaces, etc.  We'll arrange so
that the memo tables and hons spaces are set up correctly before invoking the
command.</li>

<li>The model has already been selected.  We'll arrange so that the server code
will access the proper model, and invoke our Lisp command function with the
selected @(see vls-data-p) structure as one of its arguments.</li>

<li>The command may need other arguments.  To keep the command format regular,
we'll require the Lisp function to take any extra arguments as strings, and it
will be responsible for parsing these as necessary, e.g., to convert line
numbers from @('"5"') into @('5').</li>

<li>The command may produce JSON or HTML formatted output.</li>

</ul>

<h3>JSON Commands</h3>

<p>Most commands need to dive down into part of the model and retrieve some
information.  This process might fail or succeed.  For uniformity on the
Javascript side, we will expect each JSON-producing command to signal its
failure by producing a JSON-encoded error message of the form:</p>

@({
     {":ERROR": "Couldn't do such and so..."}
})

<p>This can be done by calling @(see vls-fail).  Meanwhile, every
JSON-producing command that succeeds should produce a result of the form:</p>

@({
     {":ERROR": false,
      ":VALUE": ...actual result goes here...}
     }
})

<p>This can be done by calling @(see vls-success).</p>

<h3>HTML Commands</h3>

<p>HTML producing commands are assumed to never fail.  Their content is
generally intended to be sent directly to the web browser and not processed
further.  An HTML-producing command can generally produce a simple error
message in HTML format.</p>"""})

(local (xdoc::set-default-parents vls-commands))


(defsection vls-fail
  :short "Create a \"standard\", JSON-encoded error message for a VL server
          command."
  :long "<p>The usage is like with @(see vl-cw).</p>"

  (define vls-fail-fn ((msg stringp)
                       (alist alistp))
    :returns (json stringp :rule-classes :type-prescription)
    (b* ((err (with-local-ps (vl-fmt msg alist))))
      (bridge::json-encode
       (list (cons :error err)))))

  (defmacro vls-fail (msg &rest args)
    `(vls-fail-fn ,msg (pairlis$
                        '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
                        (list . ,args))))

  (assert!
   (equal (vls-fail "Error, something is ~x0 instead of ~x1." 'wrong 'right)
          "{\":ERROR\":\"Error, something is WRONG instead of RIGHT.\"}")))


(define vls-success
  :short "Create a \"standard\", JSON-encoded successful return value for
          a VL server command."
  (&key (json stringp "Should be a json-encoded string for the actual value you
                       want to return.  This is a keyword argument to remind the
                       caller that they need to provide a json-encoded value."))
  :returns (extended-value stringp :rule-classes :type-prescription)
  (cat "{\":ERROR\": false, \":VALUE\": " json "}")
  ///
  (assert! (equal (vls-success :json "Hello")
                  "{\":ERROR\": false, \":VALUE\": Hello}")))


(defenum vls-commandtype-p
  (:json :html))

(defaggregate vls-commandinfo
  ((fn   symbolp
         "Name of the function that will execute this command.  Should have
          the signature @('(fn [args] data)') &rarr; @('string').")
   (args symbol-listp
         "Names of the arguments.")
   (type vls-commandtype-p "Content type produced by this command.")))

(deflist vls-commandinfolist-p (x)
  (vls-commandinfo-p x))


(defsection commands-table
  :short "A list of registered @(see vls-commands)."

  :long "<p>At startup the VL server will automatically define hunchentoot
command handlers corresponding to all of the commands in this table.</p>

<p>The proper way to extend this table is with @(see define-vls-json) or @(see
define-vls-html).</p>"

  (table vl-server 'commands
         ;; Commands is just a list of all VL server commands that have been
         ;; defined.
         nil)

  (define get-vls-commands (world)
    (declare (xargs :mode :program))
    (cdr (assoc-eq 'commands (table-alist 'vl-server world)))))



(define vls-command-arg-to-eformal ((arg symbolp))
  (list arg (if (equal arg 'data)
                'vls-data-p
              'stringp)))

(defprojection vls-command-args-to-eformals ((x symbol-listp))
  (vls-command-arg-to-eformal x))

(define define-vls-command-fn (name args type rest)
  (b* (((unless (symbolp name))
        (raise "Name must be a symbol, but got ~x0." name))
       ((unless (and (symbol-listp args)
                     (uniquep args)))
        (raise "Arguments to ~x0 must be unique symbols." name))
       ((unless (uniquep (str::downcase-string-list (symbol-list-names args))))
        (raise "Arguments to ~x0 do not have unique symbol names." name))
       ((unless (member 'data args))
        (raise "Arguments to ~x0 do not include data." name))
       (reserved-names (intersection-equal '("BASE" "MODEL") (str::symbol-list-names args)))
       ((when reserved-names)
        (raise "Arguments to ~x0 use reserved names ~&1." reserved-names))
       ((unless (vls-commandtype-p type))
        (raise "Unrecognized command type for ~x0." name))
       (info (make-vls-commandinfo :fn name
                                   :args args
                                   :type type))
       (eargs (vls-command-args-to-eformals args)))
    `(progn
       (define ,name ,eargs
         :returns (ans stringp :rule-classes :type-prescription)
         . ,rest)
       (table vl-server 'commands
              (cons ',info (get-vls-commands world))))))


(defsection define-vls-json
  :parents (commands-table)
  :short "Add a JSON-producing command to the VL server."
  :long "<p>See @('server.lisp') for several examples.</p>"

  (defmacro define-vls-json (name formals &rest rest)
    (define-vls-command-fn name formals :json rest)))


(defsection define-vls-html
  :parents (commands-table)
  :short "Add an HTML-producing command to the VL server."
  :long "<p>See @('server.lisp') for several examples.</p>"

  (defmacro define-vls-html (name formals &rest rest)
    (define-vls-command-fn name formals :html rest)))


(local
 (progn

   (define-vls-json testcmd0 (data)
     (declare (ignorable data))
     "five")

   (define-vls-json testcmd1 (data)
     (b* (((vls-data data)))
       (vls-success :json (bridge::json-encode (len data.filemap)))))

   (define-vls-json testcmd2 (name data)
     (b* (((vls-data data))
          (desc (cdr (hons-assoc-equal name data.orig-descalist)))
          ((unless desc)
           (vls-fail "Didn't find ~x0." name)))
       (vls-success :json (bridge::json-encode name))))
   ))
