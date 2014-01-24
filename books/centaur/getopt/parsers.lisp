; ACL2 Getopt Library
; Copyright (C) 2013 Centaur Technology
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

(in-package "GETOPT")
(include-book "std/util/top" :dir :system)
(include-book "std/strings/strval" :dir :system)


(defsection parsers
  :parents (getopt)
  :short "Parsers for various kinds of command-line options."

  :long "<p>Different programs will need to take all sorts of different kinds
of options.  For instance:</p>

<ul>
<li>@('ssh') takes a port number between 0 and 65535,</li>
<li>@('svn') takes a revision number that can be a natural or a
    special word like @('HEAD'), @('BASE'), or @('PREV'),</li>
<li>@('wget') takes a URL,</li>
<li>@('mail') takes an email address, and so on.</li>
</ul>

<p>There's no way for @(see getopt) to anticipate and support everything that
every program might want, so instead we use a table-driven approach that you
can extend with custom parsers for your types.</p>

<p>Now, out of the box we do at least provide parsers for basic options like
@('--verbose'), @('--username jared'), @('--level=100000'), and so forth.</p>

<p>But when these aren't good enough, e.g., because you want to have stronger
type requirements on your arguments structure, you can add your own @(see
custom-parser) functions and plug them in.</p>")


(defsection custom-parser
  :parents (parsers)
  :short "How to write custom argument-parsing functions."

  :long "<p>You can extend getopt with new functions for parsing the arguments
you care about.</p>

<p>Note that once you have introduced such a new parsing function, you
can (optionally) register it as the default parser for a predicate using @(see
defparser).</p>

<p>Every argument-parsing function must have the following form:</p>

<box><code>
 (parse-foo name explicit-value args)
   &rarr;
 (mv errmsg? value rest-args)
</code></box>

<p>Inputs:</p>

<ul>

<li>@('name') is a string that is the name of the option the user typed in,
e.g., it might be @('--verbose').  This is included so that the parser can
provide a nice error message.</li>

<li>@('explicit-value') is @('nil') unless the use types something like
@('--foo=bar'), in which case it is the value being assigned, e.g.,
@('\"bar\"').</li>

<li>@('args') is a @(see string-listp) with the full command line arguments
that the user typed in after the @('name') and, if applicable, the
@('explicit-value').  It may be the empty list if @('name') was the last
argument to the program.</li>

</ul>

<p>Outputs</p>

<ul>

<li>@('errmsg?') should be @('nil') if everything is okay, or an error message
produced by @(see msg).  Typically it might be something like:

@({
     (msg \"Option ~s0 needs a valid port number, but got ~x1\"
            name (car args))
})</li>

<li>@('value') is irrelevant if there was an error, but otherwise must be a
valid @('foop'), for whatever kind of data this parser is supposed to
generate.</li>

<li>@('rest-args') should be the remainder of @('args') after the arguments to
@('name') have been removed.  For termination, its length must be no greater
than the length of @('args').</li>

</ul>

<p>All of the built-in parsers fit into the above scheme, so you can see
several examples of argument-parsing functions by just looking at the built-in
@(see parsers) like @(see parse-nat).</p>

<p>You might wonder why we have the @('explicit-value') separate from
@('args').  The basic reason is that we want to support any mixture of the
following syntaxes:</p>

<ul>
 <li>@('--color red ...')</li>
 <li>@('--color=red ...')</li>
</ul>

<p>Making the explicit-value explicit lets us very easily support this without
requiring, e.g., that every argument has exactly one value.</p>")

(table getopt 'parsers
       ;; Maps predicates to the names of their default parsing functions.
       nil)

(defun getopt-parsers (world)
  (declare (xargs :mode :program))
  (cdr (assoc-eq 'parsers (table-alist 'getopt world))))

(defun default-getopt-parser (predicate world)
  (declare (xargs :mode :program))
  (cdr (assoc predicate (getopt-parsers world))))

(defun check-plausibly-a-parser-p (ctx fn world)
  (declare (xargs :mode :program))
  (b* ((look (getprop fn 'acl2::formals :bad 'acl2::current-acl2-world world))
       ((when (eq look :bad))
        (er hard? ctx "~x0 is not the name of a defined function." fn))
       (nformals (len (look-up-formals fn world)))
       (nreturns (len (look-up-return-vals fn world)))
       ((unless (and (eql nformals 3)
                     (eql nreturns 3)))
        (er hard? ctx
            "The function ~x0 does not have the right signature for a getopt ~
             parser.  Expected 2 formals and 3 return vals, but found ~x1 and ~
             ~x2, respectively.  See :xdoc ~x3." fn nformals nreturns
             'custom-parser)))
    t))


(defsection defparser
  :parents (parsers)
  :short "Register a new argument-parsing function with @(see getopt)."

  :long "<p>@(call defparser) is a macro for registering parsing functions with
@(see getopt).</p>

<p>It first checks to make sure that @('fn') has the valid format for a @(see
custom-parser), and tries to prove the necessary progress property.</p>

<p>If @('predicate') is non-nil, it installs @('fn') as the default parsing
function to use for options of type @('predicate').  The general idea here is
that if you write a new custom parser for ports, you can then set it up to be
the default parser for any @('port-p') field.</p>"

  (defmacro defparser (fn &key predicate)
    (declare (xargs :guard (symbolp fn)))
    `(make-event
      (b* ((world (w state))
           (predicate ',predicate)
           (fn        ',fn)
           (- (check-plausibly-a-parser-p 'defparser fn world))
           ((unless (or (not predicate)
                        (and (eql (len (look-up-formals predicate world)) 1)
                             (eql (len (look-up-return-vals predicate world)) 1))))
            (er soft 'defparser
                "The function ~x0 does not seem like a valid unary predicate."
                predicate))
           (look (assoc predicate (getopt-parsers world)))
           ((unless (or (not predicate)
                        (not look)
                        (eq (cdr look) fn)))
            (er soft 'defparser
                "The predicate ~x0 already has a different getopt parser ~
               as its default: ~x1" predicate (cdr look))))
        (value
         '(progn
            (local (in-theory (enable ,fn)))

            (defthm ,(intern-in-package-of-symbol
                      (cat (symbol-name fn) "-MAKES-PROGRESS")
                      fn)
              (<= (len (mv-nth 2 (,fn name explicit-value args)))
                  (len args))
              :rule-classes ((:rewrite) (:linear)))

            ,@(if (not predicate)
                  nil
                `((table getopt 'parsers
                         (cons (cons ',predicate ',fn)
                               (getopt-parsers world)))))))))))


(define parse-plain
  :parents (parsers)
  :short "Parser for plain, argument-free options that are off by default and
must be explicitly enabled, e.g., @('--verbose') or @('--force')."

  :long "<p>We just return true, because by typing the name of the option the
user is saying they want to turn it on.  This is useful for options that the
user has to explicitly ask for because they are unsafe or just unusual.</p>"
  ((name stringp)
   (explicit-value (or (not explicit-value)
                       (stringp explicit-value)))
   (args string-listp))
  :returns (mv err
               (value booleanp :rule-classes :type-prescription)
               (rest-args string-listp :hyp (force (string-listp args))))
  (if explicit-value
      (mv (msg "Option ~s0 can't take an argument" name) nil args)
    (mv nil t args))
  ///
  (defparser parse-plain :predicate booleanp))


(define parse-string
  :parents (parsers)
  :short "Parser for options that require an argument, but where any arbitrary
string will do, e.g., @('--username') or @('--eval')."
  :long "<p>The only way this can fail is if there aren't any more arguments,
e.g., someone types something like @('myprogram --username') and doesn't say
what username to use.</p>"
  ((name stringp)
   (explicit-value (or (not explicit-value)
                       (stringp explicit-value)))
   (args string-listp))
  :returns (mv err
               (value stringp :rule-classes :type-prescription)
               (rest-args string-listp :hyp (force (string-listp args))))
  (b* (((mv val args)
        (if explicit-value
            (mv explicit-value args)
          (mv (car args) (cdr args))))
       ((unless val)
        (mv (msg "Option ~s0 needs an argument" name) "" args)))
    (mv nil (str::str-fix val) args))
  ///
  (defparser parse-string :predicate stringp))


(define parse-nat
  :parents (parsers)
  :short "Parser for options that require a @(see natp) argument, e.g.,
@('--tabsize') or @('-O'), etc."
  :long "<p>We just read the next string out of the argument list and try to
interpret it as a decimal number.  This fails if it there is no argument, or if
there are any non-numeric characters.</p>"
  ((name stringp)
   (explicit-value (or (not explicit-value)
                       (stringp explicit-value)))
   (args string-listp))
  :returns (mv err
               (value natp :rule-classes :type-prescription)
               (rest-args string-listp :hyp (force (string-listp args))))
  (b* (((mv val args)
        (if explicit-value
            (mv explicit-value args)
          (mv (car args) (cdr args))))
       ((unless val)
        (mv (msg "Option ~s0 needs an argument" name) 0 args))
       (ret (str::strval val))
       ((unless ret)
        (mv (msg "Option ~s0 needs a number, but got ~x1" name val)
            0 args)))
    (mv nil ret args))
  ///
  (defparser parse-nat :predicate natp))


(define parse-pos
  :parents (parsers)
  :short "Parser for options that require a @(see posp) argument, e.g.,
@('--block-size') or @('--line-number')."
  :long "<p>This is just like @(see parse-nat) except that we also cause
an error if the argument is zero.</p>"
  ((name stringp)
   (explicit-value (or (not explicit-value)
                       (stringp explicit-value)))
   (args string-listp))
  :returns (mv err
               (value posp :rule-classes :type-prescription)
               (rest-args string-listp :hyp (force (string-listp args))))
  (b* (((mv val args)
        (if explicit-value
            (mv explicit-value args)
          (mv (car args) (cdr args))))
       ((unless val)
        (mv (msg "Option ~s0 needs an argument" name) 1 args))
       (ret (str::strval val))
       ((unless ret)
        (mv (msg "Option ~s0 needs a number, but got ~x1" name val)
            1 args))
       ((when (eql ret 0))
        (mv (msg "Option ~s0 can't be zero" name) 1 args)))
    (mv nil ret args))
  ///
  (defparser parse-pos :predicate posp))

