; ACL2 Bridge
; Copyright (C) 2012 Centaur Technology
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

(in-package "BRIDGE")
(include-book "xdoc/top" :dir :system)
(include-book "tools/include-raw" :dir :system)
(include-book "std/strings/top" :dir :system)
(include-book "to-json")
; (depends-on "bridge-raw.lsp")

(defxdoc bridge
  :parents (acl2::interfacing-tools)
  :short "Connects ACL2 and the outside world."

  :long "<p>The ACL2 Bridge is a general mechanism for allowing other
programming languages, which may be much better than Lisp for certain tasks
like developing graphical user interfaces, to interact with ACL2.  It extends
ACL2 with a server that can accept connections from client programs and run
commands on their behalf.  The basic picture is:</p>

@({
   _____________                    _______________________
  |             |                  |                       |
  |   ACL2   [bridge]--------------|  client program       |
  |             |      socket      |  java, c, perl, ...   |
  |_____________|                  |_______________________|
})

<p>On the ACL2 side, the bridge is a simple listen/accept style server that
waits for new clients.  When a client connects, it creates a new worker thread
to handle the client's requests.  The worker thread presents the client with a
kind of read-eval-print loop.</p>

<p>The client then sends @(see command)s.  Basically each command says what
s-expression to evaluate, and also indicates how the reply should be encoded.
For instance, you can tell the bridge to return raw s-expressions, or you can
tell it to use @(see json-encoding) to make the output easy to parse in some
other programming languages.  Other options may be added in the future.</p>

<p>The worker thread executes the command.  As it runs, it may send @(see
message)s to the client.  These messages contain output that has been printed
to standard output, the return value or error conditions, and a ready indicator
that says when the worker is ready for more input.  The messages are tagged
with types so that the client can tell what kind of output it's receiving.</p>

<p>Some things are missing.  There's currently no support for Lisp functions
that want to read from standard input after they've been invoked.  For
instance, there's not really any way to interact with break loops, @('ld'),
etc.  There's also currently no direct way to send an interrupt.  However,
workers announce their name to the client when they say hello, so a client
could presumably open another connection and interrupt that way.  We haven't
developed this much, yet.</p>")


(defxdoc security
  :parents (bridge)
  :short "Important warnings about network security and the ACL2 bridge."

  :long "<p>The ACL2 bridge allows clients to run arbitrary Lisp commands,
including for instance syscall.  Because of this,</p>

<box><p>If a malicious person can connect to your bridge, then he can read or
delete your files, run arbitrary programs as you, and so on.</p></box>

<p>To reduce the chances of this happening, you should probably only run the
bridge on a <a href='http://en.wikipedia.org/wiki/Unix_domain_socket'>unix
domain socket</a>.  These sockets appear to have good security
properties.  (Per my understanding: remote users on the internet cannot connect
to them, and they even offer some protection from other users on your system
through the normal Unix filesystem permissions.)</p>

<p>The bridge <i>can</i> also be run on an ordinary TCP/IP socket, <b><color
rgb='#ff0000'>but this is very scary</color></b> because remote clients can
connect.  If you decide to run it this very scary way, then you should be very
scared:</p>

<ul>

<li>The bridge has <b>no authentication</b> mechanism, and will allow anyone
who can connect to it to run any command.</li>

<li>The bridge sends all messages in <b>plain text</b>, so an eavesdropper can
probably see everything you send to the server and everything it sends
back.</li>

</ul>

<p>So, before you even <i>think</i> about putting the bridge on a TCP/IP port,
you should make sure that, e.g., you have firewalls in place or are using SSH
tunnels or something.</p>

<p><b>Disclaimer</b>.  I am no security expert.  The advice above is probably
not enough to protect you.  Please do not use the ACL2 Bridge without
consulting your local security expert and network administrator.</p>")


(defxdoc message
  :parents (bridge)
  :short "Messages that the bridge sends to the client program."

  :long "<p>We send all output to the client in discrete <b>messages</b>.  The
message format is very simple.  It is easy for a client to reliably parse, and
doesn't require us to think about character encoding.  Informally, the format
is:</p>

@({
 type len[newline]
 contents[newline]
})

<p>To make this extremely clear: we first print the @('type'), then a space,
then the @('len'), then a newline character, then the @('contents'), then
another newline character.</p>

<p>The @('type') here is a label that describes what kind of message this is.
It matches @('[A-Z][A-Z0-9_]*').  That is, it starts with an uppercase
alphabetic character, and then contains only uppercase alphabetic, numeric, and
underscore characters.</p>

<p>The @('len') says how many characters are in @('contents').  It matches
@('[0-9]+'), i.e., it is a base-10 natural number.</p>")


(defxdoc command
  :parents (bridge)
  :short "Commands that the client sends to the bridge."

  :long "<p>Each client is expected to send discrete <b>commands</b> that will
be processed individually.</p>

<p>The command format is identical to the @(see message) format, and is meant
to be very easy for the client to generate.  Clients should typically
@('flush') the stream after printing their command to ensure that the server
gets the input.</p>

<p>The @('type') of the command governs how the server should send the result
back to the client.  The currently supported command types are:</p>

<ul>

<li>@('LISP') -- send only the first return value, and just use @('prin1') to
encode it.</li>

<li>@('LISP_MV') -- send all of the return values, essentially by doing
@('prin1') on the @('multiple-value-list') of the result.</li>

<li>@('JSON') -- send the @(see json-encoding) of the first return value.  Note
that this encoder only handles good ACL2 objects.</li>

<li>@('JSON_MV') -- send the @(see json-encoding) of the
@('multiple-value-list') of the result.  Note that this encoder only handles
good ACL2 objects.</li>

</ul>

<p>Adding other types would be trivial.  For instance, it might be useful to
add pretty-printing.</p>")


(defxdoc bindings
  :parents (bridge)
  :short "ACL2 Bridge interfaces for other programming languages."

  :long "<p>The ACL2 Bridge can probably be used from just about any
programming language that has sockets.</p>

<p>There is a nice <a href='https://www.ruby-lang.org/'>Ruby</a> interface in
@('books/centaur/bridge/ruby').</p>

<p>A <a href='https://www.python.org/'>Python</a> interface with synchronous and
asynchronous bindings is available in @('books/centaur/bridge/python').</p>

<p>For other programming languages, implementing a client should be a very easy
exercise: just read about @(see command)s and @(see message)s to understand the
communication.  You might look at the Ruby interface as an example.</p>")


(defsection start
  :parents (bridge)
  :short "Start an ACL2 Bridge server."

  :long "<p><b>Warning:</b> don't even <i>think</i> about starting an ACL2
Bridge until you have read about @(see security).</p>

<p>Unix Domain Socket Examples (recommended):</p>

@({
 (bridge::start \"./my-socket\")
 (bridge::start \"/tmp/my-socket\")
})

<p>TCP/IP Socket Examples (<b>very scary</b> -- see @(see security)!!!):</p>

@({
 (bridge::start nil)     ;; Listen on TCP/IP port 55432
 (bridge::start 12345)   ;; Listen on TCP/IP port 12345
})

<p>Additional keyword options:</p>

<ul>
<li>@(':stack-size') -- stack size for worker threads (in bytes)</li>
<li>@(':tstack-size') -- temporary stack size for worker threads (in bytes)</li>
<li>@(':vstack-size') -- value stack size for worker threads (in bytes)</li>
</ul>"

  (defun start-fn (socket-name-or-port-number
                   stack-size
                   tstack-size
                   vstack-size)
    (declare (xargs :guard t)
             (ignorable socket-name-or-port-number
                        stack-size
                        tstack-size
                        vstack-size))
    (cw "Under-the-hood definition of bridge::start-fn not installed?~%"))

  (defmacro start (socket-name-or-port-number
                   &key
                   (stack-size '(* 16 (expt 2 20)))
                   (tstack-size '(* 16 (expt 2 20)))
                   (vstack-size '(* 16 (expt 2 20))))
    `(start-fn ,socket-name-or-port-number
               ,stack-size
               ,tstack-size
               ,vstack-size)))


(defsection stop
  :parents (bridge)
  :short "Stop any running ACL2 Bridge servers."

  :long "<p>This is a low-level cleanup mechanism that ungracefully kills any
bridge-listener and bridge-worker threads.  This isn't something you probably
want to ordinarily rely on in your code, but it's useful when you want to
restart a server.</p>"

  (defun stop ()
    (declare (xargs :guard t))
    (cw "Under-the-hood definition of bridge::stop not installed?")))



; A few functions that are handy for testing things.

(defun fib (n)
  (declare (xargs :guard (natp n)))
  (cond ((zp n)
         1)
        ((= n 1)
         1)
        (t
         (+ (fib (- n 1))
            (fib (- n 2))))))

(memoize 'fib)

(defun sleep$ (n)
  "Sleep for (rfix n) seconds.  Has an under-the-hood implementation."
  (declare (xargs :guard t)
           (ignore n))
  nil)

(defun sleepyprint (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      nil
    (progn$ (cw "Sleepy print: ~x0~%" n)
            (sleep$ 1)
            (sleepyprint (- n 1)))))



(defttag :bridge)
#+ccl
(include-raw "bridge-raw.lsp")
#-ccl
(progn!
 (set-raw-mode t)
 (defun run-in-main-thread-raw (irrelevant-variable-for-return-last form)
   (error "Run-in-main-thread is a CCL utility.~%~It is not supported for ~
           this host Lisp."))
 (defun try-to-run-in-main-thread-raw (irrelevant-variable-for-return-last form)
   (error "NOTE: Try-to-run-in-main-thread is a CCL utility.~%~It is not ~
           supported for this host Lisp.")))

(defsection in-main-thread
  :parents (bridge)
  :short "Special mechanism for making sure forms execute in the main thread."

  :long "<p>This is a special form that is only meant to be used by ACL2 Bridge
clients when they issue commands.  A syntax example is:</p>

@({
 (bridge::in-main-thread (memoize 'fib) (fib 37))
})

<p>This is really just a hack that lets you use commands that, for one reason
or another, must only ever be executed in the \"main\" thread (in CCL parlance,
the \"initial listener\" thread).  Practical applications include:</p>

<ul>

<li>Running memoized functions (the memoization code isn't thread-safe, and
attempts to use a memoized function in multiple thread can result in hard
errors), and</li>

<li>Doing computations that involve a lot of @(see hons)ing (otherwise, each
thread has its own hons space, and you may not get the sharing you are
expecting).</li>

</ul>

<p>If the main thread is busy with work from other clients, this form will wait
until it becomes available again.  See also @(see try-in-main-thread), which
instead just causes an error if the main thread is busy.</p>"

  (defmacro-last run-in-main-thread)

  (defmacro in-main-thread (&rest forms)
    ;; Waits until the main-thread is available, then uses it to execute forms.
    `(run-in-main-thread :irrelevant-val-for-return-last
                         (progn$ . ,forms))))



(defsection try-in-main-thread
  :parents (bridge)
  :short "Alternative to @(see in-main-thread) that exits immediately if the
main thread is already busy with something else."

  (defmacro-last try-to-run-in-main-thread)

  (defmacro try-in-main-thread (&rest forms)
    ;; Checks if the main-thread is available, and if so uses it to execute
    ;; forms.  Otherwise, causes an error.
    `(try-to-run-in-main-thread :irrelevant-val-for-return-last
                                (progn$ . ,forms))))


(defun test-imt (x)
  (declare (xargs :guard (natp x)))
  (in-main-thread
   (cw "Hello ")
   (cw "World~%")
   (+ 1 x)))

(defun test-timt (x)
  (declare (xargs :guard (natp x)))
  (try-in-main-thread
   (cw "Hello ")
   (cw "World~%")
   (+ 1 x)))

