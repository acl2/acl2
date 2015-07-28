; Oracle Timing
; Copyright (C) 2015 Kestrel Institute (http://www.kestrel.edu)
;
; License: (An MIT license):
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
; Original authors: Jared Davis <jared@kookamara.com>

(in-package "ACL2")
(include-book "tools/include-raw" :dir :system)
(include-book "std/util/bstar" :dir :system)
(local (include-book "oslib/read-acl2-oracle" :dir :system))
; (depends-on "oracle-time-raw.lsp")

(defxdoc oracle-time
  :parents (time$)
  :short "Carry out a computation, returning (not just printing!) how long it
took and (on supported Lisps) how many bytes were allocated."

  :long "<p>The @('oracle-time') macro allows you to run a form and get the
elapsed time and memory allocation back as real ACL2 values.</p>

<p>In most cases, you don't really need to do this.  Instead, see @(see time$),
which is built into ACL2 and allows you to print the runtime and allocation of
a form as a logically invisible side-effect.  Since @(see time$) doesn't return
the elapsed time or allocation, it is simpler and doesn't need access to @(see
state).  It also has some nice features for controlling when timing information
is printed.</p>

<p>On the other hand, if you want to do things like collect up tables that
describe how your functions perform on various inputs, then @(see time$) won't
do what you want: it just prints the timing information to the terminal,
leaving you with no way to collect and compare the times and allocations.  In
this case, @('oracle-time') may be able to do what you want.  The main
limitation is that it does need access to the state.</p>


<h5>Basic Example</h5>

@({
    (oracle-time (fib 35))   ; Simple since it returns a single value
      -->
    (mv time                 ; Rational, number of seconds
        bytes                ; Natural, bytes allocated
        ans                  ; Answer from (fib 35)
        state)               ; Updated state
})


<h5>Example with Multiple Return Values</h5>

@({
    (oracle-time (random$ 100 state)  ; Returns multiple values
       :ret (mv ans state))           ; Explains the return type
      -->
    (mv time                          ; Rational, number of seconds
        bytes                         ; Natural, bytes allocated
        ans                           ; The random number produced
        state)                        ; Updated state
})

<p>See also the file @('[books]/tools/oracle-time-tests.lisp') for some
additional tests and working examples.</p>

<h5>General Form</h5>

@({
    (oracle-time form [:ret retspec])
})

<p>The @('form') can be any arbitrary ACL2 form that you want to execute.  If
the form returns an ordinary, single value, e.g., as in @('(fib 35)') then the
@(':ret') argument is not needed.  Otherwise, @(':ret') should explain the
return signature of @('form').</p>

<p>The return value of @('oracle-time') extends the return value of @('form')
with multiple values.  The basic idea is that @('oracle-time') is going to
macroexpand to something like this:</p>

@({
     (mv-let retspec
        form
        (b* (((mv & time state) (read-acl2-oracle state))
             ((mv & bytes state) (read-acl2-oracle state)))
          (mv time bytes retspec [state])))
})

<p>You can see here that the @('retspec') is used to explain how to bind the
results of executing the form.  It is also, essentially, spliced into the
return value of the whole @('oracle-time') call.  The only twist is that if
@('retspec') mentions @('state'), then we don't add an extra @('state') onto
the end of the form.</p>")

; Implementation notes.
;
; The main macro is oracle-time-exec, which runs the form using a classic
; return-last style, but times the form and records these timings in a stack so
; that they can be subsequently extracted using what logically looks like
; oracle reads.
;
; We use a stack so that oracle-time calls can be nested.
;
; The extraction function logically just does a couple of oracle reads, but
; under the hood it pulls these values off of the stack.

(defund oracle-time-extract (state)
  "Has an under-the-hood definition."
  (declare (xargs :stobjs state
                  :guard t))
  (b* (((mv ?er time state) (read-acl2-oracle state))
       ((mv ?er bytes state) (read-acl2-oracle state)))
    (mv (if (and (rationalp time)
                 (<= 0 time))
            time
          0)
        (nfix bytes)
        state)))

(local (in-theory (enable oracle-time-extract)))

(defthm type-of-oracle-time-extract.time
  (and (rationalp (mv-nth 0 (oracle-time-extract state)))
       (<= 0 (mv-nth 0 (oracle-time-extract state))))
  :rule-classes :type-prescription)

(defthm natp-of-oracle-time-extract.bytes
  (natp (mv-nth 1 (oracle-time-extract state)))
  :rule-classes :type-prescription)

(defthm state-p1-of-oracle-time-extract.state
  (implies (state-p1 state)
           (state-p1 (mv-nth 2 (oracle-time-extract state)))))

(defttag :oracle-time)
(include-raw "oracle-time-raw.lsp")
(defmacro-last oracle-time-exec)

(defun oracle-time-fn (form ret)
  (b* ((ret
        ;; Normalize :ret form so that it is just a list of names.
        (cond ((symbolp ret)
               (list ret))
              ((and (symbol-listp ret)
                    (eq (car ret) 'mv)
                    (consp (cdr ret)))
               (cdr ret))
              (t
               (er hard? 'oracle-time "Invalid :ret specifier ~x0~%" ret))))

       (return-splice
        ;; Return values from the macro itself, except for time and bytes
        (if (member 'state ret)
            ret
          (append ret '(state))))

       ((when (eql (len ret) 1))
        ;; Single-valued case.
        `(let ((,(car ret) (oracle-time-exec :ignored-arg ,form)))
           (mv-let (time bytes state)
             (oracle-time-extract state)
             (mv time bytes . ,return-splice)))))

    ;; Multiple-valued case.
    `(mv-let ,ret
       (oracle-time-exec :ignored-arg ,form)
       (mv-let (time bytes state)
         (oracle-time-extract state)
         (mv time bytes . ,return-splice)))))

(defmacro oracle-time (form &key (ret 'ret))
  (oracle-time-fn form ret))

