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
(include-book "centaur/quicklisp/bordeaux" :dir :system)
(include-book "std/util/bstar" :dir :system)
(local (include-book "oslib/read-acl2-oracle" :dir :system))
; (depends-on "oracle-timelimit-raw.lsp")


(defxdoc oracle-timelimit
  :parents (oracle-time)
  :short "Carry out some computation, returning (not just printing!) how long
it took and (on supported Lisps) how many bytes were allocated, but aborting
the execution if it takes too long."

  :long "<p>The @('oracle-timelimit') macro is similar to @(see oracle-time)
except that besides reporting times, it also allows you impose a limit on how
long the form is allowed to run for.  If execution takes too long, execution is
aborted.</p>

<p><b>Warning</b>.  This book is intended to be a practically useful tool, but
it may not be entirely sound.  In particular:</p>

<ul>

<li>In case of a timeout, execution will (of course) not complete normally.  If
the computation you are timing includes, for instance, updates to @(see stobj)s
or the @(see state), then the stobjs may have been only partially updated.
This might especially pose a soundness problem for <see topic='@(url
defabsstobj)'>abstract stobjs</see> since the stobj invariant might be ruined
if a sequence of writes is interrupted.</li>

<li>The internal, core, intermediate part of the computation makes use of a
@(see return-last) style macro that will not return the right results when the
computation is timed out.  The top-level @('oracle-timelimit') macro accounts
for this, but in principle a malicious user could directly call the internal
macro to easily cause unsoundness.</li>

</ul>

<h5>Basic Example</h5>

@({
     (oracle-timelimit 1/3 ; Fail if more than 1/3 second is needed
       (fib 35))           ; What to execute
     -->
     (mv seconds           ; NIL on timeout, or time taken (rational)
         bytes             ; NIL on timeout, or bytes allocated (natural)
         ans               ; Answer on success, or NIL on timeout
         state)            ; Adjusted with changes to oracle
})

<h5>Example with Multiple Return Values</h5>

@({
     (oracle-timelimit 5        ; Fail if more than 5 seconds are needed
       (random$ 100 state)      ; What to execute
       :ret    (mv ans state)   ; Return signature of the form to execute
       :onfail (mv :oops state) ; Alternate values to return on timeout
       )
     -->
     (mv seconds           ; NIL on timeout, or time taken (rational)
         bytes             ; NIL on timeout, or bytes allocated (natural)
         ans               ; Answer on success, or :oops on timeout
         state)            ; Adjusted with changes to the oracle
})

<p>See also the file @('[books]/tools/oracle-timelimit-tests.lisp') for some
additional tests and working examples.</p>

<h5>General Form</h5>

@({
     (oracle-timelimit
       limit                ; rational valued time limit
       form                 ; what to execute
       [:ret    retspec]    ; return signature for form
       [:onfail failspec]   ; return values for timeout case

       ;; Special option to catch Lisp errors that arise during form
       [:suppress-lisp-errors bool]
       )
})

<p>The @('limit') should evaluate to a rational number which is interpreted as
some number of seconds.</p>

<p>The @('form') can be any arbitrary ACL2 form that you want to execute.  If
this form returns an ordinary, single value, e.g., as in @('(fib 35)'), then
the @(':ret') form is not needed.  Otherwise, @(':ret') should explain the
return signature of form, as in @(see oracle-time).</p>

<p>The return value of @('oracle-timelimit') extends the return value of
@('form') with multiple values.  The basic idea is that @('oracle-timelimit')
is going to macroexpand to something like the following:</p>

@({
    (mv-let retspec
        form
      (b* (((mv & time state)  (read-acl2-oracle state))
           ((mv & bytes state) (read-acl2-oracle state))
           ((unless time)
            ;; execution timed out
            (mv nil nil failspec [state])))
         ;; Else, execution succeeded
         (mv time bytes retspec [state])))
})

<p>You can see here that the @('retspec') is used to explain how to bind the
results of executing the form.  It is also, essentially, spliced into the
return values for the success and failure cases.  The only twist is that if
@('retspec') mentions @('state'), then we don't add an extra @('state') onto
the end of the form.</p>

<p>By default, if @('form') causes a raw Lisp error such as a type error, stack
overflow, or causes some other non-local exit such as throwing to a tag, the
error will propagate through the @('oracle-timelimit') call.  However, if you
set @(':suppress-lisp-errors t'), then any such error will be treated as a
timeout.  This may have any number of unsound consequences!</p>")


(defund oracle-timelimit-extract (state)
  "Has an under-the-hood definition."
  (declare (xargs :stobjs state :guard t))
  (b* (((mv ?er time state) (read-acl2-oracle state))
       ((mv ?er bytes state) (read-acl2-oracle state))
       ((unless time)
        ;; Logical fiction for the timeout case.
        (mv nil nil state)))
    ;; Logical fiction for the success case.
    (mv (if (and (rationalp time)
                 (<= 0 time))
            time
          0)
        (nfix bytes)
        state)))

(local (in-theory (enable oracle-timelimit-extract)))

(defthm type-of-oracle-timelimit-extract.time
  (or (and (rationalp (mv-nth 0 (oracle-timelimit-extract state)))
           (<= 0 (mv-nth 0 (oracle-timelimit-extract state))))
      (not (mv-nth 0 (oracle-timelimit-extract state))))
  :rule-classes :type-prescription)

(defthm rationalp-of-oracle-timelimit-extract.time
  (iff (rationalp (mv-nth 0 (oracle-timelimit-extract state)))
       (mv-nth 0 (oracle-timelimit-extract state))))

(defthm lower-bound-of-oracle-timelimit-extract.time
  (<= 0 (mv-nth 0 (oracle-timelimit-extract state)))
  :rule-classes :linear)

(defthm type-of-oracle-timelimit-extract.bytes
  (or (natp (mv-nth 1 (oracle-timelimit-extract state)))
      (not (mv-nth 1 (oracle-timelimit-extract state))))
  :rule-classes :type-prescription)

(defthm lower-bound-of-oracle-timelimit-extract.bytes
  (<= 0 (mv-nth 1 (oracle-timelimit-extract state)))
  :rule-classes :linear)

(defthm state-p1-of-oracle-timelimit-extract.state
  (implies (state-p1 state)
           (state-p1 (mv-nth 2 (oracle-timelimit-extract state)))))

(defttag :oracle-timelimit)
(include-raw "oracle-timelimit-raw.lsp")
(defmacro-last oracle-timelimit-exec)



(defun oracle-timelimit-fn (limit form ret fail suppress-lisp-errors)
  (b* (((mv ret-list fail-vals)
        ;; Normalize :ret and :fail forms so they are always lists of
        ;; corresponding name/values
        (cond ((symbolp ret)
               (mv (list ret)
                   (list fail)))
              ((and (symbol-listp ret)
                    (eq (car ret) 'mv)
                    (consp fail)
                    (eq (car fail) 'mv)
                    (equal (len ret) (len fail)))
               (mv (cdr ret)
                   (cdr fail)))
              (t
               (mv (er hard? 'oracle-timelimit
                       "Incompatible ret/fail forms:~%  ~
                         - ret: ~x0~%  ~
                         - fail: ~x1~%"
                       ret fail)
                   nil))))

       ((mv success-splice fail-splice)
        ;; Return values for the success/failure cases, except for the
        ;; time/bytes return values.
        (if (member 'state ret-list)
            (mv ret-list fail-vals)
          (mv (append ret-list '(state))
              (append fail-vals '(state)))))

       ((when (eql (len ret-list) 1))
        ;; Single-valued case.
        `(let ((,(car ret-list) (oracle-timelimit-exec (list ,limit 1 ,suppress-lisp-errors) ,form)))
           (mv-let (time bytes state)
             (oracle-timelimit-extract state)
             (if time
                 (mv time bytes . ,success-splice)
               (mv nil nil . ,fail-splice))))))

    ;; Multiple-valued case.
    `(mv-let ,ret-list
       (oracle-timelimit-exec (list ,limit ,(len ret-list) ,suppress-lisp-errors) ,form)
       (mv-let (time bytes state)
         (oracle-timelimit-extract state)
         (if time
             (mv time bytes . ,success-splice)
           (mv nil nil . ,fail-splice))))))

(defmacro oracle-timelimit (limit form &key (ret 'ret) (onfail 'nil) (suppress-lisp-errors 'nil))
  (oracle-timelimit-fn limit form ret onfail suppress-lisp-errors))
