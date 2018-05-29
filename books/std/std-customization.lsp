; ACL2 Customization File for The Standard Approach to Using ACL2
; Copyright (C) 2009-2013 Centaur Technology
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
; Contributing author: David Rager <ragerdl@defthm.com>



; The easiest way to use this file is to just add an acl2-customization.lsp
; file to your home directory that says:
;
;   (ld "std/std-customization.lsp" :dir :system)
;
; You can, of course, put whatever additional customization you want in your
; own customization file, then.


; There's no in-package here, because it could screw up packages loaded by
; custom acl2-customization.lsp files.  Instead we use the #!ACL2 syntax to try
; to make sure this file can be read from any package.

; This file is mentioned in books/doc/practices.lisp.

#!ACL2
(set-deferred-ttag-notes t state)

#!ACL2
(set-inhibit-output-lst '(proof-tree))


#!ACL2
(with-output
  :off (summary event)
  (progn
    (defmacro d (name)
      ;; A handy macro that lets you write :d fn to disassemble a function.  I
      ;; mostly have this because my fingers always type ":diassemble$" instead of
      ;; ":disassemble$"
      (cond ((symbolp name)
             `(disassemble$ ',name :recompile nil))
            ((and (quotep name)
                  (symbolp (unquote name)))
             `(disassemble$ ',(unquote name) :recompile nil))
            ((and (quotep name)
                  (quotep (unquote name))
                  (symbolp (unquote (unquote name))))
             `(disassemble$ ',(unquote (unquote name)) :recompile nil))
            (t
             (er hard? 'd "Not a symbol or quoted symbol: ~x0~%" name))))

    (defmacro why (rule)
      ;; A handy macro that lets you figure out why a rule isn't firing.
      ;; This is useful to me because I can never remember the :monitor
      ;; syntax.
      `(er-progn
        (brr t)
        (monitor ',rule ''(:eval :go t))))

    (defun explain-fn (state)
      (declare (xargs :stobjs (state)
                      :mode :program))

; When the break-rewrite command :eval is called and the rule that has
; been broken on fails to be applied, ACL2 prints some information
; describing why the rule failed; this is mainly handled by the system
; function TILDE-@-FAILURE-REASON-PHRASE1.

; The current function is intended to supplement those messages, and
; is to be called after :eval.  It provides the following supplemental
; information:

; - If the rule failed because a hypothesis couldn't be relieved, we
;   create and print a clause showing what would need to be proved in
;   order for the hypothesis to be relieved.

; The above is the only extra information currently implemented; feel
; free to add more.

; There's no need to do :OK-IF (BRR@ :WONP) before calling this
; function, since it exits early if failure-reason is nil, which must
; be the case if (BRR@ :WONP) were T.  (NOTE: please maintain this
; property if you edit this function.)

      (let ((failure-reason (get-brr-local 'failure-reason state)))
        (cond
         ((and (consp failure-reason)
               (consp (cdr failure-reason))
               (eq (cadr failure-reason) 'rewrote-to))
          (mv-let (clause ttree)
            (clausify-type-alist (get-brr-local 'type-alist state)
                                 (list (cddr failure-reason))
                                 (ens state) (w state) nil nil)
            (declare (ignore ttree))
            (progn$
             (cw "Printing target with hyps derived from type-alist~%")
             (value (prettyify-clause clause nil (w state))))))
         (t (value :invisible)))))

    (defmacro explain ()
      `(explain-fn state))

    (defmacro why-explain (rule)
      `(er-progn
        (brr t)
        (monitor ',rule ''(:eval (explain)))))

    (defmacro with-redef (&rest forms)
      ;; A handy macro you can use to temporarily enable redefinition, but then
      ;; keep it disabled for the rest of the session
      `(progn
         (defttag with-redef)
         (progn!
          (set-ld-redefinition-action '(:doit . :overwrite) state)
          (progn . ,forms)
          (set-ld-redefinition-action nil state))))))



; XDOC SUPPORT
;
;   - Always load the xdoc package, which is pretty fast.
;
;   - Unless :SUPPRESS-PRELOAD-XDOC has been assigned, also get the xdoc
;     database preloaded so that :XDOC commands are very fast and never
;     leave any nonsense in your history.
;
; The second part is somewhat slow and makes ACL2 take noticeably longer to
; boot up.  However, for me, on the par, it seems worth it to make :xdoc much
; more useful.
;
; The suppress-preload-xdoc mechanism can be used to make sure that xdoc does
; NOT get preloaded.  Why would you want to do this?
;
; Well, a few libraries (e.g., str) have some files (package definitions,
; str::cat, etc.) that are included in the xdoc implementation code that gets
; loaded by (xdoc::colon-xdoc-init).  When you're hacking on these libraries,
; it's very easy to, e.g., change something that causes xdoc to be completely
; unloadable until you recertify everything.
;
; At any rate, if for this (or some other reason) you don't want to
; automatically do this xdoc initialization, you can just add:
;
;   (assign :suppress-preload-xdoc t)
;
; Before loading std-customization.lsp.

#!ACL2
(with-output
  :off (summary event)
  (ld "std/package.lsp" :dir :system))

#!ACL2
(make-event
 (if (not (boundp-global :suppress-preload-xdoc state))
     `(progn
        (include-book "xdoc/top" :dir :system)
        (include-book "xdoc/debug" :dir :system)
        (xdoc::colon-xdoc-init))
   `(value-triple nil)))


; maybe actually report correct times
(assign get-internal-time-as-realtime t)
