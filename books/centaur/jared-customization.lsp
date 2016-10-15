; Jared's ACL2 Customization File
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



; These are Jared's preferred settings for using ACL2.  He has put them into
; into this centaur/jared-customization.lsp file, instead of leaving them in
; his home directory, to make it easy to keep his settings shared across any
; machines that he wants to use (e.g., at work and at home).
;
; As a user that doesn't equal Jared, you probably want to use
; books/std/std-customization.lsp.  See that file more more instrutions.
;
; If you decide you still want to use this, the easiest option is to just add
; an acl2-customization.lsp file to your home directory that says:
;
;   (ld "centaur/jared-customization.lsp" :dir :system)
;
; You can, of course, put whatever additional customization you want in your
; own customization file, then.



; There's no in-package here, because it could screw up packages loaded by
; custom acl2-customization.lsp files.  Instead we use the #!ACL2 syntax to try
; to make sure this file can be read from any package.

; Rager is leaving it to Jared to decide whether Jared wants to uncomment the
; follownig ld and remove the redundant events, but he hopes that Jared will
; give him the approval to do so.  This would help avoid forking.

; (ld "std/std-customization.lsp" :dir :system)

#!ACL2
(set-gag-mode :goals)

#!ACL2
(set-splitter-output t)

#!ACL2
(set-inhibit-output-lst '(proof-tree))

#!ACL2
(gc-verbose t)

#!ACL2
(assign checkpoint-processors
        ;; Some users may not like this setting.  I usually like destructor
        ;; elimination pretty well, so adjust checkpoint printing so that
        ;; checkpoints are shown AFTER destructor elimination, instead of
        ;; before it.
        (remove 'eliminate-destructors-clause
                (@ checkpoint-processors)))


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
        (monitor '(:rewrite ,rule) ''(:eval :go t))))

    (defmacro all-included-books ()
      ;; Simple macro to list all books that have been included, recursively
      '(strip-cars (global-val 'include-book-alist (w state))))

    (defmacro with-redef (&rest forms)
      ;; A handy macro you can use to temporarily enable redefinition, but then
      ;; keep it disabled for the rest of the session
      `(progn
         (defttag with-redef)
         (progn!
          (set-ld-redefinition-action '(:doit . :overwrite) state)
          (progn . ,forms)
          (set-ld-redefinition-action nil state))))))



; Untranslate support to convert cadaddrpillars into more readable nests of
; FIRST, SECOND, THIRD, FOURTH, etc.

#!ACL2
(with-output
  :off (summary event)
  (progn
    (include-book "misc/untranslate-patterns" :dir :system)
    (add-untranslate-pattern (car ?x)
                             (first ?x))

    (add-untranslate-pattern (cdr ?x)
                             (rest ?x))

    (add-untranslate-pattern (car (car ?x))
                             (first (first ?x)))

    (add-untranslate-pattern (car (cdr ?x))
                             (second ?x))

    (add-untranslate-pattern (car (car (cdr ?x)))
                             (first (second ?x)))

    (add-untranslate-pattern (car (cdr (car (cdr ?x))))
                             (second (second ?x)))

    (add-untranslate-pattern (car (cdr (car ?x)))
                             (second (first ?x)))

    (add-untranslate-pattern (car (cdr (cdr ?x)))
                             (third ?x))

    (add-untranslate-pattern (car (car (cdr (cdr ?x))))
                             (first (third ?x)))

    (add-untranslate-pattern (car (cdr (car (cdr (cdr ?x)))))
                             (second (third ?x)))

    (add-untranslate-pattern (car (cdr (cdr (car (cdr (cdr ?x))))))
                             (second (third ?x)))

    (add-untranslate-pattern (car (cdr (cdr (car (cdr ?x)))))
                             (third (second ?x)))

    (add-untranslate-pattern (car (cdr (cdr (car ?x))))
                             (third (first ?x)))

    (add-untranslate-pattern (car (cdr (cdr (cdr ?x))))
                             (fourth ?x))

    (add-untranslate-pattern (car (car (cdr (cdr (cdr ?x)))))
                             (first (fourth ?x)))

    (add-untranslate-pattern (car (cdr (car (cdr (cdr (cdr ?x))))))
                             (second (fourth ?x)))

    (add-untranslate-pattern (car (cdr (cdr (car (cdr (cdr (cdr ?x)))))))
                             (third (fourth ?x)))

    (add-untranslate-pattern (car (cdr (cdr (cdr (car (cdr (cdr (cdr ?x))))))))
                             (fourth (fourth ?x)))

    (add-untranslate-pattern (car (cdr (cdr (cdr (car (cdr (cdr ?x)))))))
                             (fourth (third ?x)))

    (add-untranslate-pattern (car (cdr (cdr (cdr (car (cdr ?x))))))
                             (fourth (second ?x)))

    (add-untranslate-pattern (car (cdr (cdr (cdr (car ?x)))))
                             (fourth (first ?x)))

    (add-untranslate-pattern (first (cdr ?x))
                             (second ?x))

    (add-untranslate-pattern (first (cdr (cdr ?x)))
                             (third ?x))

    (add-untranslate-pattern (first (cdr (cdr (cdr ?x))))
                             (fourth ?x))

    (optimize-untranslate-patterns)))



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
; Before loading jared-customization.lsp.

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

#!ACL2
(defmacro hostname ()
  `(getenv$ "HOSTNAME" state))


(include-book "tools/prettygoals/top" :dir :system)

;; #!ACL2
;; (defmacro s (&rest args)
;;   ;; Shorter name for sidekick lookup function
;;   `(acl2::show . ,args))


;; (define skip-until-subgoal-fn (prefix id clause)
;;   :mode :program
;;   (b* ((current-goal (acl2::string-for-tilde-@-clause-id-phrase id))
;;        ((when (equal prefix current-goal))
;;         (cw "Target goal: ~x0.~%" clause))
;;        ((when (str::strprefixp prefix current-goal))
;;         nil))
;;     '(:by nil)))

;; (defmacro skip-until-subtoal (prefix)
;;   `(skip-until-subgoal-fn ,prefix id clause))

;; (set-inhibit-output-lst '(acl2::prove acl2::proof-builder acl2::proof-tree))

