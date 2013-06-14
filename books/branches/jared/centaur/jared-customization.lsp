; Jared's ACL2 Customization File
; Copyright (C) 2009-2013 Centaur Technology
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



; These are my preferred settings for using ACL2.  I've put them into into this
; centaur/jared-customization.lsp file, instead of leaving them in my home
; directory, to make it easy to keep my settings shared across any machines
; that I want to use (e.g., at work and at home).
;
; If you decide you want to use this, the easiest option is to just add an
; acl2-customization.lsp file to your home directory that says:
;
;   (ld "centaur/jared-customization.lsp" :dir :system)
;
; You can, of course, put whatever additional customization you want in your
; own customization file, then.



; There's no in-package here, because it could screw up packages loaded by
; custom acl2-customization.lsp files.  Instead we use the #!ACL2 syntax to try
; to make sure this file can be read from any package.

#!ACL2
(set-deferred-ttag-notes t state)

#!ACL2
(set-gag-mode :goals)

#!ACL2
(set-splitter-output t)

#!ACL2
(set-inhibit-output-lst '(proof-tree))

#!ACL2
(assign checkpoint-processors
        ;; Some users may not like this setting.  I usually like destructor
        ;; elimination pretty well, so adjust checkpoint printing so that
        ;; checkpoints are shown AFTER destructor elimination, instead of
        ;; before it.
        (remove 'eliminate-destructors-clause
                (@ checkpoint-processors)))


#!ACL2
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

#!ACL2
(defmacro why (rule)
  ;; A handy macro that lets you figure out why a rule isn't firing.
  ;; This is useful to me because I can never remember the :monitor
  ;; syntax.
  `(er-progn
    (brr t)
    (monitor '(:rewrite ,rule) ''(:eval :go t))))

#!ACL2
(defmacro with-redef (&rest forms)
  ;; A handy macro you can use to temporarily enable redefinition, but then
  ;; keep it disabled for the rest of the session
  `(progn
     (defttag with-redef)
     (progn!
      (set-ld-redefinition-action '(:doit . :overwrite) state)
      (progn . ,forms)
      (set-ld-redefinition-action nil state))))



; Untranslate support to convert cadaddrpillars into more readable nests of
; FIRST, SECOND, THIRD, FOURTH, etc.

#!ACL2
(include-book "misc/untranslate-patterns" :dir :system)

#!ACL2
(progn

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

  (optimize-untranslate-patterns))



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
(ld "xdoc/package.lsp" :dir :system)

#!ACL2
(make-event
 (if (not (boundp-global :suppress-preload-xdoc state))
     `(progn
        (include-book "xdoc/top" :dir :system)
        (xdoc::colon-xdoc-init))
   `(value-triple nil)))

