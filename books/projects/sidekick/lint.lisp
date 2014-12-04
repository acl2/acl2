; ACL2 Sidekick
; Copyright (C) 2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "SIDEKICK")
(include-book "webcommand")
(include-book "tools/lint" :dir :system)
(include-book "std/strings/pretty-program" :dir :system)
(include-book "centaur/bridge/to-json" :dir :system)
(set-state-ok t)
(program)

(defmacro lint ()
  (push-webcommand (list (cons :action :lint))))

(define json-summarize-rule (rule printconfig state)
  (b* (((acl2::rewrite-rule rule) rule)
       (concl (list rule.equiv rule.lhs rule.rhs))
       (body  (cond ((<= 2 (len rule.hyps))
                     `(implies (and . ,rule.hyps) ,concl))
                    ((consp rule.hyps)
                     `(implies ,(car rule.hyps) ,concl))
                    (t
                     concl)))
       (body-str (str::pretty body :config printconfig))
       (name (second rule.rune))
       ((mv er origin state) (acl2::origin-fn name state))
       (origin (if er :error origin)))
    (mv (list (cons :rule (cat (symbol-package-name name) "::" (symbol-name name)))
              (cons :origin origin)
              (cons :body body-str))
        state)))

(define json-summarize-redundancy (x printconfig state)
  ;; See tools/lint.lisp, this is styled after summarize-redundancy
  (b* (((unless (eq (car x) :redundant))
        (mv (raise "Expected (:redundant rule rule), found ~x0" x) state))
       ((mv rule1 state) (json-summarize-rule (second x) printconfig state))
       ((mv rule2 state) (json-summarize-rule (third x) printconfig state)))
    (mv (list (cons :type :redundant)
              (cons :rule1 rule1)
              (cons :rule2 rule2))
        state)))

(define json-summarize-redundancies (x printconfig state)
  (b* (((when (atom x))
        (mv nil state))
       ((mv car state) (json-summarize-redundancy (car x) printconfig state))
       ((mv cdr state) (json-summarize-redundancies (cdr x) printconfig state)))
    (mv (cons car cdr) state)))

(define json-lint (state)
  (b* ((rules        (acl2::get-enabled-rewrite-rules state))
       (redundancies (acl2::find-redundancies-top rules))
       (printconfig  (str::make-printconfig :home-package (pkg-witness (current-package state))
                                            :print-lowercase t
                                            ;; bozo probably smaller right-margin
                                            ))
       ((mv summary state) (json-summarize-redundancies redundancies printconfig state))
       (alist (list (cons :error nil)
                    (cons :redundant summary)
                    ;; Some day maybe other kinds of warnings
                    ))
       (ans (bridge::json-encode alist)))
    (mv ans state)))
