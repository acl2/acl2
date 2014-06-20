; ACL2 Sidekick
; Copyright (C) 2014 Kookamara LLC
;
; Contact:
;   Kookamara LLC
;   11410 Windermere Meadows, Austin TX, 78759, USA.
;   http://www.kookamara.com/
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
    (mv (list (cons :rule name)
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
       (ans (bridge::json-encode summary)))
    (mv ans state)))
