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
(include-book "centaur/quicklisp/bordeaux" :dir :system)
(defttag :sidekick)

; web commands -- the browser portion polls for the current "web commands" and
; can respond to them by taking actions, e.g., the :show command is implemented
; this way.

; The user's commands are pushed into a thread-safe stack.  The server can
; fetch this stack and decide what to do with it.  The fetching function is
; only available in raw Lisp because it wouldn't be sound to expose it to the
; logic.

(defun push-webcommand (x)
  ;; X can be any ACL2 object.  Normally it is something with a nice JSON
  ;; encoding.
  (declare (xargs :guard t)
           (ignorable x))
  (er hard? 'push-webcommand "Under the hood definition not yet installed."))

(defmacro show (name)
  (cond ((symbolp name)
         (push-webcommand (list (cons :action :show)
                                (cons :name (xdoc::full-escape-symbol name)))))
        ((and (quotep name)
              (symbolp (second name)))
         (push-webcommand (list (cons :action :show)
                                (cons :name (xdoc::full-escape-symbol (second name))))))
        (t
         (er hard? 'show "Expected a symbol, not ~x0." name))))

; (depends-on "webcommand-raw.lsp")
(include-raw "webcommand-raw.lsp")
