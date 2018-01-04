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
(include-book "quicklisp/bordeaux" :dir :system)
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

(defmacro home ()
  (push-webcommand (list (cons :action :home))))

; (depends-on "webcommand-raw.lsp")
(include-raw "webcommand-raw.lsp")
