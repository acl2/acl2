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
(include-book "centaur/quicklisp/hunchentoot" :dir :system)
(include-book "centaur/bridge/to-json" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defconsts" :dir :system)
(include-book "oslib/catpath" :dir :system)
(include-book "system/origin" :dir :system)
(include-book "session")
(include-book "disassemble")
(include-book "lookup")
(include-book "xdoc")
(include-book "webcommand")
(include-book "lint")
(include-book "eventdata")
(include-book "centaur/misc/tshell" :dir :system)
(include-book "std/basic/defs" :dir :system)
(include-book "std/strings/defs-program" :dir :system)
(include-book "std/io/read-string" :dir :system)
(defttag :sidekick)
(set-state-ok t)
(program)


(defconsts *sidekick-dir* (cbd))

(define start (&key (port maybe-natp))
  :parents (sidekick)
  :short "Start the ACL2 sidekick web server."
  (declare (ignorable port))
  (raise "Under the hood definition not installed."))

(define stop ()
  :parents (sidekick)
  :short "Stop the ACL2 sidekick web server."
  (raise "Under the hood definition not installed."))

(define format$-fn (str args)
  (declare (ignorable str args))
  (raise "Under the hood definition not installed."))

(defmacro format$ (str &rest args)
  `(format$-fn ,str (list . ,args)))

(defmacro sk-json-error (fmt-str &rest args)
  `(bridge::json-encode
    (list (cons :error (format$ ,fmt-str . ,args)))))

(define sk-get-props ((name stringp) state)
  :returns (mv json-props state)
  (b* (((mv errmsg objs state) (acl2::read-string name))
       ((when errmsg)
        (mv (sk-json-error "Error in props: parsing failed: ~a: ~a" name errmsg)
            state))
       ((unless (and (equal (len objs) 1)
                     (symbolp (car objs))))
        (mv (sk-json-error "Error in props: not a symbol: ~a" name)
            state))
       (props (props-jalist (car objs) state)))
    (mv (bridge::json-encode
         (list (cons :error nil)
               (cons :val props)))
        state)))

(define sk-get-origin ((name stringp) state)
  :returns (mv json-props state)
  (b* (((mv errmsg objs state) (acl2::read-string name))
       ((when errmsg)
        (mv (sk-json-error "Error in origin: parsing failed: ~a: ~a~%" name errmsg)
            state))
       ((unless (and (equal (len objs) 1)
                     (symbolp (car objs))))
        (mv (sk-json-error "Error in origin: not a symbol: ~a~%" name)
            state))
       ((mv ?er val ?state)
        (acl2::origin-fn (car objs) state)))
    (mv (bridge::json-encode (list (cons :error nil)
                                   (cons :val val)))
        state)))

(define sk-get-xdoc ((name stringp) state)
  :returns (mv json-props state)
  (b* (((mv errmsg objs state) (acl2::read-string name))
       ((when errmsg)
        (mv (sk-json-error "Error in origin: parsing failed: ~a: ~a~%" name errmsg)
            state))
       ((unless (and (equal (len objs) 1)
                     (symbolp (car objs))))
        (mv (sk-json-error "Error in origin: not a symbol: ~a~%" name)
            state))
       ((mv out state) (json-xdoc-topic (car objs) state)))
    (mv out state)))

(define sk-get-disassembly ((name stringp) state)
  :returns (mv json-props state)
  (b* (((mv errmsg objs state) (acl2::read-string name))
       ((when errmsg)
        (mv (sk-json-error "Error in disassemble: parsing failed: ~a: ~a~%" name errmsg)
            state))
       ((unless (and (equal (len objs) 1)
                     (symbolp (car objs))))
        (mv (sk-json-error "Error in disassemble: not a symbol: ~a~%" name)
            state))
       ((mv disassembly state) (disassemble-to-string (car objs) state)))
    (mv (bridge::json-encode (list (cons :error nil)
                                   (cons :val disassembly)))
        state)))

(define sk-get-eventdata ((name stringp) state)
  :returns (mv json-eventdata state)
  (b* (((mv errmsg objs state) (acl2::read-string name))
       ((when errmsg)
        (mv (sk-json-error "Error in eventdata: parsing failed: ~a: ~a~%" name errmsg)
            state))
       ((unless (and (equal (len objs) 1)
                     (symbolp (car objs))))
        (mv (sk-json-error "Error in eventdata: not a symbol: ~a~%" name)
            state))
       (data (find-eventdata (car objs) (sidekick-get-all-event-data)))
       (ans  (bridge::json-encode (list (cons :error nil)
                                   (cons :val data)))))
    (mv ans state)))

(define sk-undo-back-through ((num stringp) state)
  :returns (mv json-eventdata state)
  :mode :program
  (b* ((n (str::strval num))
       ((unless n)
        (mv (sk-json-error "Error in sk-undo-back-through: not a number: ~a" num)
            state))
       #+hons
       ((when t)
        (mv (sk-json-error "Sorry, undo doesn't work on ACL2(h) because memoization isn't ~
                            thread safe.")
            state))
       ((mv erp ?val state) (acl2::ubt!-ubu!-fn :ubt n state))
       ((when erp)
        (mv (sk-json-error "ubt!-ubu!-fn returned an error.")
            state))
       (ans (bridge::json-encode (list (cons :error nil)))))
    (mv ans state)))

; (depends-on "server-raw.lsp")
(include-raw "server-raw.lsp"
             :host-readtable t)
