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

; (depends-on "server-raw.lsp")
(include-raw "server-raw.lsp"
             :host-readtable t)
