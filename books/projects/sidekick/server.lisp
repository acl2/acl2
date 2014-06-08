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
(include-book "session")
(include-book "disassemble")
(include-book "std/basic/defs" :dir :system)
(include-book "std/strings/defs-program" :dir :system)
(include-book "std/io/read-string" :dir :system)
(defttag :sidekick)
(set-state-ok t)

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

; (depends-on "server-raw.lsp")
(include-raw "server-raw.lsp"
             :host-readtable t)
