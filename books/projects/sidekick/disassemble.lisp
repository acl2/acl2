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
(include-book "tools/bstar" :dir :system)
(include-book "tools/include-raw" :dir :system)
(defttag :sidekick)
(set-state-ok t)

; (depends-on "disassemble-raw.lsp")

(defun disassemble-to-string (fn state)
  (declare (xargs :guard (symbolp fn)
                  :stobjs state)
           (ignorable fn))
  (b* ((- (er hard? 'disassemble-to-string "Raw Lisp definition not installed?"))
       ((mv err val state) (read-acl2-oracle state))
       ((when (or err
                  (not (stringp val))))
        (mv "" state)))
    (mv val state)))

(include-raw "disassemble-raw.lsp")
