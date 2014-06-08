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

; (depends-on "lock-raw.lsp")
(include-raw "lock-raw.lsp")

(defsection with-sidekick-lock
  :parents (sidekick)
  :short "Special macro that should be used to ensure thread-safety when
accessing the sidekick's state."

  :long "<p>This should generally be used any time you are accessing the
sidekick's state with @(see sget-raw) and @(see sset-raw).</p>

  @(def with-sidekick-lock)
  @(def with-sidekick-lock-aux)"

  (defmacro-last with-sidekick-lock-aux)

  (defmacro with-sidekick-lock (form)
    `(with-sidekick-lock-aux nil ,form)))
