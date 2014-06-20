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

(in-package "ACL2")
(include-book "std/portcullis" :dir :system)
(include-book "centaur/bridge/portcullis" :dir :system)
(include-book "centaur/vl/portcullis" :dir :system)

(defpkg "SIDEKICK"
  (union-eq-exec
   (union-eq-exec '(include-raw
                    std::def-primitive-aggregate
                    std::defval ;; bozo not in std-exports?
                    bridge::json-encode
                    ;; for integrating documentation
                    sidekick

                    str::cat
                    str::natstr

                    ;; acl2 stuff we want access to
                    ens
                    er-decode-cd
                    access-command-tuple-number
                    make-ldds-command-sequence
                    er-let*
                    access
                    ldd-status

                    ;; other handy functions
                    maybe-natp

                    ;; interactive sidekick commands
                    home
                    show
                    session
                    lint
                    )
                  std::*std-exports*)
   *std-pkg-symbols*))

