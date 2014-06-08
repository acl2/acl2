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
(include-book "session")
(include-book "disassemble")
(set-state-ok t)
(program)

(define props-jalist-aux (alist (config str::printconfig-p))
  (b* (((when (atom alist))
        nil)
       ((cons key val) (car alist)))
    (cons (cons key (str::pretty val :config config))
          (props-jalist-aux (cdr alist) config))))

(define props-jalist (name state)
  (b* (((unless (symbolp name))
        nil)
       (world  (w state))
       (alist  (getprops name 'acl2::current-acl2-world world))
       (pkg    (current-package state))
       (config (str::make-printconfig :home-package (pkg-witness pkg)
                                      :print-lowercase t
                                      :hard-right-margin 60
                                      ))
       (pretty-printed-alist (props-jalist-aux alist config)))
    pretty-printed-alist))

