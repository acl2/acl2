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
(include-book "xdoc/save" :dir :system)
(set-state-ok t)
(program)

(defun json-xdoc-topic (name state)
  (b* (((mv topics state)    (xdoc::all-xdoc-topics state))
       (topics-fal           (xdoc::topics-fal topics))
       (topic                (cdr (hons-get name topics-fal)))
       ((unless topic)
        (mv (bridge::json-encode
             (list (cons :error (str::cat "No xdoc for topic " (symbol-name name)))))
            state))
       ((mv short-str state) (xdoc::short-xml-for-topic topic topics-fal state))
       ((mv long-str  state) (xdoc::long-xml-for-topic  topic topics-fal state)))
    (mv (bridge::json-encode
         (list (cons :error nil)
               (cons :short short-str)
               (cons :long long-str)))
        state)))


