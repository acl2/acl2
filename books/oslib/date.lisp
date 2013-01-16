; OSLIB -- Operating System Utilities
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "OSLIB")
(include-book "read-acl2-oracle")
(include-book "cutil/define" :dir :system)
(include-book "tools/include-raw" :dir :system)
(include-book "str/cat" :dir :system)
(include-book "str/natstr" :dir :system)
; (depends-on "date-raw.lsp")

(define date (state)
  :returns (mv (datestamp stringp :rule-classes :type-prescription)
               (state state-p1 :hyp (force (state-p1 state))))
  :parents (oslib)
  :short "Get the current datestamp, like \"November 17, 2010 10:25:33\"."

  :long "<p>In the logic this function reads from the ACL2 oracle.  In the
execution we use Common Lisp's @('get-decoded-time') function to figure out
what the current date and time is.  We think this <i>should</i> work on any
Common Lisp system.</p>"

  (b* ((- (er hard? __function__ "Raw Lisp definition not installed?"))
       ((mv err val state) (read-acl2-oracle state)))
    (if (and (not err)
             (stringp val))
        (mv val state)
      (mv "Error reading date." state))))

(defttag oslib)
(include-raw "date-raw.lsp")
