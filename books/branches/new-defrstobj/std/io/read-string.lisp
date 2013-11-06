; Standard IO Library
; read-string.lisp
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

(in-package "ACL2")
(include-book "std/util/define" :dir :system)
(include-book "tools/include-raw" :dir :system)
(local (include-book "oslib/read-acl2-oracle" :dir :system))

(define read-string
  :parents (std/io)
  :short "Parse a string into s-expressions, by using Common Lisp's @('read')
under the hood. (requires a ttag)"
  ((str stringp "The string to parse.")
   &key
   (state 'state))
  :returns (mv (errmsg  "An error @(see msg) on failure, e.g., parse errors;
                         or @('nil') on success.")
               (objects "The list of objects parsed from @('str').")
               (state   state-p1 :hyp (state-p1 state)))

  :long "<p>In the logic we just read the oracle to decide if parsing will
succeed or fail.  So you can never prove any relationship between the input
@('str') and the resulting s-expressions that you get out.</p>

<p>In the execution, we turn the string into a Common Lisp input stream and try
to parse it using @('read'), so that full Common Lisp syntax is permitted.  If
we are able to successfully parse objects until EOF is reached, we return
success and the list of objects we read.</p>

<p>Jared thinks this may be sound.  See read-string-tests.lisp for some obvious
attempts to cause unsoundness.</p>"

  (declare (ignorable str))
  (b* ((- (raise "Raw lisp definition not installed?"))
       ((mv err1 errmsg? state) (read-acl2-oracle state))
       ((mv err2 objects state) (read-acl2-oracle state))
       ((when (or err1 err2))
        (mv (msg "Reading oracle failed.") nil state))
       ((when errmsg?)
        (mv errmsg? nil state)))
    (mv nil objects state)))

(defttag :read-string)

; (depends-on "read-string-raw.lsp")
(include-raw "read-string-raw.lsp")
