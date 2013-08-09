; SATLINK - Link from ACL2 to SAT Solvers
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "cutil/portcullis" :dir :system)
(ld "tools/flag-package.lsp" :dir :system)
(include-book "oslib/portcullis" :dir :system)

(defpkg "SATLINK"
  (union-eq *acl2-exports*
            *common-lisp-symbols-from-main-lisp-package*
            cutil::*cutil-exports*
            '(b*
              bitp
              lnfix
              lbfix
              bfix
              b-not
              b-and
              b-ior
              b-xor
              b-eqv
              defxdoc
              defsection
              defstobj-clone
              list-fix
              list-equiv
              set-equiv
              nat-equiv
              bit-equiv
              bits-equiv
              rev
              duplicity
              alist-keys
              alist-vals
              hons-remove-duplicates
              set-reasoning
              enable*
              disable*
              e/d*
              bitarr get-bit set-bit bits-length resize-bits bits-equiv
              natarr get-nat set-nat nats-length resize-nats nats-equiv
              tshell-call tshell-start tshell-stop tshell-ensure
              satlink boolean-reasoning
              )))

