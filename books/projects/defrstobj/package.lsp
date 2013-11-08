; Record Like Stobjs
; Copyright (C) 2011-2012 Centaur Technology
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

(defpkg "RSTOBJ"
  (union-eq *acl2-exports*
            *common-lisp-symbols-from-main-lisp-package*
            ;; things missing from acl2 exports
            '(unsigned-byte-p signed-byte-p extend-pathname defstobj-template
                              translate-declaration-to-guard keyword-value-listp
                              partition-rest-and-keyword-args assoc-keyword
                              remove-keyword alist-to-keyword-alist *defstobj-keywords*
                              update-nth-array)
            ;; single-letter variables for better theorem compatibility with
            ;; acl2 package, and for g/s.
            '(a b c d e f g h i j k l m n o p q r s u v w x y z)
            ;; things we're importing from acl2 libraries
            '(<< equal-by-nths equal-by-nths-lhs equal-by-nths-rhs equal-by-nths-hyp
                 defsection definline b*)
            ;; things from from type-spec-fns
            '(atom-fix bitp bit-fix bit-listp character-fix cons-fix nat-listp
                       string-fix symbol-fix signed-byte-fix signed-byte-listp
                       unsigned-byte-fix unsigned-byte-listp)
            ;; things we want to "export" into the ACL2 package
            '(defrstobj def-typed-record)))