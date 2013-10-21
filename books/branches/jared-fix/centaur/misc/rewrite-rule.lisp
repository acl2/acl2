; Dumb Rewriter
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
(include-book "cutil/define" :dir :system)

;; Accessors for rewrite rules, since otherwise the proof obligations become
;; giant cadaddrpillars.

(define rewrite-rule->rune ((rule weak-rewrite-rule-p))
  :inline t
  (access rewrite-rule rule :rune))

(define rewrite-rule->hyps ((rule weak-rewrite-rule-p))
  :inline t
  (access rewrite-rule rule :hyps))

(define rewrite-rule->lhs ((rule weak-rewrite-rule-p))
  :inline t
  (access rewrite-rule rule :lhs))

(define rewrite-rule->rhs ((rule weak-rewrite-rule-p))
  :inline t
  (access rewrite-rule rule :rhs))

(define rewrite-rule->equiv ((rule weak-rewrite-rule-p))
  :inline t
  (access rewrite-rule rule :equiv))

(define rewrite-rule->subclass ((rule weak-rewrite-rule-p))
  :inline t
  (access rewrite-rule rule :subclass))

(define rewrite-rule->heuristic-info ((rule weak-rewrite-rule-p))
  :inline t
  (access rewrite-rule rule :heuristic-info))


(define drw-get-rules ((fn symbolp)
                       (world plist-worldp))
  :returns rules
  (fgetprop fn 'lemmas nil world))
