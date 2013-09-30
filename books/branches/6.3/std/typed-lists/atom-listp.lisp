; Standard Typed Lists Library
; Copyright (C) 2008-2013 Centaur Technology
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
(include-book "cutil/deflist" :dir :system)

(defsection std/typed-lists/atom-listp
  :parents (std/typed-lists atom-listp)
  :short "Lemmas about @(see atom-listp) available in the @(see
std/typed-lists) library."
  :long "<p>Most of these are generated automatically with @(see
cutil::deflist).</p>"

  (cutil::deflist atom-listp (x)
    (atom x)
    :true-listp t
    :elementp-of-nil t
    :already-definedp t
    ;; Set :parents to nil to avoid overwriting the built-in ACL2 documentation
    :parents nil)

  ;; These rules are no good because they target ATOM instead of CONSP:
  (in-theory (disable ATOM-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP
                      ATOM-OF-CAR-WHEN-ATOM-LISTP))

  (defthmd consp-when-member-equal-of-atom-listp
    ;; The free variable matching may make this reasonably cheap for some uses,
    ;; but I think it's likely to cause performance problems, so I'll leave it
    ;; disabled by default.
    (implies (and (member-equal a x)
                  (atom-listp x))
             (equal (consp a)
                    nil))
    :rule-classes ((:rewrite :backchain-limit-lst 1)
                   (:rewrite
                    :corollary (implies (and (atom-listp x)
                                             (member-equal a x))
                                        (equal (consp a)
                                               nil))
                    :backchain-limit-lst 1)))

  (defthm consp-of-car-when-atom-listp
    (implies (atom-listp (double-rewrite x))
             (equal (consp (car x))
                    nil))
    ;; I have seen this be expensive, e.g., in centaur/vl/parse-nets,
    ;; so severely limit it.
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm atom-listp-of-remove-equal
    ;; BOZO probably add to deflist
    (implies (atom-listp x)
             (atom-listp (remove-equal a x))))

  (defthm atom-listp-of-make-list-ac
    (equal (atom-listp (make-list-ac n x ac))
           (and (atom-listp ac)
                (or (atom x)
                    (zp n)))))

  (defthm atom-listp-of-rev
    ;; BOZO consider adding to deflist
    (equal (atom-listp (rev x))
           (atom-listp (list-fix x)))
    :hints(("Goal" :induct (len x)))))

