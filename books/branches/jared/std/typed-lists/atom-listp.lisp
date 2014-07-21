; Standard Typed Lists Library
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "std/util/deflist" :dir :system)

(defsection std/typed-lists/atom-listp
  :parents (std/typed-lists atom-listp)
  :short "Lemmas about @(see atom-listp) available in the @(see
std/typed-lists) library."
  :long "<p>Most of these are generated automatically with @(see
std::deflist).</p>"

  (std::deflist atom-listp (x)
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

