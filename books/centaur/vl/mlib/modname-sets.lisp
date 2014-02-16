; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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

(in-package "VL")
(include-book "../parsetree")
(local (include-book "../util/osets"))
(local (include-book "../util/arithmetic"))

; We find it useful to exploit the fact that the name of each module comes
; first in its record.  Because of this, and because of the lexicographic style
; of the total order, we are able to prove some useful properties below.  These
; allow us to avoid sorting in certain cases, and so on.

(defthmd <<-of-cons
  (equal (<< (cons a b) x)
         (if (not (consp x))
             nil
           (or (<< a (car x))
               (and (equal a (car x))
                    (<< b (cdr x))))))
  :hints(("Goal" :in-theory (enable << acl2::lexorder))))

(defthmd <<-of-modules
  (implies (and (vl-module-p x)
                (vl-module-p y)
                (not (equal (vl-module->name x)
                            (vl-module->name y))))
           (equal (<< x y)
                  (<< (vl-module->name x)
                      (vl-module->name y))))
  :hints(("Goal" :in-theory (enable vl-module-p
                                    vl-module->name
                                    <<-of-cons))))

(local (in-theory (enable <<-of-cons <<-of-modules)))

(defthm setp-of-vl-modulelist->names-when-no-duplicates
  (implies (and (no-duplicatesp-equal (vl-modulelist->names x))
                (force (vl-modulelist-p x)))
           (equal (setp (vl-modulelist->names x))
                  (setp (list-fix x))))
   :hints(("Goal"
           :induct (len x)
           :do-not '(generalize fertilize)
           :in-theory (enable no-duplicatesp-equal (:ruleset set::primitive-rules)))))

(local (defthm vl-modulelist->names-of-insert
         (implies (and (not (in (vl-module->name a) (vl-modulelist->names x)))
                       (force (vl-module-p a))
                       (force (vl-modulelist-p x))
                       (force (setp (vl-modulelist->names x)))
                       (force (setp x)))
                  (equal (vl-modulelist->names (insert a x))
                         (insert (vl-module->name a)
                                 (vl-modulelist->names x))))
         :hints(("Goal"
                 :induct (insert a x)
                 :do-not-induct t
                 :do-not '(generalize fertilize)
                 :in-theory (e/d ((:ruleset set::primitive-rules)) ((force)))))))

(defthm vl-modulelist->names-of-mergesort
  (implies (and (case-split (no-duplicatesp-equal (vl-modulelist->names x)))
                (force (vl-modulelist-p x)))
           (equal (vl-modulelist->names (mergesort x))
                  (mergesort (vl-modulelist->names x)))))

(defthm setp-of-vl-modulelist->names-of-mergesort
  (implies (and (case-split (no-duplicatesp-equal (vl-modulelist->names x)))
                (force (vl-modulelist-p x)))
           (setp (vl-modulelist->names (mergesort x)))))
