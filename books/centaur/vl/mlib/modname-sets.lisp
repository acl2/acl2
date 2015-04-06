; VL Verilog Toolkit
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

(in-package "VL")
(include-book "../parsetree")
(local (include-book "../util/osets"))
(local (include-book "../util/arithmetic"))

; We find it useful to exploit the fact that the name of each module comes
; first in its record.  Because of this, and because of the lexicographic style
; of the total order, we are able to prove some useful properties below.  These
; allow us to avoid sorting in certain cases.

;; Stupid speed hint
(local (in-theory (disable VL-ATTS-P-OF-CDR-WHEN-VL-ATTS-P
                           SUBSETP-EQUAL-WHEN-FIRST-TWO-SAME-YADA-YADA
                           ACL2::CONSP-OF-CAR-WHEN-ALISTP
                           ;; ALISTP-WHEN-VL-ATTS-P-REWRITE
                           ;; VL-ATTS-P-WHEN-SUBSETP-EQUAL
                           acl2::CONSP-OF-CAR-WHEN-CONS-LISTP
                           CONSP-OF-CAR-WHEN-VL-COMMENTMAP-P
                           CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P
                           ;; CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P
                           ACL2::CONSP-UNDER-IFF-WHEN-TRUE-LISTP
                           default-car
                           default-cdr
                           (:rules-of-class :type-prescription :here)
                           (:e tau-system)
                           )))

(defthmd <<-of-cons
  (equal (<< (cons a b) x)
         (if (not (consp x))
             nil
           (or (<< a (car x))
               (and (equal a (car x))
                    (<< b (cdr x))))))
  :hints(("Goal" :in-theory (enable << acl2::lexorder))))

(encapsulate
  ()
  (local (defthm <<-when-consp-left
           (implies (consp x)
                    (equal (<< x y)
                           (if (atom y)
                               nil
                             (or (<< (car x) (car y))
                                 (and (equal (car x) (car y))
                                      (<< (cdr x) (cdr y)))))))
           :hints(("Goal" :in-theory (enable << acl2::lexorder)))))

  (defthmd <<-of-modules
    (implies (and (vl-module-p x)
                  (vl-module-p y)
                  (not (equal (vl-module->name x)
                              (vl-module->name y))))
             (equal (<< x y)
                    (<< (vl-module->name x)
                        (vl-module->name y))))
    :hints(("Goal" :in-theory (e/d (vl-module-p
                                    vl-module->name))))))

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
