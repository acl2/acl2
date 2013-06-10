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
(include-book "../mlib/modnamespace")
(include-book "../mlib/writer")
(include-book "../util/cwtime")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))

; This is pretty lousy collection code, especially since we repeatedly
; string-downcase all of the strings.  OTOH, it performs well enough, so
; whatever.

(defsection vl-collect-ieqv-strings

  (defund vl-collect-ieqv-strings-aux (a x)
    ;; Assumes A is already lowercase.
    ;; O(n) in the length of X
    (declare (xargs :guard (and (stringp a)
                                (string-listp x))))
    (cond ((atom x)
           nil)
          ((equal a (str::downcase-string (car x)))
           (cons (car x)
                 (vl-collect-ieqv-strings-aux a (cdr x))))
          (t
           (vl-collect-ieqv-strings-aux a (cdr x)))))

  (defund vl-collect-ieqv-strings (a x)
    ;; Returns all strings in X that are case-equivalent to A.
    ;; O(n) in the length of X
    (declare (xargs :guard (and (stringp a)
                                (string-listp x))))
    (vl-collect-ieqv-strings-aux (str::downcase-string a) x))

  (local (in-theory (enable vl-collect-ieqv-strings-aux
                            vl-collect-ieqv-strings)))

  (defthm string-listp-of-vl-collect-ieqv-strings-aux
    (implies (force (string-listp x))
             (string-listp (vl-collect-ieqv-strings-aux a x))))

  (defthm string-listp-of-vl-collect-ieqv-strings
    (implies (force (string-listp x))
             (string-listp (vl-collect-ieqv-strings a x)))))



(defsection vl-find-case-equivalent-strings

  (defund vl-find-case-equivalent-strings-aux (x y)
    ;; O(n^2) in the length of X, but X should be the list of duplicated strings,
    ;; so there shouldn't be many.
    (declare (xargs :guard (and (string-listp x)
                                (string-listp y))))
    (if (atom x)
        nil
      (cons (vl-collect-ieqv-strings (car x) y)
            (vl-find-case-equivalent-strings-aux (cdr x) y))))

  (defund vl-find-case-equivalent-strings (x)
    ;; Returns a string list list, where each sub-list is a set of
    ;; case-equivalent strings within X.
    (declare (xargs :guard (string-listp x)))
    (b* ((xl    (cwtime (str::downcase-string-list x) :mintime 1/2))                  ;; O(n) in |X|
         (dupes (cwtime (duplicated-members xl) :mintime 1/2))                        ;; O(n log n) in |X|
         (sets  (cwtime (vl-find-case-equivalent-strings-aux dupes x) :mintime 1/2))) ;; O(n^2) in |dupes|
      sets))

  (local (in-theory (enable vl-find-case-equivalent-strings-aux
                            vl-find-case-equivalent-strings)))

  (defthm string-list-listp-of-vl-find-case-equivalent-strings-aux
    (implies (force (string-listp y))
             (string-list-listp (vl-find-case-equivalent-strings-aux x y))))

  (defthm string-list-listp-of-vl-find-case-equivalent-strings
    (implies (force (string-listp x))
             (string-list-listp (vl-find-case-equivalent-strings x))))

  (local (assert! (equal (vl-find-case-equivalent-strings
                          (list "foo" "BAR" "baz" "Foo" "Bar"))
                         '(("BAR" "Bar") ("foo" "Foo"))))))



(define vl-equiv-strings-to-lines ((x string-list-listp) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq
     (vl-basic-cw "      - ~&0~%" (car x))
     (vl-equiv-strings-to-lines (cdr x)))))

(defsection vl-module-check-case

  (defund vl-module-check-case (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((vl-module x) x)
         ;; The sort here eliminates repetitions of the same name.
         (names       (cwtime (mergesort
                               (vl-portdecllist->names-exec x.portdecls
                                                            (vl-module->modnamespace-exec x)))
                              :name check-case-gather-names
                              :mintime 1/2))
         (equiv-names (cwtime (vl-find-case-equivalent-strings names)
                              :name check-case-find-equiv-strs
                              :mintime 1/2))
         ((unless equiv-names)
          x)
         (w (make-vl-warning
             :type :vl-warn-case-sensitive-names
             :msg "In ~a0, found names that differ only by case.  This might ~
                   indicate a typo, and otherwise it might cause problems ~
                   for some Verilog tools.  Details: ~%~s1"
             :args (list x.name (with-local-ps (vl-equiv-strings-to-lines equiv-names)))
             :fatalp nil
             :fn 'vl-module-check-case)))
      (change-vl-module x :warnings (cons w x.warnings))))

  (local (in-theory (enable vl-module-check-case)))

  (defthm vl-module-p-of-vl-module-check-case
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-check-case x))))

  (defthm vl-module->name-of-vl-module-check-case
    (equal (vl-module->name (vl-module-check-case x))
           (vl-module->name x))))

(defsection vl-modulelist-check-case

  (defprojection vl-modulelist-check-case (x)
    (vl-module-check-case x)
    :guard (vl-modulelist-p x)
    :result-type vl-modulelist-p)

  (local (in-theory (enable vl-modulelist-check-case)))

  (defthm vl-modulelist->names-of-vl-modulelist-check-case
    (equal (vl-modulelist->names (vl-modulelist-check-case x))
           (vl-modulelist->names x))))


