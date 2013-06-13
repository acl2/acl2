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
(include-book "defs")
(local (include-book "arithmetic"))

(deflist character-list-listp (x)
  (character-listp x)
  :elementp-of-nil t
  :parents (utilities))

(defthm character-listp-of-flatten
  (implies (character-list-listp x)
           (character-listp (flatten x)))
  :hints(("Goal" :in-theory (enable flatten))))


(defsection vl-character-list-list-values-p
  :parents (utilities)
  :short "Recognizer for alists whose values are strings."

;; BOZO switch to defalist

  (defund vl-character-list-list-values-p (x)
    (declare (xargs :guard t))
    (if (consp x)
        (and (consp (car x))
             (character-list-listp (cdar x))
             (vl-character-list-list-values-p (cdr x)))
      (not x)))

  (local (in-theory (enable vl-character-list-list-values-p)))

  (defthm vl-character-list-list-values-p-when-not-consp
    (implies (not (consp x))
             (equal (vl-character-list-list-values-p x)
                    (not x))))

  (defthm vl-character-list-list-values-p-of-cons
    (equal (vl-character-list-list-values-p (cons a x))
           (and (consp a)
                (character-list-listp (cdr a))
                (vl-character-list-list-values-p x))))

  (defthm vl-character-list-list-values-p-of-hons-shrink-alist
    (implies (and (vl-character-list-list-values-p x)
                  (vl-character-list-list-values-p ans))
             (vl-character-list-list-values-p (hons-shrink-alist x ans)))
    :hints(("Goal" :in-theory (e/d (hons-shrink-alist)
                                   ((force))))))

  (defthm character-list-listp-of-cdr-of-hons-assoc-equal-when-vl-character-list-list-values-p
    (implies (vl-character-list-list-values-p x)
             (character-list-listp (cdr (hons-assoc-equal a x))))))



(define explode-list ((x string-listp))
  :parents (utilities)
  :short "Coerce a list of strings into a @(see character-list-listp)."

  (if (atom x)
      nil
    (cons (explode (car x))
          (explode-list (cdr x))))

  :returns (ans character-list-listp)

  ///

  (defthm explode-list-when-atom
    (implies (atom x)
             (equal (explode-list x)
                    nil)))

  (defthm explode-list-of-cons
    (equal (explode-list (cons a x))
           (cons (explode a)
                 (explode-list x)))))


