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
(include-book "../util/echars")
(local (include-book "../util/arithmetic"))

(defsection vl-defines-p
  :parents (preprocessor)
  :short "Alist for definitions."

  :long "<p>We keep track of the @('`defines') which have been issued using a
simple alist that maps strings to their values.  Each value is an @(see
vl-echarlist-p) of the characters in the definition.</p>

<p>This model is too simple to support macros with arguments, but for now it
is adequate.</p>"

  (defund vl-defines-p (x)
    (declare (xargs :guard t))
    (if (atom x)
        (eq x nil)
      (and (consp (car x))
           (stringp (caar x))
           (vl-echarlist-p (cdar x))
           (vl-defines-p (cdr x)))))

  (local (in-theory (enable vl-defines-p)))

  (defthm vl-defines-p-when-not-consp
    (implies (not (consp x))
             (equal (vl-defines-p x)
                    (not x))))

  (defthm vl-defines-p-of-cons
    (equal (vl-defines-p (cons a x))
           (and (consp a)
                (stringp (car a))
                (vl-echarlist-p (cdr a))
                (vl-defines-p x))))

  (defthm alistp-when-vl-defines-p
    (implies (vl-defines-p x)
             (alistp x)))

  (defthm vl-echarlist-p-of-cdr-of-hons-assoc-equal-when-vl-defines-p
    (implies (vl-defines-p x)
             (vl-echarlist-p (cdr (hons-assoc-equal a x)))))

  (defthm vl-defines-p-of-remove-from-alist
    (implies (vl-defines-p x)
             (vl-defines-p (remove-from-alist key x)))))



(defsection vl-lookup-in-defines
  :parents (vl-defines-p)
  :short "@(call vl-lookup-in-defines) looks up a string in a @(see
vl-defines-p)."

  :long "<p>We introduce @('vl-lookup-in-defines') instead of just using
@('hons-assoc-equal') because its stronger guard is good for type checking.
But for reasoning, we just leave this function enabled and reason
about@('hons-assoc-equal') instead.</p>

<p>Note that the defines aren't a fast alist and we aren't using @('hons-get');
we're just using @('hons-assoc-equal') as our normal form.</p>"

  (defun vl-lookup-in-defines (name x)
    (declare (xargs :guard (and (stringp name)
                                (vl-defines-p x))))
    (hons-assoc-equal name x)))


(defsection vl-compress-defines

  (defund vl-compressed-defines-p (x)
    (declare (xargs :guard t))
    (if (atom x)
        (eq x nil)
      (and (tuplep 3 (car x))
           (stringp (first (car x)))
           (stringp (second (car x)))
           (vl-location-p (third (car x)))
           (vl-compressed-defines-p (cdr x)))))

  (defund vl-compress-defines (x)
    (declare (xargs :guard (vl-defines-p x)))
    (if (atom x)
        nil
      (cons (list (caar x)
                  (vl-echarlist->string (cdar x))
                  (if (consp (cdar x))
                      (vl-echar->loc (car (cdar x)))
                    *vl-fakeloc*))
            (vl-compress-defines (cdr x)))))

  (local (in-theory (enable vl-compress-defines
                            vl-compressed-defines-p)))

  (defthm vl-compressed-defines-p-of-vl-compress-defines
    (implies (force (vl-defines-p x))
             (vl-compressed-defines-p (vl-compress-defines x))))

  (defund vl-uncompress-defines (x)
    (declare (xargs :guard (vl-compressed-defines-p x)))
    (if (atom x)
        nil
      (b* ((entry (car x))
           (name  (first entry))
           (str   (second entry))
           ((vl-location loc) (third entry))
           (chars (vl-echarlist-from-str str
                                         :filename loc.filename
                                         :line loc.line
                                         :col loc.col)))
          (cons (cons name chars)
                (vl-uncompress-defines (cdr x))))))

  (local (in-theory (enable vl-uncompress-defines)))

  (defthm vl-defines-p-of-vl-uncompress-defines
    (implies (force (vl-compressed-defines-p x))
             (vl-defines-p (vl-uncompress-defines x)))))



(defsection vl-make-initial-defines
  :parents (vl-defines-p)
  :short "@(call vl-make-initial-defines) is given a list of strings, and
builds a @(see vl-defines-p) structure that @('`define')s each of these names
to @('1')."

  (defund vl-make-initial-defines (x)
    (declare (xargs :guard (string-listp x)))
    (if (atom x)
        nil
      (cons (cons (car x) (vl-echarlist-from-str "1"))
            (vl-make-initial-defines (cdr x)))))

  (local (in-theory (enable vl-make-initial-defines)))

  (defthm vl-defines-p-of-vl-make-initial-defines
    (implies (force (string-listp x))
             (vl-defines-p (vl-make-initial-defines x)))))
