; Centaur Miscellaneous Books
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
; introduce-var.lisp
;
; Original authors: Jared Davis <jared@centtech.com>
;                   Anna Slobadova <anna@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "clause-processors/generalize" :dir :system)
(include-book "centaur/vl/util/namedb" :dir :system)


; We introduce the INTRODUCE-VARS clause processor.  To use this clause
; processor you should just do this:
;
;   :hints(("Goal" ... your hints ...)
;          (introduce-vars))
;
; Whenever this clause processor runs, it examines your goal for any
; occurrences of (INTRODUCE-VAR 'NAME TERM), and replaces them with fresh
; variables that are based on NAME.
;
; The function INTRODUCE-VAR is just an identity that returns TERM and ignores
; NAME.  Typically you will want to write rewrite rules that produce
; INTRODUCE-VAR forms anywhere that you don't want to see an offensive term.
;
; For instance, a rewrite rule like:
;
;   (implies (and (true-listp x)
;                 (true-listp y))
;            (equal (equal x y)
;                   (let ((n (look-for-mismatching-elt x y)))
;                     (equal (nth n x) (nth n y)))))
;
; Where look-for-mismatching-elt presumably goes through the lists to find
; the first index where they disagree.  The problem with a rule like this is
; that when it fires, you'll end up with large, yucky terms like
;
;        (look-for-mismatching-elt (cons ...) (foo ...))
;
; Where you really just want a new variable, say "idx".  The fix for this rule
; is just:
;
;   (implies (and (true-listp x)
;                 (true-listp y))
;            (equal (equal x y)
;                   (let ((n (introduce-var 'idx (hide (look-for-mismatching-elt x y)))))
;                     (equal (nth n x) (nth n y)))))
;
; The hide is optional but probably a good idea.  After this rule has fired, the
; INTRODUCE-VARS clause processor will notice the new, even uglier term:
;
;      (introduce-var 'idx
;       (hide
;        (look-for-mismatching-elt (cons ...) (foo ...))))
;
; And will replace it with something like IDX, IDX_1, etc., as appropriate to
; avoid name clashes.

(defund introduce-var (name term)
  (declare (xargs :guard t)
           (ignore name))
  term)


(mutual-recursion

; These scanning functions look for occurrences of (INTRODUCE-VAR 'VAR TERM)
; and construct an alist with (TERM . VAR) entries.  In practice we expect that
; VAR should generally be a string or symbol, but we allow it to be any object.

 (defun scan-term-for-introduce-var (x)
   (declare (xargs :guard t))
   (cond ((atom x) nil)
         ((quotep x) nil)
         (t (case-match x
              (('introduce-var ('quote v . &) . &)
               (list (cons x v)))
              (& (scan-termlist-for-introduce-var (cdr x)))))))
 (defun scan-termlist-for-introduce-var (x)
   (declare (xargs :guard t))
   (if (atom x)
       nil
     (append (scan-term-for-introduce-var (car x))
             (scan-termlist-for-introduce-var (cdr x))))))


; We need to be careful to avoid name clashes.  There can be two kinds of name
; clashes:
;
; (1) There might be separate occurrences of INTRODUCE-VAR that use the same VAR,
; for instance our goal might be:
;
;    (let ((a (introduce-var 'key (hide (find-key x y))))
;          (b (introduce-var 'key (hide (find-key y x)))))
;      (conclusion a b))
;
; Here we need to be sure to introduce separate keys, e.g., KEY and KEY_2.
;
; (2) The variable we want to introduce might already be used somewhere else in
; the goal, e.g.,
;
;    (let ((a (introduce-var 'key (hide (find-key x y)))))
;      (implies (member key x)
;               ...))
;
; In which case we must not try to introduce generalize the term to just KEY.
; We use a VL name database to generate fresh keys.  This is slightly
; complicated because name databases only deal with strings.

(defund names-for-introduce-var-to-avoid (current-pkg var-lst)
  "Returns a string list."
  (declare (xargs :guard (and (stringp current-pkg)
                              (not (equal current-pkg "")))))

; VAR-LST should initially be the output of TERM-VARS-LIST on the clause.
; I.e., it's a list of all the variables we need to avoid due to #2 above.
; We're always going to generate symbols in the current-package, so we only
; need to avoid symbols in var-lst that are in the current package.

  (cond ((atom var-lst)
         nil)
        ((and (symbolp (car var-lst))
              (equal (car var-lst) (intern$ (symbol-name (car var-lst)) current-pkg)))
         ;; It's a symbol that's effectively in the current package, so we need
         ;; to avoid it.
         (cons (symbol-name (car var-lst))
               (names-for-introduce-var-to-avoid current-pkg (cdr var-lst))))
        (t
         (names-for-introduce-var-to-avoid current-pkg (cdr var-lst)))))

(local (defthm string-listp-of-names-for-introduce-var-to-avoid
         (string-listp (names-for-introduce-var-to-avoid current-pkg var-lst))
         :hints(("Goal" :in-theory (enable names-for-introduce-var-to-avoid)))))


(defund uniquify-introduce-var-alist (current-pkg alist namedb)
  "Returns (MV ALIST' NAMEDB')"
  (declare (xargs :guard (and (stringp current-pkg)
                              (not (equal current-pkg ""))
                              (vl::vl-namedb-p namedb))))

; ALIST is the alist of (TERM . VAR) entries that we found, where each TERM
; should be replaced by VAR.  But the VARs in ALIST are not necessarily unique.
; Make a new alist where each term is bound to a new, unique symbol in the
; current package.

  (b* (((when (atom alist))
        (mv alist namedb))

       ((when (atom (car alist)))
        ;; Bad alist convention
        (uniquify-introduce-var-alist current-pkg (cdr alist) namedb))

       ((cons term var) (car alist))
       (preferred-varname (cond ((symbolp var) (symbol-name var))
                                ((stringp var) var)
                                (t             "VAR")))
       ((mv fresh-name namedb)
        (vl::vl-namedb-indexed-name preferred-varname namedb))
       (fresh-sym (intern$ fresh-name current-pkg))
       ((mv rest namedb)
        (uniquify-introduce-var-alist current-pkg (cdr alist) namedb)))
    (mv (cons (cons term fresh-sym) rest)
        namedb)))

(local (defthm vl-namedb-p-of-uniquify-introduce-var-alist
         (implies (vl::vl-namedb-p namedb)
                  (vl::vl-namedb-p (mv-nth 1 (uniquify-introduce-var-alist current-pkg alist namedb))))
         :hints(("Goal" :in-theory (enable uniquify-introduce-var-alist)))))


(defund scan-for-introduce-var (current-pkg clause)
  (declare (xargs :guard (and (stringp current-pkg)
                              (not (equal current-pkg "")))))
  (b* ((initial-alist (scan-termlist-for-introduce-var clause))
       ((unless initial-alist)
        ;; Optimization: avoid looking at the term vars if there's nothing to do
        nil)
       (clause-vars (ec-call (term-vars-list clause)))
       (avoid-names (names-for-introduce-var-to-avoid current-pkg clause-vars))
       (namedb      (vl::vl-starting-namedb avoid-names))
       ((mv fresh-alist namedb)
        (uniquify-introduce-var-alist current-pkg initial-alist namedb)))
    (vl::vl-free-namedb namedb)
    fresh-alist))

(defmacro introduce-vars ()
  '(let ((al (scan-for-introduce-var (current-package state) clause)))
     (and al
          `(:computed-hint-replacement
            t
            :clause-processor (simple-generalize-cp clause ',al)))))

#||

(defstub foo () nil)
(defstub bar () nil)
(defstub baz () nil)

(set-gag-mode nil)

(thm
 ;; Good, we properly get (equal key FOO) and (equal key FOO_1) instead
 ;; of thinking that KEY is equal to both.
 (implies (and (equal key (introduce-var 'foo (foo)))
               (equal key (introduce-var 'foo (bar))))
          (baz))
 :hints((introduce-vars)))

(thm
 ;; Good, we get FOO and KEY_1 instead of FOO and KEY.
 (implies (and (equal key (introduce-var 'foo (foo)))
               (equal key (introduce-var 'key (bar))))
          (equal key (baz)))
 :hints((introduce-vars)))


(thm
 ;; Nice, we get ACL2-package variables even though we're using VL-package
 ;; names in the introduce-var calls
 (implies (and (equal key (introduce-var 'vl::foo (foo)))
               (equal key (introduce-var 'vl::key (bar))))
          (equal key (baz)))
 :hints((introduce-vars)))


(thm
 ;; Good enough, strings and other keys work, although not in a great way.
 (implies (and (equal key (introduce-var 1 (foo)))
               (equal key (introduce-var "bar" (bar))))
          (equal key (baz)))
 :hints((introduce-vars)))

||#