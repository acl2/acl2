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

;; lexutils.lisp --- general-purpose routines for writing echar-based lexers.

(in-package "VL")
(include-book "unicode/prefixp" :dir :system)
(include-book "../util/echars")
(local (include-book "../util/arithmetic"))


(defsection def-prefix/remainder-thms
  :parents (lexer)
  :short "Introduce prefix/remainder theorems for a lexing function."

  :long "<p>Many of our lexing routines take <tt>echars</tt>, an @(see
vl-echarlist-p), as input, and split this list into a <tt>prefix</tt> and
<tt>remainder</tt>.  This macro allows us to quickly prove several common
properties about such a function.  In particular, we show:</p>

<ul>

<li><tt>prefix</tt> is always a true-listp, and furthermore it is also a
vl-echarlist-p as long as the <tt>echars</tt> is.</li>

<li><tt>remainder</tt> is a true-listp exactly when <tt>echars</tt> is,
and furthermore it is a vl-echarlist-p whenever <tt>echars</tt> is.</li>

<li>Appending the <tt>prefix</tt> and <tt>remainder</tt> always returns
the original <tt>echars</tt>.  A corollary is that whenever <tt>prefix</tt>
is empty, <tt>remainder</tt> is the whole of <tt>echars</tt>.</li>

<li>The acl2-count of <tt>remainder</tt> is never greater than that of
<tt>echars</tt>, and strictly decreases whenever <tt>prefix</tt> is
non-nil.</li>

</ul>"

  (defmacro def-prefix/remainder-thms (fn &key
                                          (formals '(echars))
                                          (prefix-n '0)
                                          (remainder-n '1))
    (let ((mksym-package-symbol 'vl))
      `(encapsulate
        ()
        (local (in-theory (enable ,fn)))

        (defthm ,(mksym 'prefix-of- fn)
          (and (true-listp (mv-nth ,prefix-n (,fn . ,formals)))
               (implies (force (vl-echarlist-p echars))
                        (vl-echarlist-p (mv-nth ,prefix-n (,fn . ,formals)))))
          :rule-classes ((:rewrite)
                         (:type-prescription :corollary
                                             (true-listp (mv-nth ,prefix-n (,fn . ,formals))))))

        (defthm ,(mksym 'remainder-of- fn)
          (and (equal (true-listp (mv-nth ,remainder-n (,fn . ,formals)))
                      (true-listp echars))
               (implies (force (vl-echarlist-p echars))
                        (vl-echarlist-p (mv-nth ,remainder-n (,fn . ,formals)))))
          :rule-classes ((:rewrite)
                         (:type-prescription
                          :corollary
                          (implies (true-listp echars)
                                   (true-listp (mv-nth ,remainder-n (,fn . ,formals))))))
          :hints(("Goal" :in-theory (disable (force)))))

        (defthm ,(mksym 'append-of- fn)
          (equal (append (mv-nth ,prefix-n (,fn . ,formals))
                         (mv-nth ,remainder-n (,fn . ,formals)))
                 echars))

        (defthm ,(mksym 'no-change-loser-of- fn)
          (implies (not (mv-nth ,prefix-n (,fn . ,formals)))
                   (equal (mv-nth ,remainder-n (,fn . ,formals))
                          echars)))

        (defthm ,(mksym 'acl2-count-of- fn '-weak)
          (<= (acl2-count (mv-nth ,remainder-n (,fn . ,formals)))
              (acl2-count echars))
          :rule-classes ((:rewrite) (:linear))
          :hints(("Goal" :in-theory (disable (force)))))

        (defthm ,(mksym 'acl2-count-of- fn '-strong)
          (implies (mv-nth ,prefix-n (,fn . ,formals))
                   (< (acl2-count (mv-nth ,remainder-n (,fn . ,formals)))
                      (acl2-count echars)))
          :rule-classes ((:rewrite) (:linear))
          :hints(("Goal" :in-theory (disable (force)))))
        ))))



(defsection vl-matches-string-p
  :parents (lexer)
  :short "Determine if a string occurs at the front of an @(see
vl-echarlist-p)."

  :long "<p><b>Signature:</b> @(call vl-matches-string-p) returns a
boolean.</p>

<p>This function determines if some <tt>string</tt> occurs at the front of
<tt>echars</tt>.  More exactly, it computes:</p>

<code>
 (prefixp (coerce string 'list)
          (vl-echarlist-&gt;chars echars))
</code>

<p>But we actually implement the operation with a fast function that does not
call <tt>coerce</tt> or build the list of characters.</p>

<h3>Definition and Theorems</h3>

@(def vl-matches-string-p-impl)
@(def vl-matches-string-p)
@(thm len-when-vl-matches-string-p-fc)
@(thm consp-when-vl-matches-string-p-fc)
@(thm vl-matches-string-p-when-acl2-count-zero)"

  (defund vl-matches-string-p-impl (string i len echars)
    (declare (type string string)
             (xargs :guard (and (natp i)
                                (natp len)
                                (equal len (length string))
                                (vl-echarlist-p echars))
                    :measure (if (< (nfix i) (nfix len))
                                 (nfix (- (nfix len) (nfix i)))
                               0)))
    (mbe :logic (or (>= (nfix i) (nfix len))
                    (and (consp echars)
                         (eql (char string i) (vl-echar->char (car echars)))
                         (vl-matches-string-p-impl string (+ (nfix i) 1) len (cdr echars))))
         :exec (or (>= i len)
                   (and (consp echars)
                        (eql (char string i)
                             (the character (vl-echar->char (car echars))))
                        (vl-matches-string-p-impl string (+ i 1) len (cdr echars))))))

  (definlined vl-matches-string-p (string echars)
    (declare (type string string)
             (xargs :guard (and (not (equal string ""))
                                (vl-echarlist-p echars))
                    :verify-guards nil))
    (mbe :logic (prefixp (coerce (string-fix string) 'list) (vl-echarlist->chars echars))
         :exec (vl-matches-string-p-impl string 0 (length string) echars)))

  (local (defthm lemma
           (implies (and (stringp string)
                         (natp i)
                         (natp len)
                         (equal len (length string))
                         (vl-echarlist-p echars))
                    (equal (vl-matches-string-p-impl string i len echars)
                           (prefixp (nthcdr i (coerce string 'list)) (vl-echarlist->chars echars))))
           :hints(("Goal" :in-theory (enable vl-matches-string-p-impl)))))

  (verify-guards vl-matches-string-p$inline)

  (local (in-theory (enable vl-matches-string-p)))

  (defthm len-when-vl-matches-string-p-fc
    (implies (vl-matches-string-p string echars)
             (<= (len (coerce string 'list))
                 (len echars)))
    :rule-classes ((:forward-chaining)
                   (:linear)))

  (defthm consp-when-vl-matches-string-p-fc
    (implies (and (vl-matches-string-p string echars)
                  (stringp string)
                  (not (equal string "")))
             (consp echars))
    :rule-classes :forward-chaining)

  (defthm vl-matches-string-p-when-acl2-count-zero
    (implies (and (equal 0 (acl2-count echars))
                  (force (stringp string)))
             (equal (vl-matches-string-p string echars)
                    (equal string "")))
    :hints(("Goal" :in-theory (enable acl2-count)))))




(defsection vl-read-literal
  :parents (lexer)
  :short "Match a literal string."

  :long "<p><b>Signature:</b> @(call vl-read-literal) returns <tt>(mv prefix
remainder)</tt>.</p>

<p>This is a standard prefix/remainder style function which satisfies the
properties described in @(see def-prefix/remainder-thms).</p>

<p>We try to match <tt>echars</tt> against some literal <tt>string</tt>.  On
success, <tt>prefix</tt> is the matching prefix of <tt>echars</tt>; otherwise
it is <tt>nil</tt>.</p>

<h3>Definition and Additional Theorems</h3>

@(def vl-read-literal)
@(thm vl-echarlist->chars-of-prefix-of-vl-read-literal)
@(thm vl-echarlist->string-of-prefix-of-vl-read-literal)"

  (definlined vl-read-literal (string echars)
    (declare (type string string)
             (xargs :guard (and (not (equal string ""))
                                (vl-echarlist-p echars)
                                (true-listp echars))))
    (if (vl-matches-string-p string echars)
        (let ((strlen (length (string-fix string))))
          (mv (take strlen echars) (nthcdr strlen echars)))
      (mv nil echars)))

  (def-prefix/remainder-thms vl-read-literal :formals (string echars))

  (local (in-theory (enable vl-read-literal)))

  (defthm vl-echarlist->chars-of-prefix-of-vl-read-literal
    (implies (and (mv-nth 0 (vl-read-literal string echars))
                  (force (vl-echarlist-p echars)))
             (equal (vl-echarlist->chars (mv-nth 0 (vl-read-literal string echars)))
                    (coerce (string-fix string) 'list)))
    :hints(("Goal" :in-theory (enable vl-matches-string-p))))

  (defthm vl-echarlist->string-of-prefix-of-vl-read-literal
    (implies (and (mv-nth 0 (vl-read-literal string echars))
                  (force (vl-echarlist-p echars)))
             (equal (vl-echarlist->string (mv-nth 0 (vl-read-literal string echars)))
                    (string-fix string)))
    :hints(("Goal" :in-theory (enable vl-matches-string-p)))))



(defsection vl-read-some-literal
  :parents (lexer)
  :short "Match one of many literal strings."

  :long "<p><b>Signature:</b> @(call vl-read-some-literal) returns <tt>(mv
prefix remainder)</tt></p>

<p>This is a standard prefix/remainder style function which satisfies the
properties described in @(see def-prefix/remainder-thms).</p>

<p>We try to match <tt>echars</tt> against any member of <tt>strings</tt>, a
list of strings.  We try each string in order, so that <tt>prefix</tt> will
contain the characters for the first match.  If none of the strings match,
<tt>prefix</tt> will be <tt>nil</tt>.</p>

@(def vl-read-some-literal)"

  (defund vl-read-some-literal (strings echars)
    (declare (xargs :guard (and (string-listp strings)
                                (not (member-equal "" strings))
                                (vl-echarlist-p echars)
                                (true-listp echars))))
    (if (atom strings)
        (mv nil echars)
      (mv-let (prefix remainder)
              (vl-read-literal (car strings) echars)
              (if prefix
                  (mv prefix remainder)
                (vl-read-some-literal (cdr strings) echars)))))

  (def-prefix/remainder-thms vl-read-some-literal
    :formals (strings echars)))




(defsection vl-read-until-literal
  :parents (lexer)
  :short "Match any characters up until some literal."

  :long "<p><b>Signature:</b> @(call vl-read-until-literal) returns <tt>(mv
successp prefix remainder)</tt></p>

<p>This is a standard prefix/remainder style function which satisfies the
properties described in @(see def-prefix/remainder-thms).</p>

<p>On success, <tt>prefix</tt> contains all characters leading up to, <i>but
not including</i>, the first occurrence of <tt>string</tt>.  If <tt>string</tt>
never occurs in <tt>echars</tt>, then <tt>prefix</tt> is the entire list of
<tt>echars</tt> and <tt>remainder</tt> is its final cdr.</p>

<h3>Definition and Additional Theorems</h3>

@(def vl-read-until-literal-impl)
@(def vl-read-until-literal)
@(thm type-of-vl-read-until-literal-1)
@(thm len-of-vl-read-until-literal)
@(thm vl-matches-string-p-after-vl-read-until-literal)"

  (defund vl-read-until-literal-impl (string echars acc)
    (declare (type string string)
             (xargs :guard (and (not (equal string ""))
                                (vl-echarlist-p echars))))
    (cond ((atom echars)
           (mv nil acc echars))
          ((vl-matches-string-p string echars)
           (mv t acc echars))
          (t
           (vl-read-until-literal-impl string (cdr echars) (cons (car echars) acc)))))

  (definlined vl-read-until-literal (string echars)
    (declare (type string string)
             (xargs :guard (and (not (equal string ""))
                                (vl-echarlist-p echars))
                    :verify-guards nil))
    (mbe :logic (cond ((atom echars)
                       (mv nil nil echars))
                      ((vl-matches-string-p string echars)
                       (mv t nil echars))
                      (t
                       (mv-let (successp prefix remainder)
                               (vl-read-until-literal string (cdr echars))
                               (mv successp
                                   (cons (car echars) prefix)
                                   remainder))))
         :exec (mv-let (successp acc remainder)
                       (vl-read-until-literal-impl string echars nil)
                       (mv successp (reverse acc) remainder))))

  (local (in-theory (enable vl-read-until-literal
                            vl-read-until-literal-impl)))

  (defthm vl-read-until-literal-impl-equiv
    (equal (vl-read-until-literal-impl string echars acc)
           (list (mv-nth 0 (vl-read-until-literal string echars))
                 (revappend (mv-nth 1 (vl-read-until-literal string echars)) acc)
                 (mv-nth 2 (vl-read-until-literal string echars)))))

  (verify-guards vl-read-until-literal$inline)


  (def-prefix/remainder-thms vl-read-until-literal
    :formals (string echars)
    :prefix-n 1
    :remainder-n 2)

  (defthm type-of-vl-read-until-literal-1
    (or (equal (mv-nth 0 (vl-read-until-literal string echars)) t)
        (equal (mv-nth 0 (vl-read-until-literal string echars)) nil))
    :rule-classes :type-prescription)

  (defthm len-of-vl-read-until-literal
    (implies (mv-nth 0 (vl-read-until-literal string echars))
             (<= (len (coerce string 'list))
                 (len (mv-nth 2 (vl-read-until-literal string echars)))))
    :rule-classes ((:rewrite) (:linear)))

  (defthm vl-matches-string-p-after-vl-read-until-literal
    (implies (mv-nth 0 (vl-read-until-literal string echars))
             (equal (vl-matches-string-p string (mv-nth 2 (vl-read-until-literal string echars)))
                    t))))



(defsection vl-read-through-literal
  :parents (lexer)
  :short "Match any characters until and through some literal."

  :long "<p><b>Signature:</b> @(call vl-read-through-literal) returns <tt>(mv
successp prefix remainder)</tt></p>

<p>This is a standard prefix/remainder style function which satisfies the
properties described in @(see def-prefix/remainder-thms).</p>

<p>On success, <tt>prefix</tt> contains all characters leading up to, <i>and
including</i>, the first occurrence of <tt>string</tt>.  If <tt>string</tt>
never occurs in <tt>echars</tt>, then <tt>prefix</tt> is the entire list of
<tt>echars</tt> and <tt>remainder</tt> is its final cdr.</p>

<h3>Definition</h3>

@(def revappend-of-take)
@(def vl-read-through-literal)"

  (defun revappend-of-take (n x y)
    (declare (xargs :guard (and (natp n)
                                (<= n (len x)))))
    (mbe :logic (revappend (take n x) y)
         :exec (if (= n 0)
                   y
                 (revappend-of-take (- n 1) (cdr x) (cons (car x) y)))))

  (defund vl-read-through-literal (string echars)
    (declare (type string string)
             (xargs :guard (and (not (equal string ""))
                                (vl-echarlist-p echars)
                                (true-listp echars))))
    (mbe :logic (let ((string (string-fix string)))
                  (mv-let (successp prefix remainder)
                          (vl-read-until-literal string echars)
                          (if (not successp)
                              (mv nil prefix remainder)
                            (mv t
                                (append prefix (take (length string) remainder))
                                (nthcdr (length string) remainder)))))
         :exec (mv-let (successp prefix remainder)
                       (vl-read-until-literal-impl string echars nil)
                       (if (not successp)
                           (mv nil (reverse prefix) remainder)
                         (let ((strlen (length string)))
                           (mv t
                               (reverse (revappend-of-take strlen remainder prefix))
                               (nthcdr strlen remainder)))))))

  (def-prefix/remainder-thms vl-read-through-literal
    :formals (string echars)
    :prefix-n 1
    :remainder-n 2)

  (defthm prefix-of-vl-read-through-literal-under-iff
    (implies (and (stringp string)
                  (not (equal string "")))
             (iff (mv-nth 1 (vl-read-through-literal string echars))
                  (consp echars)))
    :hints(("Goal" :in-theory (enable vl-read-through-literal
                                      vl-read-until-literal)))))




(defsection vl-echarlist-kill-underscores
  :parents (lexer)
  :short "@(call vl-echarlist-kill-underscores) removes all occurrences of the
underscore character from a @(see vl-echarlist-p)."

  :long "<p>Verilog uses underscores as a digit separator, e.g., you can write
<tt>1_000_000</tt> instead of <tt>1000000</tt> for greater readability on long
numbers.  This function strips away the underscores so we can interpret the
remaining digits with @(see vl-echarlist-unsigned-value).</p>

<h3>Definition and Theorems</h3>

@(def vl-echarlist-kill-underscores)
@(thm vl-echarlist-p-of-vl-echarlist-kill-underscores)"

  (defund vl-echarlist-kill-underscores (x)
    (declare (xargs :guard (vl-echarlist-p x)))
    (if (consp x)
        (if (eql (vl-echar->char (car x)) #\_)
            (vl-echarlist-kill-underscores (cdr x))
          (cons (car x)
                (vl-echarlist-kill-underscores (cdr x))))
      nil))

  (local (in-theory (enable vl-echarlist-kill-underscores)))

  (defthm vl-echarlist-p-of-vl-echarlist-kill-underscores
    (implies (force (vl-echarlist-p x))
             (vl-echarlist-p (vl-echarlist-kill-underscores x)))))



(defsection vl-read-while-ctype
  :parents (lexer)
  :short "Match as many characters of some type as possible."

  :long "<p><b>Signature:</b> @(call vl-read-while-ctype) returns <tt>(mv
prefix remainder)</tt>.</p>

<p>This is a generic function.  See @(see defchar) for a convenient way to
instantiate this function, and its corresponding theory, for your own character
recognizers.</p>

<p><tt>(vl-ctype-p x)</tt> is a constrained function that we imagine represents
some recognizer for certain <tt>characterp</tt> objects.  Using this function,
@(call vl-read-while-ctype) splits <tt>echars</tt> into a prefix and remainder,
where <tt>prefix</tt> holds all of the leading characters of <tt>echars</tt>
that satisfy <tt>vl-ctype-p</tt>, and <tt>remainder</tt> holds the rest.</p>

<h3>Definitions</h3>

@(def vl-ctype-list-p)
@(def vl-read-while-ctype-impl)
@(def vl-read-while-ctype)

<h3>Theorems</h3>

@(thm prefix-of-vl-read-while-ctype)
@(thm equiv-of-vl-read-while-ctype-impl)
@(thm remainder-of-vl-read-while-ctype)
@(thm prefix-of-vl-read-while-ctype-when-vl-ctype-p)
@(thm vl-read-while-ctype-sound)
@(thm vl-read-while-ctype-complete)
@(thm append-of-vl-read-while-ctype)
@(thm no-change-loser-of-vl-read-while-ctype)
@(thm acl2-count-of-vl-read-while-ctype-weak)
@(thm acl2-count-of-vl-read-while-ctype-strong)"

  (encapsulate
   (((vl-ctype-p *) => *))
   (local (defun vl-ctype-p (x)
            (eql x #\a)))
   (defthm vl-type-p-of-nil
     (not (vl-ctype-p nil))))

  (defund vl-ctype-list-p (x)
    (declare (xargs :guard (vl-echarlist-p x)))
    (if (consp x)
        (and (vl-ctype-p (car x))
             (vl-ctype-list-p (cdr x)))
      t))

  (defthm vl-ctype-list-p-when-not-consp
    (implies (not (consp x))
             (equal (vl-ctype-list-p x)
                    t))
    :hints(("Goal" :in-theory (enable vl-ctype-list-p))))

  (defthm vl-ctype-list-p-of-cons
    (equal (vl-ctype-list-p (cons a x))
           (and (vl-ctype-p a)
                (vl-ctype-list-p x)))
    :hints(("Goal" :in-theory (enable vl-ctype-list-p))))

  (defund vl-read-while-ctype-impl (echars acc)
    (declare (xargs :guard (vl-echarlist-p echars)))
    (cond ((atom echars)
           (mv acc echars))
          ((vl-ctype-p (vl-echar->char (car echars)))
           (vl-read-while-ctype-impl (cdr echars) (cons (car echars) acc)))
          (t
           (mv acc echars))))

  (defund vl-read-while-ctype (echars)
    (declare (xargs :guard (vl-echarlist-p echars)
                    :verify-guards nil))
    (mbe :logic (cond ((atom echars)
                       (mv nil echars))
                      ((vl-ctype-p (vl-echar->char (car echars)))
                       (mv-let (prefix remainder)
                               (vl-read-while-ctype (cdr echars))
                               (mv (cons (car echars) prefix) remainder)))
                      (t
                       (mv nil echars)))
         :exec (mv-let (prefix-rev remainder)
                       (vl-read-while-ctype-impl echars nil)
                       (mv (reverse prefix-rev) remainder))))

  (local (in-theory (enable vl-read-while-ctype)))

  (defthm prefix-of-vl-read-while-ctype
    (and (true-listp (mv-nth 0 (vl-read-while-ctype echars)))
         (implies (force (vl-echarlist-p echars))
                  (vl-echarlist-p (mv-nth 0 (vl-read-while-ctype echars)))))
    :rule-classes ((:rewrite)
                   (:type-prescription :corollary
                                       (true-listp (mv-nth 0 (vl-read-while-ctype echars))))))

  (defthm equiv-of-vl-read-while-ctype-impl
    (and (equal (len (vl-read-while-ctype-impl echars acc)) 2)
         (implies (true-listp acc)
                  (and (true-listp (mv-nth 0 (vl-read-while-ctype-impl echars acc)))
                       (equal (mv-nth 0 (vl-read-while-ctype-impl echars acc))
                              (revappend (mv-nth 0 (vl-read-while-ctype echars)) acc))
                       (equal (mv-nth 1 (vl-read-while-ctype-impl echars acc))
                              (mv-nth 1 (vl-read-while-ctype echars))))))
    :hints(("Goal" :in-theory (enable vl-read-while-ctype-impl))))

  (verify-guards vl-read-while-ctype)

  (defthm remainder-of-vl-read-while-ctype
    (and (equal (true-listp (mv-nth 1 (vl-read-while-ctype echars)))
                (true-listp echars))
         (implies (force (vl-echarlist-p echars))
                  (vl-echarlist-p (mv-nth 1 (vl-read-while-ctype echars)))))
    :rule-classes ((:rewrite)
                   (:type-prescription
                    :corollary
                    (implies (true-listp echars)
                             (true-listp (mv-nth 1 (vl-read-while-ctype echars)))))))

  (defthm prefix-of-vl-read-while-ctype-when-vl-ctype-p
    (implies (vl-ctype-p (vl-echar->char (car echars)))
             (iff (mv-nth 0 (vl-read-while-ctype echars))
                  t)))

  (defthm vl-read-while-ctype-sound
    ;; This says that all the characters vl-read-while-ctype reads are, indeed,
    ;; vl-ctype-p's.  In other words, it reads only good characters.
    (vl-ctype-list-p (vl-echarlist->chars (mv-nth 0 (vl-read-while-ctype echars)))))

  (defthm vl-read-while-ctype-complete
    ;; This says that if vl-read-while-ctype didn't read all the entire stream,
    ;; it leaves a non vl-ctype-p at the front.  In other words, it reads
    ;; exactly as far as it can.
    (equal (vl-ctype-p (vl-echar->char (car (mv-nth 1 (vl-read-while-ctype echars)))))
           nil))

  (defthm append-of-vl-read-while-ctype
    (equal (append (mv-nth 0 (vl-read-while-ctype echars))
                   (mv-nth 1 (vl-read-while-ctype echars)))
           echars))

  (defthm no-change-loser-of-vl-read-while-ctype
    (implies (not (mv-nth 0 (vl-read-while-ctype echars)))
             (equal (mv-nth 1 (vl-read-while-ctype echars))
                    echars)))

  (defthm acl2-count-of-vl-read-while-ctype-weak
    (<= (acl2-count (mv-nth 1 (vl-read-while-ctype echars)))
        (acl2-count echars))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-vl-read-while-ctype-strong
    (implies (mv-nth 0 (vl-read-while-ctype echars))
             (< (acl2-count (mv-nth 1 (vl-read-while-ctype echars)))
                (acl2-count echars)))
    :rule-classes ((:rewrite) (:linear))))



(defsection defchar
  :parents (lexer)
  :short "Introduce lexing utilites from a character recognizer."

  :long "<p><tt>Defchar</tt> is a macro for instantiating @(see
vl-read-while-ctype).</p>

<h5>General Form</h5>
<code>
 (DEFCHAR BASENAME CRITERIA
   [:PREFIX prefix]
   [:PKG pkg])
</code>

<h5>Example</h5>
<code>
 (defchar whitespace
  (or (eql x #\Space)
      (eql x #\Tab)
      (eql x #\Page) ;; \"form feed\"
      (eql x #\Newline)))
</code>

<p>The <tt>basename</tt>, <tt>prefix</tt>, and <tt>pkg</tt> are each symbols
which influence the names of the new definitions and theorems we introduce.
In particular,</p>

<ul>

<li>The <tt>basename</tt> is the name of the main part of the new character
type you are introducing.</li>

<li>The <tt>prefix</tt> is prepended to the symbol names we generate, and
defaults to the symbol <tt>'vl-</tt>.  For instance, in the above example, the
single-character recognizer will be named <tt>vl-whitespace-p</tt>.</li>

<li>The <tt>pkg</tt> is used to control what package the new functions and
theorems are defined in.  It defaults to <tt>'VL::foo</tt>, so in the above
example the symbols are introduced in the <tt>VL::</tt> package.
</li>

</ul>

<p>Finally, the <tt>criteria</tt> is some term about the variable <tt>x</tt>.
You may assume that <tt>x</tt> is an ordinary <tt>characterp</tt>, and specify
what kinds of characters you want using functions such as <tt>eql</tt> and
<tt>char&lt;=</tt>.</p>

<p>Calling this macro introduces the following functions:</p>

<ul>

<li><tt>(PKG::PREFIX-BASENAME-P X)</tt>, recognizes those <tt>characterp</tt>s
which satsify <tt>criteria</tt>,</li>

<li><tt>(PKG::PREFIX-BASENAME-ECHAR-P X)</tt>, recognizes those @(see
vl-echar-p)s whose character satisfies <tt>criteria</tt>,</li>

<li><tt>(PKG::PREFIX-BASENAME-LIST-P X)</tt>, recognizes those <tt>character-listp</tt>s
where every character satisfies <tt>criteria</tt>,</li>

<li><tt>(PKG::PREFIX-READ-WHILE-BASENAME ECHARS)</tt> splits <tt>echars</tt>
into a prefix and remainder, where <tt>prefix</tt> is the longest leading
list of characters that satisfy <tt>criteria</tt>.</li>

</ul>

<p>It also introducs a number of theorems, enumerated in @(see
vl-read-while-ctype).</p>"

  (defun defchar-fn (prefix basename criteria pkg parents short long)
    (flet ((mksym (name pkg)
                  (intern-in-package-of-symbol name pkg)))
          (let* ((namestr         (cat prefix basename "-P"))
                 (enamestr        (cat prefix basename "-ECHAR-P"))
                 (liststr         (cat prefix basename "-LIST-P"))
                 (readwhilestr    (cat prefix "READ-WHILE-" basename))
                 (readwhileimpstr (cat readwhilestr "-IMPL"))
                 (char-p          (mksym namestr pkg))
                 (echar-p         (mksym enamestr pkg))
                 (char-list-p     (mksym liststr pkg))
                 (read-while      (mksym readwhilestr pkg))
                 (read-while-impl (mksym readwhileimpstr pkg))
                 (x               (mksym "X" pkg))
                 (fi-pairs        `((vl-ctype-p               ,char-p)
                                    (vl-ctype-list-p          ,char-list-p)
                                    (vl-read-while-ctype      ,read-while)
                                    (vl-read-while-ctype-impl ,read-while-impl)))
                 (doc             (if (or parents short long)
                                      `((defxdoc ,char-p
                                          :parents ,parents
                                          :short ,short
                                          :long ,long))
                                    nil)))
            `(encapsulate
              ()
              (set-verify-guards-eagerness 2) ;; implicitly local
              (logic)

              ,@doc

              (definlined ,char-p (,x)
                (declare (type character ,x))
                ;; This MBT ensures that ,char-p does not recognize nil.
                (and (mbt (characterp ,x))
                     ,criteria))

              (definline ,echar-p (,x)
                (declare (xargs :guard (vl-echar-p ,x)))
                (,char-p (vl-echar->char ,x)))

              (deflist ,char-list-p (,x)
                (,char-p ,x)
                :guard (character-listp ,x)
                :parents ,parents)

              (defund ,read-while-impl (echars acc)
                (declare (xargs :guard (vl-echarlist-p echars)))
                (cond ((atom echars)
                       (mv acc echars))
                      ((,char-p (vl-echar->char (car echars)))
                       (,read-while-impl (cdr echars) (cons (car echars) acc)))
                      (t
                       (mv acc echars))))

              (definlined ,read-while (echars)
                (declare (xargs :guard (vl-echarlist-p echars)
                                :verify-guards nil))
                (mbe :logic (cond ((atom echars)
                                   (mv nil echars))
                                  ((,char-p (vl-echar->char (car echars)))
                                   (mv-let (prefix remainder)
                                           (,read-while (cdr echars))
                                           (mv (cons (car echars) prefix) remainder)))
                                  (t
                                   (mv nil echars)))
                     :exec (mv-let (prefix-rev remainder)
                                   (,read-while-impl echars nil)
                                   (mv (reverse prefix-rev) remainder))))

              (local (in-theory (enable ,read-while-impl ,read-while)))

              (defthm ,(mksym (cat "PREFIX-OF-" readwhilestr) pkg)
                (and (true-listp (mv-nth 0 (,read-while echars)))
                     (implies (force (vl-echarlist-p echars))
                              (vl-echarlist-p (mv-nth 0 (,read-while echars)))))
                :rule-classes ((:rewrite)
                               (:type-prescription
                                :corollary (true-listp (mv-nth 0 (,read-while echars)))))
                :hints(("Goal" :use ((:functional-instance prefix-of-vl-read-while-ctype . ,fi-pairs)))))

              (local (defthm ,(mksym (cat "EQUIV-OF-" readwhileimpstr) pkg)
                       (and (equal (len (,read-while-impl echars acc)) 2)
                            (implies (true-listp acc)
                                     (and (true-listp (mv-nth 0 (,read-while-impl echars acc)))
                                          (equal (mv-nth 0 (,read-while-impl echars acc))
                                                 (revappend (mv-nth 0 (,read-while echars)) acc))
                                          (equal (mv-nth 1 (,read-while-impl echars acc))
                                                 (mv-nth 1 (,read-while echars))))))
                       :hints(("Goal" :use ((:functional-instance equiv-of-vl-read-while-ctype-impl . ,fi-pairs))))))

              (verify-guards ,(intern-in-package-of-symbol
                               (str::cat (symbol-name read-while) acl2::*inline-suffix*)
                               read-while))

              (defthm ,(mksym (cat "REMAINDER-OF-" readwhilestr) pkg)
                (and (equal (true-listp (mv-nth 1 (,read-while echars)))
                            (true-listp echars))
                     (implies (vl-echarlist-p echars)
                              (vl-echarlist-p (mv-nth 1 (,read-while echars)))))
                :rule-classes ((:rewrite)
                               (:type-prescription
                                :corollary
                                (implies (true-listp echars)
                                         (true-listp (mv-nth 1 (,read-while echars))))))
                :hints(("Goal" :use ((:functional-instance remainder-of-vl-read-while-ctype . ,fi-pairs)))))

              (defthm ,(mksym (cat "PREFIX-OF-" readwhilestr "-WHEN-" namestr) pkg)
                (implies (,char-p (vl-echar->char (car echars)))
                         (iff (mv-nth 0 (,read-while echars))
                              t))
                :hints(("Goal" :use ((:functional-instance prefix-of-vl-read-while-ctype-when-vl-ctype-p . ,fi-pairs)))))

              (defthm ,(mksym (cat readwhilestr "-SOUND") pkg)
                (,char-list-p (vl-echarlist->chars (mv-nth 0 (,read-while echars))))
                :hints(("Goal" :use ((:functional-instance vl-read-while-ctype-sound . ,fi-pairs)))))

              (defthm ,(mksym (cat readwhilestr "-COMPLETE") pkg)
                (equal (,char-p (vl-echar->char (car (mv-nth 1 (,read-while echars)))))
                       nil)
                :hints(("Goal" :use ((:functional-instance vl-read-while-ctype-complete . ,fi-pairs)))))

              (defthm ,(mksym (cat "APPEND-OF-" readwhilestr) pkg)
                (equal (append (mv-nth 0 (,read-while echars))
                               (mv-nth 1 (,read-while echars)))
                       echars)
                :hints(("Goal" :use ((:functional-instance append-of-vl-read-while-ctype . ,fi-pairs)))))

              (defthm ,(mksym (cat "NO-CHANGE-LOSER-OF-" readwhilestr) pkg)
                (implies (not (mv-nth 0 (,read-while echars)))
                         (equal (mv-nth 1 (,read-while echars))
                                echars))
                :hints(("Goal" :use ((:functional-instance no-change-loser-of-vl-read-while-ctype . ,fi-pairs)))))

              (defthm ,(mksym (cat "ACL2-COUNT-OF-" readwhilestr "-WEAK") pkg)
                (<= (acl2-count (mv-nth 1 (,read-while echars)))
                    (acl2-count echars))
                :rule-classes ((:rewrite) (:linear))
                :hints(("Goal" :use ((:functional-instance acl2-count-of-vl-read-while-ctype-weak . ,fi-pairs)))))

              (defthm ,(mksym (cat "ACL2-COUNT-OF-" readwhilestr "-STRONG") pkg)
                (implies (mv-nth 0 (,read-while echars))
                         (< (acl2-count (mv-nth 1 (,read-while echars)))
                            (acl2-count echars)))
                :rule-classes ((:rewrite) (:linear))
                :hints(("Goal" :use ((:functional-instance acl2-count-of-vl-read-while-ctype-strong . ,fi-pairs)))))

                ))))

  (defmacro defchar (basename criteria &key
                              (prefix 'vl-)
                              (pkg 'nil pkg-p)
                              (parents '(lexer))
                              (short 'nil)
                              (long 'nil)
                              )
    (declare (xargs :guard (and (symbolp prefix)
                                (symbolp basename)
                                (symbolp pkg))))
    (defchar-fn (symbol-name prefix)
      (symbol-name basename)
      criteria
      (if pkg-p pkg prefix)
      parents short long)))


(local
 (encapsulate
  ()
  ;; Simple test to make sure defchar is working

  (defchar nine
    (eql x #\9))))


(defun vl-orcar-mv2s-fn (forms)
  (if (consp forms)
      (if (consp (cdr forms))
          `(mv-let (a-for-vl-orcar-mv2s-do-not-use-elsewhere
                    b-for-vl-orcar-mv2s-do-not-use-elsewhere)
                   ,(car forms)
                   (if a-for-vl-orcar-mv2s-do-not-use-elsewhere
                       (mv a-for-vl-orcar-mv2s-do-not-use-elsewhere
                           b-for-vl-orcar-mv2s-do-not-use-elsewhere)
                     (check-vars-not-free
                      (a-for-vl-orcar-mv2s-do-not-use-elsewhere
                       b-for-vl-orcar-mv2s-do-not-use-elsewhere)
                     ,(vl-orcar-mv2s-fn (cdr forms)))))
        (car forms))
    (er hard? 'vl-orcar-mv2s "Expected at least one form.")))

(defmacro vl-orcar-mv2s (&rest forms)
  ;; Each form in FORMS should return (MV A B).  We return the first
  ;; of these MV pairs with A != nil.
  (vl-orcar-mv2s-fn forms))



