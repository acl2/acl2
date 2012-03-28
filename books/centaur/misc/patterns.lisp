; Centaur Miscellaneous Books
; Copyright (C) 2010 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "alist-equiv")
(local (include-book "centaur/misc/fast-alists" :dir :system))

; BOZO Jared is putting this book into centaur/misc temporarily.  After we
; release esim, move it back into the esim dir.

(defsection patterns
  :parents (esim)
  :short "A representation for structured data."

  :long "<p>A <b>pattern</b> is a simple kind of structure for representing
structured data.</p>

<p>Patterns were historically used in the EMOD hardware simulator, where they
played a large role.  In @(see esim) we have largely moved toward just using
alists instead of patterns, but patterns are still used in a few places, most
notably the representation of module input and output lists.</p>

<p>A definition for patterns is:</p>

<ul>
<li><tt>NIL</tt> is a special, empty pattern</li>
<li>Any non-nil atom is a <b>pattern variable</b> (a kind of pattern), and</li>
<li>A cons of two patterns is a pattern.</li>
</ul>

<p>This means that any ACL2 object is a pattern, but here is perhaps a typical
example of a pattern:</p>

<code>
 (a (b0 b1) (c (d0 d1) e))    ;; example pattern
</code>

<p>We say that this pattern is <b>compatible</b> with certain other ACL2
objects that have a similar cons structure, such as:</p>

<code>
 (1 (2 3) (4 (5 6) 7))        ;; example data
</code>

<p>The general idea is that the example data \"fits\" into the pattern by
saying:</p>

<code>
  a = 1   b0 = 2   c = 4   d0 = 5   e = 7
          b1 = 3           d1 = 6
</code>

<p>Another way of thinking about patterns is as follows.  Consider an alist
like <tt>((a . 1) (b . 2) (c . 3))</tt>.  It is often convenient to have the
keys and values together.  But if you remember that your keys are <tt>(a b
c)</tt>, then you could separately work with your values, <tt>(1 2 3)</tt>.
This is the basic idea behind patterns, except that the keys and values can be
structured instead of just being lists.</p>

<p>This is a little awkward, and it would probably usually be better to just
work with alists everywhere.</p>")


(defsection data-for-patternp
  :parents (patterns)
  :short "@(call data-for-patternp) determines whether <tt>data</tt> is
compatible with the pattern <tt>pat</tt>."

  (defun data-for-patternp (pat data)
    (declare (xargs :guard t))
    (if pat
        (or (atom pat)
            (and (consp data)
                 (data-for-patternp (car pat) (car data))
                 (data-for-patternp (cdr pat) (cdr data))))
      t)))



(defsection similar-patternsp
  :parents (patterns)
  :short "@(call similar-patternsp) determines whether <tt>pat1</tt> and
<tt>pat2</tt> are compatible with the same data."

  (defun similar-patternsp (pat1 pat2)
    (declare (xargs :guard t))
    (if pat1
        (and pat2
             (if (atom pat1)
                 (atom pat2)
               (and (consp pat2)
                    (similar-patternsp (car pat1) (car pat2))
                    (similar-patternsp (cdr pat1) (cdr pat2)))))
      (not pat2)))

  (defthm similar-patternsp-commutes
    (implies (similar-patternsp pat2 pat1)
             (similar-patternsp pat1 pat2)))

  (defthm similar-patternsp-self
    (similar-patternsp x x))

  (defequiv similar-patternsp)

  (defcong similar-patternsp iff (data-for-patternp x y) 1)
  (defcong similar-patternsp iff (data-for-patternp x y) 2))


(defsection pat->al
  :parents (patterns)
  :short "@(call pat->al) extends the alist <tt>al</tt> by associating the
variables from <tt>pat</tt> with the data from <tt>data</tt>."

  :long "<p>The cars of the new pairs are precisely all the non-NIL atoms of
the pattern <tt>pat</tt>.  The cdrs of the new pairs are the objects at
corresponding locations in <tt>data</tt>.  For instance,</p>

<code>
   (pat-&gt;al '(a (b) (c d))
             '(1 (2) (3 4))
             nil)
     --&gt;
   ((a . 1) (b . 2) (c . 3) (d . 4))
</code>

<p>The alist is extended with ordinary <tt>cons</tt> operations; that is, it
probably doesn't make much sense for <tt>al</tt> to be a fast alist, because
the new alist won't be fast.  See @(see pat->fal) for an alternative.</p>"

  (defun pat->al (pat data al)
    (declare (xargs :guard (data-for-patternp pat data)))

    (if pat
        (if (atom pat)
            (cons (cons pat data) al)
          (pat->al (car pat)
                   (car data)
                   (pat->al (cdr pat) (cdr data) al)))
      al))

  (local
   (defun pat->al-to-append-ind (a b acc)
     (if a
         (if (atom a)
             (cons (cons a b) acc)
           (list (pat->al-to-append-ind
                  (car a) (car b)
                  (pat->al (cdr a) (cdr b) acc))
                 (pat->al-to-append-ind
                  (car a) (car b)
                  (pat->al (cdr a) (cdr b) nil))
                 (pat->al-to-append-ind (cdr a) (cdr b) acc)))
       nil)))

  (defthm pat->al-to-append
    (implies (syntaxp (not (equal acc ''nil)))
             (equal (pat->al a b acc)
                    (append (pat->al a b nil)
                            acc)))
    :hints (("goal" :induct (pat->al-to-append-ind a b acc)))))


(defsection pat->fal
  :parents (patterns)
  :short "Alternative to @(see pat->al) that generates a fast alist."
  :long "<p>The input <tt>al</tt> also needs to be fast.</p>"

  (defun pat->fal (pat data al)
    (declare (xargs :guard (data-for-patternp pat data)))
    (mbe :logic (pat->al pat data al)
         :exec
         (if pat
             (if (atom pat)
                 (hons-acons pat data al)
               (pat->fal (car pat)
                         (car data)
                         (pat->fal (cdr pat) (cdr data) al)))
           al))))


(defsection al->pat
  :parents (patterns)
  :short "@(call al->pat) builds a new data object that is compatible with
<tt>pat</tt>, using the data from <tt>al</tt> and providing the <tt>default</tt>
value for missing keys."

  :long "<p>For instance,</p>

<code>
 (al-&gt;pat '((a (b c)) d)
          '((a . 1) (b . 2) (d . 4))
          'oops)
   --&gt;
 ((1 (2 oops)) 4)
</code>

<p>Note that <tt>al</tt> should be a fast alist.</p>"

  (defun al->pat (pat al default)
    (declare (xargs :guard t))
    (if pat
        (if (atom pat)
            (let ((look (hons-get pat al)))
              (if look (cdr look) default))
          (cons (al->pat (car pat) al default)
                (al->pat (cdr pat) al default)))
      nil))

  (defthm true-listp-al->pat
    (implies (true-listp pat)
             (true-listp (al->pat pat al default)))
    :rule-classes ((:rewrite)
                   (:type-prescription)))

  (defthm len-al->pat
    (implies (true-listp pat)
             (equal (len (al->pat pat al default))
                    (len pat)))))



(defsection pat-flatten
  :parents (patterns)
  :short "Flatten a pattern into a list of atoms (with an accumulator)."
  :long "<p>@(call pat-flatten) flattens <tt>pat</tt>, appending its atoms onto
<tt>acc</tt>, in order.  For instance,</p>

<code>
  (pat-flatten '((a) (b c)) '(x y z))
  --&gt;
  (a b c x y z)
</code>

<p>The accumulator argument is occasionally useful.  But for reasoning, we
rewrite <tt>pat-flatten</tt> into @(see pat-flatten1) with the following
theorem:</p>

@(def pat-flatten-is-pat-flatten1)"

  (defun pat-flatten (pat acc)
    (declare (xargs :guard t))
    (if pat
      (if (atom pat)
          (cons pat acc)
        (pat-flatten (car pat) (pat-flatten (cdr pat) acc)))
    acc)))



(defsection pat-flatten1
  :parents (patterns)
  :short "Flatten a pattern into a list of atoms (without an accumulator)."

  :long "<p>@(call pat-flatten1) is just a simpler flattening function that
does the same thing as @(see pat-flatten) but without an accumulator.  It is
generally convenient to reason about.</p>"

  (defund pat-flatten1 (pat)
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic
         (if pat
             (if (atom pat)
                 (list pat)
               (append (pat-flatten1 (car pat))
                       (pat-flatten1 (cdr pat))))
           nil)
         :exec (pat-flatten pat nil)))

  (local (in-theory (enable pat-flatten1)))

  (defthm pat-flatten-is-pat-flatten1
    (equal (pat-flatten pat acc)
           (append (pat-flatten1 pat) acc)))

  (verify-guards pat-flatten1)

  (defthm true-listp-of-pat-flatten1
    ;; [Jared] I don't understand why I have to have this as a rewrite rule in
    ;; addition to as a type-prescription rule (which would just get inferred
    ;; from the definition anyway).  But, without the :rewrite rule, the
    ;; theorem esim-is-monotonic fails because the rule that rewrites (append x
    ;; nil) to x when (true-listp x) is known doesn't fire.  How can this be???
    (true-listp (pat-flatten1 x))
    :rule-classes ((:type-prescription)
                   (:rewrite)))

  (defthm pat-flatten1-when-atom
    (implies (atom pat)
             (equal (pat-flatten1 pat)
                    (if pat (list pat) nil))))

  (defthm pat-flatten1-of-cons
    (equal (pat-flatten1 (cons x y))
           (append (pat-flatten1 x) (pat-flatten1 y))))

  (defthm pat-flatten1-nonnil
    (not (member-equal nil (pat-flatten1 x)))))


(defsection alist-keys-pat->al
  :extension pat->al

  (defthm alist-keys-pat->al
    (equal (alist-keys (pat->al p1 p2 nil))
           (pat-flatten1 p1))
    :hints(("Goal" :in-theory (enable pat-flatten1)))))



(defsection member-of-pat-flatten
  :parents (patterns)
  :short "@(call member-of-pat-flatten) is an optimized way to ask if
<tt>a</tt> is a member of <tt>(pat-flatten1 pat)</tt>."

  :long "<p>This just avoids actually flattening the pattern, and picks a
function with optimized EQ/EQL/EQUAL testing.</p>"

  (local (in-theory (enable pat-flatten1)))

  (defun member-eq-of-pat-flatten (a pat)
    (declare (xargs :guard (symbolp a)))
    (mbe :logic (if (member-equal a (pat-flatten1 pat))
                    t
                  nil)
         :exec
         (if pat
             (if (atom pat)
                 (eq a pat)
               (or (member-eq-of-pat-flatten a (car pat))
                   (member-eq-of-pat-flatten a (cdr pat))))
           nil)))

  (defun member-eql-of-pat-flatten (a pat)
    (declare (xargs :guard (eqlablep a)))
    (mbe :logic (if (member-equal a (pat-flatten1 pat))
                    t
                  nil)
         :exec
         (if pat
             (if (atom pat)
                 (eql a pat)
               (or (member-eql-of-pat-flatten a (car pat))
                   (member-eql-of-pat-flatten a (cdr pat))))
           nil)))

  (defun member-equal-of-pat-flatten-aux (a pat)
    ;; -aux to discourage people from calling it directly
    (declare (xargs :guard t))
    (mbe :logic (if (member-equal a (pat-flatten1 pat))
                    t
                  nil)
         :exec
         (if pat
             (if (atom pat)
                 (equal a pat)
               (or (member-equal-of-pat-flatten-aux a (car pat))
                   (member-equal-of-pat-flatten-aux a (cdr pat))))
           nil)))

  (defun member-of-pat-flatten (a pat)
    (declare (xargs :guard t))
    (mbe :logic (if (member-equal a (pat-flatten1 pat))
                    t
                  nil)
         :exec (cond ((symbolp a)
                      (member-eq-of-pat-flatten a pat))
                     ((or (acl2-numberp a)
                          (characterp a))
                      (member-eql-of-pat-flatten a pat))
                     (t
                      (member-equal-of-pat-flatten-aux a pat))))))


(defsection assoc-pat->al
  :parents (patterns)
  :short "@(call assoc-pat->al) is an optimized way to look up a particular
key, given some pattern and data."

  :long "<p>This is logically just a lookup in the alist constructed by @(see
pat->al), but we avoid constructing the alist.</p>"

  (defun assoc-pat->al (key pat data)
    (declare (xargs :guard (data-for-patternp pat data)))
    (mbe :logic (hons-assoc-equal key (pat->al pat data nil))
         :exec
         (if pat
             (if (atom pat)
                 (if (equal key pat)
                     (cons pat data)
                   nil)
               (or (assoc-pat->al key (car pat) (car data))
                   (assoc-pat->al key (cdr pat) (cdr data))))
           nil))))
