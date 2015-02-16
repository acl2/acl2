; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")
(include-book "../../util/defs")
(include-book "../../util/echars")
(local (include-book "../../util/arithmetic"))


(defsection defchar
  :parents (lexer)
  :short "Introduce lexing utilites from a character recognizer."

  :long "<p>@('Defchar') is a macro for quickly introducing character classes
and functions to read them.</p>

<h5>General Form</h5>

@({
    (defchar basename criteria
      [:prefix prefix]
      [:pkg pkg]
      [:parents parents]
      [:short short]
      [:long long])
})

<h5>Example</h5>

@({
    (defchar whitespace
      (or (eql x #\Space)
          (eql x #\Tab)
          (eql x #\Page)
          (eql x #\Newline)))
})

<p>The @('basename'), @('prefix'), and @('pkg') are each symbols which
influence the names of the new definitions and theorems we introduce.  In
particular,</p>

<ul>

<li>The @('basename') is the name of the main part of the new character type
you are introducing.</li>

<li>The @('prefix') is prepended to the symbol names we generate, and defaults
to the symbol @(''vl-').  For instance, in the above example, the
single-character recognizer will be named @('vl-whitespace-p').</li>

<li>The @('pkg') is used to control what package the new functions and theorems
are defined in.  It defaults to @(''VL2014::foo'), so in the above example the
symbols are introduced in the @('VL2014::') package.  </li>

</ul>

<p>Finally, the @('criteria') is some term about the variable @('x').  You may
assume that @('x') is an ordinary @('characterp'), and specify what kinds of
characters you want using functions such as @('eql') and @('char<=').</p>

<p>Calling this macro introduces the following functions:</p>

<ul>

<li>@('(PKG::PREFIX-BASENAME-P X)'), recognizes those @('characterp')s which
satsify @('criteria'),</li>

<li>@('(PKG::PREFIX-BASENAME-ECHAR-P X)'), recognizes those @(see vl-echar-p)s
whose character satisfies @('criteria'),</li>

<li>@('(PKG::PREFIX-BASENAME-LIST-P X)'), recognizes those
@('character-listp')s where every character satisfies @('criteria'),</li>

<li>@('(PKG::PREFIX-READ-WHILE-BASENAME ECHARS)') splits @('echars') into a
prefix and remainder, where @('prefix') is the longest leading list of
characters that satisfy @('criteria').</li>

</ul>

<p>It also introducs a number of theorems, enumerated in @(see
vl-read-while-ctype).</p>")

(local (xdoc::set-default-parents defchar))


(defsection vl-ctype-p
  :short "Generic stub for a character type recognizer."
  :long "<p>This is the basis of the generic theory that @(see defchar)
instantiates.  Typically this is standing in for a function that recognizes
some particular set of characters, say digits.  The only constraints are
that:</p>
<ul>
<li>The function must be Boolean-valued, and</li>
<li>It must <i>not</i> tolerate @('nil').</li>
</ul>

 @(def vl-ctype-p)"

  (encapsulate
    (((vl-ctype-p *) => *))
    (local (defun vl-ctype-p (x)
             (eql x #\a)))

    (defrule vl-ctype-p-of-nil
      (not (vl-ctype-p nil)))

    (defrule booleanp-of-vl-ctype-p
      (booleanp (vl-ctype-p x))
      :rule-classes :type-prescription)))

(deflist vl-ctype-list-p (x)
  (vl-ctype-p x)
  :elementp-of-nil nil)

(define vl-read-while-ctype-impl ((echars vl-echarlist-p) acc)
  :parents (vl-read-while-ctype)
  (cond ((atom echars)
         (mv acc echars))
        ((vl-ctype-p (vl-echar->char (car echars)))
         (vl-read-while-ctype-impl (cdr echars) (cons (car echars) acc)))
        (t
         (mv acc echars))))

(define vl-read-while-ctype
  :short "Match as many characters of some type as possible."
  ((echars vl-echarlist-p))
  :returns (mv (prefix "All of the leading characters from @('echars') that
                        satisfy @(see vl-ctype-p).")
               (remainder "The remaining characters afterwards."))
  :long "<p>This is a generic function.  See @(see defchar) for a convenient
way to instantiate this function, and its corresponding theory, for your own
character recognizers.</p>"
  :verify-guards nil
  (mbe :logic (b* (((when (atom echars))
                    (mv nil echars))
                   ((unless (vl-ctype-p (vl-echar->char (car echars))))
                    (mv nil echars))
                   ((mv prefix remainder)
                    (vl-read-while-ctype (cdr echars))))
                (mv (cons (car echars) prefix) remainder))
       :exec (b* (((mv prefix-rev remainder)
                   (vl-read-while-ctype-impl echars nil)))
               (mv (reverse prefix-rev) remainder)))
  ///
  (defrule prefix-of-vl-read-while-ctype
    (and (true-listp (mv-nth 0 (vl-read-while-ctype echars)))
         (implies (force (vl-echarlist-p echars))
                  (vl-echarlist-p (mv-nth 0 (vl-read-while-ctype echars)))))
    :rule-classes ((:rewrite)
                   (:type-prescription :corollary
                                       (true-listp (mv-nth 0 (vl-read-while-ctype echars))))))

  (defrule equiv-of-vl-read-while-ctype-impl
    (and (equal (len (vl-read-while-ctype-impl echars acc)) 2)
         (implies (true-listp acc)
                  (and (true-listp (mv-nth 0 (vl-read-while-ctype-impl echars acc)))
                       (equal (mv-nth 0 (vl-read-while-ctype-impl echars acc))
                              (revappend (mv-nth 0 (vl-read-while-ctype echars)) acc))
                       (equal (mv-nth 1 (vl-read-while-ctype-impl echars acc))
                              (mv-nth 1 (vl-read-while-ctype echars))))))
    :enable vl-read-while-ctype-impl)

  (verify-guards vl-read-while-ctype)

  (defrule remainder-of-vl-read-while-ctype
    (and (equal (true-listp (mv-nth 1 (vl-read-while-ctype echars)))
                (true-listp echars))
         (implies (force (vl-echarlist-p echars))
                  (vl-echarlist-p (mv-nth 1 (vl-read-while-ctype echars)))))
    :rule-classes ((:rewrite)
                   (:type-prescription
                    :corollary
                    (implies (true-listp echars)
                             (true-listp (mv-nth 1 (vl-read-while-ctype echars)))))))

  (defrule prefix-of-vl-read-while-ctype-when-vl-ctype-p
    (implies (vl-ctype-p (vl-echar->char (car echars)))
             (iff (mv-nth 0 (vl-read-while-ctype echars))
                  (consp echars))))

  (defrule vl-read-while-ctype-sound
    ;; This says that all the characters vl-read-while-ctype reads are, indeed,
    ;; vl-ctype-p's.  In other words, it reads only good characters.
    (vl-ctype-list-p (vl-echarlist->chars (mv-nth 0 (vl-read-while-ctype echars)))))

  (defrule vl-read-while-ctype-complete
    ;; This says that if vl-read-while-ctype didn't read all the entire stream,
    ;; it leaves a non vl-ctype-p at the front.  In other words, it reads
    ;; exactly as far as it can.
    (equal (vl-ctype-p (vl-echar->char (car (mv-nth 1 (vl-read-while-ctype echars)))))
           (if (consp (mv-nth 1 (vl-read-while-ctype echars)))
               nil
             (vl-ctype-p (vl-echar->char nil)))))

  (defrule append-of-vl-read-while-ctype
    (equal (append (mv-nth 0 (vl-read-while-ctype echars))
                   (mv-nth 1 (vl-read-while-ctype echars)))
           echars))

  (defrule no-change-loser-of-vl-read-while-ctype
    (implies (not (mv-nth 0 (vl-read-while-ctype echars)))
             (equal (mv-nth 1 (vl-read-while-ctype echars))
                    echars)))

  (defrule acl2-count-of-vl-read-while-ctype-weak
    (<= (acl2-count (mv-nth 1 (vl-read-while-ctype echars)))
        (acl2-count echars))
    :rule-classes ((:rewrite) (:linear)))

  (defrule acl2-count-of-vl-read-while-ctype-strong
    (implies (mv-nth 0 (vl-read-while-ctype echars))
             (< (acl2-count (mv-nth 1 (vl-read-while-ctype echars)))
                (acl2-count echars)))
    :rule-classes ((:rewrite) (:linear))))


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
                              (vl-read-while-ctype-impl ,read-while-impl))))
      `(defsection ,char-p
         ,@(and parents `(:parents ,parents))
         ,@(and short   `(:short ,short))
         ,@(and long    `(:long ,long))

         (set-verify-guards-eagerness 2) ;; implicitly local
         (logic)

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

         (defrule ,(mksym (cat "PREFIX-OF-" readwhilestr) pkg)
           (and (true-listp (mv-nth 0 (,read-while echars)))
                (implies (force (vl-echarlist-p echars))
                         (vl-echarlist-p (mv-nth 0 (,read-while echars)))))
           :rule-classes ((:rewrite)
                          (:type-prescription
                           :corollary (true-listp (mv-nth 0 (,read-while echars)))))
           :use ((:functional-instance prefix-of-vl-read-while-ctype . ,fi-pairs)))

         (local (defrule ,(mksym (cat "EQUIV-OF-" readwhileimpstr) pkg)
                  (and (equal (len (,read-while-impl echars acc)) 2)
                       (implies (true-listp acc)
                                (and (true-listp (mv-nth 0 (,read-while-impl echars acc)))
                                     (equal (mv-nth 0 (,read-while-impl echars acc))
                                            (revappend (mv-nth 0 (,read-while echars)) acc))
                                     (equal (mv-nth 1 (,read-while-impl echars acc))
                                            (mv-nth 1 (,read-while echars))))))
                  :use ((:functional-instance equiv-of-vl-read-while-ctype-impl . ,fi-pairs))))

         (verify-guards ,(intern-in-package-of-symbol
                          (str::cat (symbol-name read-while) acl2::*inline-suffix*)
                          read-while))

         (defrule ,(mksym (cat "REMAINDER-OF-" readwhilestr) pkg)
           (and (equal (true-listp (mv-nth 1 (,read-while echars)))
                       (true-listp echars))
                (implies (vl-echarlist-p echars)
                         (vl-echarlist-p (mv-nth 1 (,read-while echars)))))
           :rule-classes ((:rewrite)
                          (:type-prescription
                           :corollary
                           (implies (true-listp echars)
                                    (true-listp (mv-nth 1 (,read-while echars))))))
           :use ((:functional-instance remainder-of-vl-read-while-ctype . ,fi-pairs)))

         (defrule ,(mksym (cat "PREFIX-OF-" readwhilestr "-WHEN-" namestr) pkg)
           (implies (,char-p (vl-echar->char (car echars)))
                    (iff (mv-nth 0 (,read-while echars))
                         (consp echars)))
           :use ((:functional-instance prefix-of-vl-read-while-ctype-when-vl-ctype-p . ,fi-pairs)))

         (defrule ,(mksym (cat readwhilestr "-SOUND") pkg)
           (,char-list-p (vl-echarlist->chars (mv-nth 0 (,read-while echars))))
           :use ((:functional-instance vl-read-while-ctype-sound . ,fi-pairs)))

         (defrule ,(mksym (cat readwhilestr "-COMPLETE") pkg)
           (equal (,char-p (vl-echar->char (car (mv-nth 1 (,read-while echars)))))
                  (if (consp (mv-nth 1 (,read-while echars)))
                      nil
                    (,char-p (vl-echar->char nil))))
           :use ((:functional-instance vl-read-while-ctype-complete . ,fi-pairs)))

         (defrule ,(mksym (cat "APPEND-OF-" readwhilestr) pkg)
           (equal (append (mv-nth 0 (,read-while echars))
                          (mv-nth 1 (,read-while echars)))
                  echars)
           :use ((:functional-instance append-of-vl-read-while-ctype . ,fi-pairs)))

         (defrule ,(mksym (cat "NO-CHANGE-LOSER-OF-" readwhilestr) pkg)
           (implies (not (mv-nth 0 (,read-while echars)))
                    (equal (mv-nth 1 (,read-while echars))
                           echars))
           :use ((:functional-instance no-change-loser-of-vl-read-while-ctype . ,fi-pairs)))

         (defrule ,(mksym (cat "ACL2-COUNT-OF-" readwhilestr "-WEAK") pkg)
           (<= (acl2-count (mv-nth 1 (,read-while echars)))
               (acl2-count echars))
           :rule-classes ((:rewrite) (:linear))
           :use ((:functional-instance acl2-count-of-vl-read-while-ctype-weak . ,fi-pairs)))

         (defrule ,(mksym (cat "ACL2-COUNT-OF-" readwhilestr "-STRONG") pkg)
           (implies (mv-nth 0 (,read-while echars))
                    (< (acl2-count (mv-nth 1 (,read-while echars)))
                       (acl2-count echars)))
           :rule-classes ((:rewrite) (:linear))
           :use ((:functional-instance acl2-count-of-vl-read-while-ctype-strong . ,fi-pairs)))

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
    parents short long))


(local
 (encapsulate
  ()
  ;; Simple tests to make sure defchar is working
  (defchar nine
    (eql x #\9))
  (defchar not-nine
    (not (eql x #\9)))))

