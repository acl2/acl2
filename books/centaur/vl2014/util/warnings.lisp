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
(include-book "defs")
(include-book "defsort/remove-dups" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(local (include-book "arithmetic"))
(local (std::add-default-post-define-hook :fix))
(local (xdoc::set-default-parents warnings))

(defprod vl-warning
  :short "Fundamental warning object used throughout @(see VL2014)."
  :tag :vl-warning
  :layout :alist

  ((type symbolp :rule-classes :type-prescription
         "A symbol, most often a keyword symbol, that describes very broadly
          what kind of warning this is.  There is no particular discipline or
          strategy for assigning types to warnings, but the basic goal is to be
          able to use these types to filter out or group up similar warnings.")

   (fatalp booleanp :rule-classes :type-prescription
           "Indicates whether this error is so severe that the module ought to
            be thrown away and not subjected to further translation.  See the
            general discussion in @(see warnings) for more information on how
            this is used.")

   (msg  stringp :rule-classes :type-prescription
         "A more detailed message describing what went wrong.  This string
          should be acceptable to @(see vl-fmt); it is similar to the \"format
          strings\" used by ACL2's @(see cw) function, but there are some
          important differences, e.g., not all @(see fmt) directives are
          supported, and extra Verilog-specific directives are available.")

   (args true-listp :rule-classes :type-prescription
         "Arguments that will be composed with the tilde directives in @('msg')
          when the warning is displayed to the user.  That is, a directive like
          @('~x0') refers to the first argument, @('~x1') to the second, etc.")

   (fn symbolp :rule-classes :type-prescription
       "A symbol, intended to be the name of the function that caused the
        warning.  This is intended to be useful for VL debugging, to help make
        the source of the warning more apparent.  Only good discipline (and
        handy macros) ensure that this is correctly reported.")))

(fty::deflist vl-warninglist
  :elt-type vl-warning-p
  :elementp-of-nil nil
  :true-listp nil
  ///
  (defthm vl-warninglist-p-of-remove-adjacent-duplicates
    (implies (force (vl-warninglist-p x))
             (vl-warninglist-p (acl2::remove-adjacent-duplicates x)))
    :hints(("Goal" :in-theory (enable acl2::remove-adjacent-duplicates)))))

(defprojection vl-warninglist->types ((x vl-warninglist-p))
  :returns (types symbol-listp)
  (vl-warning->type x))

(defsection ok
  :short "A convenient shorthand for calling @(see vl-warninglist-fix)."
  :long "<p>@('(ok)') is just syntactic sugar for:</p>

@({
   (vl-warninglist-fix warnings)
})

<p>This is often useful as a base case in functions that sometimes create
warnings.  The name of the warnings accumulator to fix can also be specified,
e.g.,:</p>

@({
    (ok acc) == (vl-warninglist-fix acc)
})

@(def ok)"

  (defmacro ok (&optional (warnings 'warnings))
    `(vl-warninglist-fix ,warnings))

  (defthm ok-correct
    (and (equal (ok x) (vl-warninglist-fix x))
         (equal (ok) (vl-warninglist-fix warnings)))
    :rule-classes nil))

(defsection warn
  :short "Extend a @(see warnings) accumulator with a non-fatal warning."
  :long "<p>Syntax:</p>

@({
    (warn [:type type]
          [:msg msg]
          [:args args]
          [:fn fn]         ;; defaults to __function__
          [:acc warnings]  ;; defaults to warnings
          )
       -->
    warnings'
})

<p>This macro builds a new, <b>non-fatal</b> warning @('w') from the given
@('type'), @('msg'), @('args'), and @('fn'), then conses @('w') onto the @(see
warnings) accumulator @('acc').</p>

<p>See also @(see fatal); it is identical except that it builds fatal
warnings.</p>

<p>We make use of a few interfacing tricks:</p>

<ul>

<li>@('acc') defaults to @('warnings') because we often use @('warnings') as
the name of the warnings accumulator we are working with.  That is, as long as
your warnings accumulator is named @('warnings'), you don't have to give an
@('acc') argument.</li>

<li>@('fn') defaults to @('__function__').  Macros like @(see define) often
bind this symbol to the name of the current function, so if you are using a
macro like this you don't have to give a @('fn') argument.  But you will need
to explicitly give a function name when using raw @(see defun).</li>

<li>We cons the new warning not onto @('acc'), but instead onto
@('(vl-warninglist-fix acc)').  This ensures that code written using @('warn')
can unconditionally produce @(see vl-warninglist-p)s, without needing to do
explicit fixing.</li>

</ul>"

  (defmacro warn (&key type msg args
                       (fn '__function__)
                       (acc 'warnings))
    `(cons (make-vl-warning :type ,type
                            :msg ,msg
                            :args ,args
                            :fatalp nil
                            :fn ,fn)
           (vl-warninglist-fix ,acc))))

(defsection fatal
  :short "Extend a @(see warnings) accumulator with a fatal warning."
  :long "<p>See @(see warn); @('fatal') is identical except that it produces
fatal warnings instead of non-fatal warnings.</p>"

  (defmacro fatal (&key type msg args
                        (fn '__function__)
                        (acc 'warnings))
    `(cons (make-vl-warning :type ,type
                            :msg ,msg
                            :args ,args
                            :fatalp t
                            :fn ,fn)
           (vl-warninglist-fix ,acc))))

(define vl-warning-< ((x vl-warning-p)
                      (y vl-warning-p))
  :parents (vl-warning-sort)
  :short "A basic, rather arbitrary ordering for warnings."
  (b* (((vl-warning x) x)
       ((vl-warning y) y)

       ((when (symbol< x.type y.type)) t)
       ((unless (eq x.type y.type)) nil)

       ((when (<< x.fn y.fn)) t)
       ((unless (eq x.fn y.fn)) nil)

       ((when (string< x.msg y.msg)) t)
       ((unless (equal x.msg y.msg)) nil)

       ((when (<< x.args y.args)) t)
       ((unless (equal x.args y.args)) nil))

    (<< x.fatalp y.fatalp))

  ///
  (defthm vl-warning-<-transitive
    (implies (and (vl-warning-< x y)
                  (vl-warning-< y z))
             (vl-warning-< x z))
    :hints(("Goal" :in-theory (enable string<)))))

(defsection vl-warning-sort
  :short "Mergesort warnings using @(see vl-warning-<)"

  (ACL2::defsort :comparablep vl-warning-p
                 :compare< vl-warning-<
                 :prefix vl-warning)

  ;; Ugh, stupid defsort.  I should be able to rename these functions.
  (defthm vl-warning-list-p-is-vl-warninglist-p
    (equal (vl-warning-list-p x)
           (vl-warninglist-p x))
    :hints(("Goal" :in-theory (enable vl-warning-list-p))))

  (defthm vl-warninglist-p-of-vl-warning-sort
    (implies (force (vl-warninglist-p x))
             (vl-warninglist-p (vl-warning-sort x)))
    :hints(("Goal"
            :in-theory (disable vl-warning-sort-creates-comparable-listp)
            :use ((:instance vl-warning-sort-creates-comparable-listp (ACL2::x x))))))

  ;; BOZO this is pretty gross, and should probably be built into defsort.

  (local (defthm l0
           (implies (< 0 (duplicity a x))
                    (consp x))))

  (local (defthm l1
           (implies (consp x)
                    (consp (vl-warning-sort x)))
           :hints(("Goal"
                   :in-theory (disable l0
                                       vl-warning-sort-preserves-duplicity)
                   :use ((:instance l0 (a (car x)))
                         (:instance vl-warning-sort-preserves-duplicity
                          (acl2::a (car x))
                          (acl2::x x)))))))

  (local (defthm l2
           (implies (equal (duplicity (car x) x) 0)
                    (atom x))))

  (local (defthm l3
           (implies (consp (vl-warning-sort x))
                    (consp x))
           :hints(("Goal"
                   :in-theory (disable l0
                                       vl-warning-sort-preserves-duplicity)
                   :use ((:instance l2
                          (x (vl-warning-sort x)))
                         (:instance vl-warning-sort-preserves-duplicity
                          (acl2::a (car (vl-warning-sort x)))
                          (acl2::x x)))))))

  (defthm consp-of-vl-warning-sort
    (equal (consp (vl-warning-sort x))
           (consp x))
    :hints(("Goal" :cases ((consp x))))))

(define vl-clean-warnings
  :parents (warnings clean-warnings)
  :short "Sort and remove duplicates from a list of warnings."
  ((x vl-warninglist-p))
  :returns (ans vl-warninglist-p)
  (ACL2::remove-adjacent-duplicates
   (vl-warning-sort
    (list-fix
     (vl-warninglist-fix x))))
  ///
  (defthm vl-clearn-warnings-under-iff
    (iff (vl-clean-warnings x)
         (consp x))))

(define vl-remove-warnings
  :short "Remove warnings of certain types."
  ((types symbol-listp     "Types of warnings to remove.")
   (x     vl-warninglist-p "The list of warnings to filter."))
  :returns (ans vl-warninglist-p)
  :long "<p>This can be useful to filter out mundane warnings that you do not
want to bother the user with.</p>"
  (cond ((atom x)
         nil)
        ((member (vl-warning->type (car x)) types)
         (vl-remove-warnings types (cdr x)))
        (t
         (cons (vl-warning-fix (car x))
               (vl-remove-warnings types (cdr x))))))

(define vl-keep-warnings
  :short "Keep only warnings of certain types."
  ((types symbol-listp     "Types of warnings to keep.")
   (x     vl-warninglist-p "The list of warnings to filter."))
  :returns (ans vl-warninglist-p :hyp (force (vl-warninglist-p x)))
  :long "<p>This can be useful to highlight certain warnings that are of
particular interest.</p>"
  (cond ((atom x)
         nil)
        ((member (vl-warning->type (car x)) types)
         (cons (vl-warning-fix (car x))
               (vl-keep-warnings types (cdr x))))
        (t
         (vl-keep-warnings types (cdr x)))))

(define vl-some-warning-fatalp
  :short "Check if any warning is marked as fatal."
  ((x vl-warninglist-p))
  :returns (bool booleanp :rule-classes :type-prescription)
  (cond ((atom x)
         nil)
        ((vl-warning->fatalp (car x))
         t)
        (t
         (vl-some-warning-fatalp (cdr x))))
  ///
  (defthm vl-some-warning-fatalp-when-not-consp
    (implies (not (consp x))
             (equal (vl-some-warning-fatalp x)
                    nil)))

  (defthm vl-some-warning-fatalp-of-cons
    (equal (vl-some-warning-fatalp (cons a x))
           (or (if (vl-warning->fatalp a) t nil)
               (vl-some-warning-fatalp x))))

  (defthm vl-some-warning-fatalp-of-append
    (equal (vl-some-warning-fatalp (append x y))
           (or (vl-some-warning-fatalp x)
               (vl-some-warning-fatalp y))))

  (defthm vl-some-warning-fatalp-of-list-fix
    (equal (vl-some-warning-fatalp (list-fix x))
           (vl-some-warning-fatalp x)))

  (local (defthm l0
           (implies (and (vl-warning->fatalp a)
                         (member-equal a x))
                    (vl-some-warning-fatalp x))))

  (local (defthm l1
           (implies (and (subsetp-equal x y)
                         (vl-some-warning-fatalp x))
                    (vl-some-warning-fatalp y))
           :hints(("Goal" :in-theory (enable subsetp-equal)))))

  (defcong set-equiv equal (vl-some-warning-fatalp x) 1
    :event-name vl-some-warning-fatalp-preserves-set-equiv
    :hints(("Goal"
            :cases ((vl-some-warning-fatalp x))
            :in-theory (enable set-equiv)
            :do-not-induct t))))

(define vl-some-warning-of-type-p
  :short "Check if there are any warnings of certain types."
  ((types symbol-listp)
   (x     vl-warninglist-p))
  :returns (bool booleanp :rule-classes :type-prescription)
  :long "<p>Note: we just leave this function enabled.</p>"
  (mbe :logic
       (intersectp-equal types (vl-warninglist->types x))
       :exec
       (cond ((atom x)
              nil)
             ((member (vl-warning->type (car x)) types)
              t)
             (t
              (vl-some-warning-of-type-p types (cdr x))))))

