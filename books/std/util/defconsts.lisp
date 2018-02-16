; Standard Utilities Library
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

(in-package "STD")
(include-book "xdoc/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
;; removed these because it made for a long critial path (~30 sec) for a very basic book.  Now ~3 sec.
;; (local (include-book "std/strings/explode-atom" :dir :system))
;; (local (include-book "../typed-lists/symbol-listp"))

(defxdoc defconsts
  :parents (std/util defconst)
  :short "An enhanced variant of @(see defconst) that lets you use @(see state)
and other @(see acl2::stobj)s, and directly supports calling @(see
mv)-returning functions to define multiple constants."

  :long "<p>Examples:</p>

@({
 (include-book \"std/util/defconsts\" :dir :system)

 (defconsts *foo* 1)
 (defconsts (*foo*) 1)
 (defconsts (*foo* *bar*) (mv 1 2))
 (defconsts (*foo* *bar* &) (mv 1 2 3))

 (defconsts (& *shell* state) (getenv$ \"SHELL\" state))

 (defconsts (*hundred* state)
   (mv-let (col state)
           (fmt \"Hello, world!\" nil *standard-co* state nil)
           (declare (ignore col))
           (mv 100 state)))
})

<p>General form:</p>
@({
 (defconsts names body)
})

<p>where @('names') may be a single symbol or a list of @('n') symbols, and
body is a form that returns @('n') values.</p>

<p>Each symbol in @('names') should either be:</p>

<ul>
<li>A \"starred\" name like @('*foo*'),</li>
<li>The name of a stobj (e.g., @(see state)), or</li>
<li>The symbol @('&'), which means \"ignore this return value.\"</li>
</ul>

<p>We introduce a @(see defconst) form that binds each starred name to the
corresponding value returned by @('body').</p>

<h3>Defconst versus Defconsts</h3>

<p><color rgb='#ff0000'><b>NOTE</b></color>: @('defconsts') differs from @(see
defconst) in an important way.  When you use these forms in a book:</p>

<ul>

<li>Results from @('defconsts') are <b>stored in the @(see
acl2::certificate)</b>, while</li>

<li>Results from @('defconst') are <b>recomputed at @(see include-book)
time</b>.</li>

</ul>

<p>This has some performance implications:</p>

<ul>

<li>Computations that take a long time but produce \"small\" results (e.g.,
checking the primality of a large number) might best be done as @('defconsts')
to avoid repeating the computation.</li>

<li>Computations that are fast but produce \"large\" results (e.g.,
@('(make-list 10000)')), might best be done as @('defconst'), to avoid storing
this large list in the certificate.</li>

</ul>")

(defun defconsts-check-names (x)
  ;; Same as symbol-listp but causes errors
  (declare (xargs :guard t))
  (mbe :logic (symbol-listp x)
       :exec
       (if (atom x)
           (or (not x)
               (er hard? 'defconsts-check-names "Names are not a true-listp."))
         (and (or (symbolp (car x))
                  (er hard? 'defconsts-check-names
                      "Not a valid name for defconsts: ~x0.~%" (car x)))
              (defconsts-check-names (cdr x))))))

(defund defconsts-const-name-p (x)
  ;; Recognize *foo*
  (declare (xargs :guard (symbolp x)))
  (let* ((name (symbol-name x))
         (nl   (length name)))
    (and (>= nl 3)
         (eql (char name 0) #\*)
         (eql (char name (- nl 1)) #\*))))

(defund defconsts-collect-stobj-names (x)
  ;; Collect names other than *foo* and &.
  (declare (xargs :guard (symbol-listp x)))
  (cond ((atom x)
         nil)
        ((or (defconsts-const-name-p (car x))
             (eq (car x) '&))
         (defconsts-collect-stobj-names (cdr x)))
        (t
         (cons (car x)
               (defconsts-collect-stobj-names (cdr x))))))

(defsection defconsts-strip-stars
  ;; (*foo* *bar* baz) --> (foo bar baz)

  (defund defconsts-strip-stars1 (x)
    ;; *foo* --> foo
    (declare (xargs :guard (symbolp x)
                    :guard-hints(("Goal" :in-theory (enable defconsts-const-name-p)))))
    (if (defconsts-const-name-p x)
        (let* ((name    (symbol-name x))
               (nl      (length name))
               (nostars (subseq name 1 (- nl 1))))
          (intern-in-package-of-symbol nostars x))
      (and (mbt (symbolp x))
           x)))

  (defund defconsts-strip-stars (x)
    (declare (xargs :guard (symbol-listp x)))
    (if (atom x)
        nil
      (cons (defconsts-strip-stars1 (car x))
            (defconsts-strip-stars (cdr x)))))

  (local (in-theory (enable defconsts-strip-stars)))

  (defthm symbol-listp-of-defconsts-strip-stars
    (symbol-listp (defconsts-strip-stars x)))

  (defthm len-of-defconsts-strip-stars
    (equal (len (defconsts-strip-stars x))
           (len x))))


(defsection defconsts-make-n-fresh-symbols

  (local (defthm character-listp-of-explode-nonneg
           (implies (character-listp acc)
                    (character-listp (explode-nonnegative-integer x base acc)))
           :hints(("Goal" :in-theory (enable explode-nonnegative-integer)))))

  (defund defconsts-make-n-fresh-symbols (n)
    (declare (xargs :guard (natp n)))
    (if (zp n)
        nil
      (cons (intern-in-package-of-symbol
             (concatenate 'string "defconsts-ignore-"
                          (coerce (explode-atom n 10) 'string))
             'foo)
            (defconsts-make-n-fresh-symbols (- n 1)))))

  (local (in-theory (enable defconsts-make-n-fresh-symbols)))

  (defthm symbol-listp-of-defconsts-make-n-fresh-symbols
    (symbol-listp (defconsts-make-n-fresh-symbols n)))

  (defthm len-of-defconsts-make-n-fresh-symbols
    (equal (len (defconsts-make-n-fresh-symbols n))
           (nfix n))))


(defsection defconsts-replace-amps
  ;; (*foo* *bar* & & baz) --> (*foo* *bar* fresh-syms3 fresh-syms4 baz)

  (defund defconsts-replace-amps (x fresh-syms)
    (declare (xargs :guard (and (symbol-listp x)
                                (symbol-listp fresh-syms)
                                (= (len fresh-syms) (len x)))))
    (cond ((atom x)
           nil)
          ((eq (car x) '&)
           (cons (car fresh-syms)
                 (defconsts-replace-amps (cdr x) (cdr fresh-syms))))
          (t
           (cons (car x)
                 (defconsts-replace-amps (cdr x) (cdr fresh-syms))))))

  (local (in-theory (enable defconsts-replace-amps)))

  (defthm symbol-listp-of-defconsts-replace-amps
    (implies (and (symbol-listp x)
                  (symbol-listp fresh-syms))
             (symbol-listp (defconsts-replace-amps x fresh-syms)))))


(defund defconsts-make-defconsts (x)
  ;; (*foo* *bar* & & baz)
  ;;   -->
  ;; ((list 'defconst '*foo* foo)
  ;;  (list 'defconst '*bar* bar))
  (declare (xargs :guard (symbol-listp x)))
  (cond ((atom x)
         nil)
        ((defconsts-const-name-p (car x))
         (cons `(list 'defconst ',(car x)
                      (list 'quote ,(defconsts-strip-stars1 (car x))))
               (defconsts-make-defconsts (cdr x))))
        (t
         (defconsts-make-defconsts (cdr x)))))

(defun check-stobjs (stobjs wrld acc)
  (declare (xargs :guard (and (plist-worldp wrld)
                              (true-listp acc))))
  (cond ((atom stobjs)
         (and acc
              (er hard? 'defconsts
                  "The symbol~#0~[ ~&0 is~/s ~&0 are~] illegal for defconsts. ~
                   ~ See :DOC defconsts."
                  (reverse acc))))
        ((acl2::stobjp (car stobjs) t wrld)
         (check-stobjs (cdr stobjs) wrld acc))
        (t (check-stobjs (cdr stobjs) wrld (cons (car stobjs) acc)))))

(local (defthm symbolp-car-when-symbol-listp
         (implies (symbol-listp x)
                  (symbolp (car x)))))

(local (defthm symbol-listp-of-set-diff
         (implies (symbol-listp x)
                  (symbol-listp (set-difference-eq x y)))))

(local (defthm symbol-listp-of-remove
         (implies (symbol-listp x)
                  (symbol-listp (remove-eq y x)))))

(local (defthm len-revappend
         (Equal (len (revappend x y))
                (+ (len x) (len y)))))

(local (defthm symbol-listp-revappend
         (implies (and (symbol-listp x)
                       (symbol-listp y))
                  (symbol-listp (revappend x y)))))

(defund defconsts-fn (consts body)
  (declare (xargs :guard t))
  (b* ( ;; Goofy thing to allow (defconsts *foo* ...) instead of (defconsts (*foo*) ...)
       (consts (if (atom consts)
                   (list consts)
                 consts))

       ((unless (defconsts-check-names consts))
        nil)

       (nconsts (len consts))
       (fresh   (reverse (defconsts-make-n-fresh-symbols nconsts)))

       (illegal (intersection-eq fresh consts))
       ((when illegal)
        (er hard? 'defconsts "Illegal to use ~&0.~%" illegal))

       ;; Make symbols to bind with let/mv-let:
       ;;  - remove stars from constants to introduce
       ;;  - replace & with fresh symbols
       (star-free (defconsts-strip-stars consts))
       (amp-free  (defconsts-replace-amps star-free fresh))

       ;; Make "ignore" declaration for any fresh vars we introduced:
       (temps     (intersection-eq amp-free fresh))
       (idecl     (and temps `((declare (ignore . ,temps)))))

       ;; Actual list of things to introduce:
       (cmds     (defconsts-make-defconsts consts))

       (event    (if cmds
                     `(list 'progn ,@cmds)
                   ''(value-triple :empty-defconsts)))
       (event    `(list 'with-output :off '(event) ,event))

       ;; If there are any stobjs, we need to return
       ;;    (mv nil '(progn (defconst ...)) state ... stobjs ...)
       (stobjs         (defconsts-collect-stobj-names consts))
       (stobjs-nostate (remove 'state stobjs))
       (ret            (if stobjs
                           (append (list 'mv nil event 'state)
                                   stobjs-nostate)
                         event))

       ;; We now generate a nice summary string
       ;; real-syms is (*foo* *bar* ...) with no stobjs and no amps.
       (real-syms (set-difference-eq (remove '& consts) stobjs))
       (real1     (car real-syms))
       (dc        (symbol-name 'defconsts))
       (summary   (cond ((atom real-syms)
                         ;; Just stobjs or nothing, we just elide everything
                         (concatenate 'string
                                      "(" dc " ...)"))
                        ((atom (cdr consts))
                         ;; Just *foo* and no other args
                         (concatenate 'string
                                      "(" dc " " (symbol-name real1) " ...)"))
                        ((equal real1 (car consts))
                         ;; *foo* is first but there are other args
                         (concatenate 'string
                                      "(" dc " (" (symbol-name real1) " ...) ...)"))
                        ((equal (car (last consts)) real1)
                         ;; *foo* is the only real arg, and comes last
                         (concatenate 'string
                                      "(" dc " (... " (symbol-name real1) ") ...)"))
                        (t
                         ;; *foo* is neither first nor last
                         (concatenate 'string
                                      "(" dc " (... " (symbol-name real1) "...) ...)"))))

       ;; Use let or mv-let depending on how many constants there are.
       (form (if (= (len consts) 1)
                 `(let ((,(car amp-free) ,body))
                    ,@idecl
                    ,ret)
               `(mv-let ,amp-free
                  ,body
                  ,@idecl
                  ,ret))))

    `(make-event (prog2$
                  (check-stobjs ',stobjs (w state) nil)
                  (time$
                   (let ((__function__
                          ;; Goofy: we bind __function__ to make it easy to
                          ;; move code between functions based on
                          ;; std::define and defconsts forms
                          ',(intern summary "ACL2")))
                     (declare (ignorable __function__))
                     ,form)
                   :msg "; ~s0: ~st seconds, ~sa bytes~%"
                   :args (list ,summary))))))
                     
                         

(defmacro defconsts (consts body)
  (defconsts-fn consts body))


;; Basic state-free tests
(local
 (encapsulate
  ()
  (defconsts *foo* 1)

  (defconsts (*foo*) 1)

  (defconsts (*foo* *bar*)
    (mv 1 2))

  (defconsts (*foo* *bar* &)
    (mv 1 2 3))

  (defconsts (*foo* *bar* & *baz*)
    (mv 1 2 3 4))

  (defthm foo (equal *foo* 1) :rule-classes nil)
  (defthm bar (equal *bar* 2) :rule-classes nil)
  (defthm baz (equal *baz* 4) :rule-classes nil)))


;; Basic tests that manipulate state
(local
 (encapsulate
  ()
  (defconsts state
    (mv-let (col state)
            (fmt "Hello, world!~%" nil *standard-co* state nil)
            (declare (ignore col))
            state))

  (defconsts (state)
    (mv-let (col state)
            (fmt "Hello, world!~%" nil *standard-co* state nil)
            (declare (ignore col))
            state))

  (defconsts (*hundred* state)
    (mv-let (col state)
            (fmt "Hello, world!~%" nil *standard-co* state nil)
            (declare (ignore col))
            (mv 100 state)))

  (defconsts (state *hundred*)
    (mv-let (col state)
            (fmt "Hello, world!~%" nil *standard-co* state nil)
            (declare (ignore col))
            (mv state 100)))

  (defthm hundred (equal *hundred* 100) :rule-classes nil)))


;; Basic tests that manipulate a stobj

(local
 (encapsulate
  ()

  (defstobj mystobj
    (field :initially 0))

  (defconsts *zero* (field mystobj))

  (defconsts mystobj
    (update-field 3 mystobj))

  (defconsts *three* (field mystobj))

  (defconsts (*five* mystobj state)
    (mv-let (col state)
            (fmt "Hello, world!~%" nil *standard-co* state nil)
            (declare (ignore col))
            (let ((mystobj (update-field 5 mystobj)))
              (mv (field mystobj) mystobj state))))

  (defthm t1 (equal *zero* 0) :rule-classes nil)
  (defthm t2 (equal *three* 3) :rule-classes nil)
  (defthm t3 (equal *five* 5) :rule-classes nil)))


;; tests of __function__

(local
 (encapsulate
  ()
  (defconsts *oops*
    __function__)

  (defconsts (*oops2* state)
    (mv __function__ state))

  ;; If you change how summaries work, these won't be right.  But, the point
  ;; is to make sure with some test here that __function__ is working.  So, if
  ;; you change summaries, just change these tests to make them work.
  (defthm f1 (equal *oops* 'ACL2::|(DEFCONSTS *OOPS* ...)|)
    :rule-classes nil)
  (defthm f2 (equal *oops2* 'ACL2::|(DEFCONSTS (*OOPS2* ...) ...)|)
    :rule-classes nil)))
