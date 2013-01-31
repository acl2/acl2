; Defconsts -- A defconst that can do multiple values
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "bstar")


(defdoc defconsts
  ":Doc-Section defconst
Define multiple constants~/

Examples:
~bv[]
 (include-book \"tools/defconsts\" :dir :system)

 (defconsts *foo* 1)
 (defconsts (*foo*) 1)
 (defconsts (*foo* *bar*) (mv 1 2))
 (defconsts (*foo* *bar* &) (mv 1 2 3))

 (defconsts (*hundred* state)
   (mv-let (col state)
           (fmt \"Hello, world!\" nil *standard-co* state nil)
           (declare (ignore col))
           (mv 100 state)))
~ev[]

General form:
~bv[]
 (defconsts consts body)
~ev[]

where ~c[consts] is a single symbol or a list of N symbols, and body is a form
that returns N values.

Each symbol in ~c[consts] should either be:
  - A \"starred\" name like ~c[*foo*],
  - A non-starred name which names a stobj (e.g., ~c[state]), or
  - ~c[&], which means \"skip this return value.\"

We introduce a ~c[defconst] form that binds each starred name to the
corresponding value returned by ~c[body].~/

Because these bindings are introduced with a ~ilc[make-event], ~c[defconsts]
acts more like ~c[defconst-fast] than ~c[defconst].  This has certain
performance implications, e.g., the expansion of these constants will be stored
in the certificate file instead of being recomputed.~/")


(local (defthm true-listp-when-symbol-listp
         (implies (symbol-listp x)
                  (true-listp x))))

(local (defthm len-of-revappend
         (equal (len (revappend x y))
                (+ (len x) (len y)))))

(local (defthm symbolp-of-car-when-symbol-listp
         (implies (symbol-listp x)
                  (symbolp (car x)))))

(local (defthm symbol-listp-of-cdr-when-symbol-listp
         (implies (symbol-listp x)
                  (symbol-listp (cdr x)))))

(local (defthm symbol-listp-of-revappend
         (implies (and (force (symbol-listp x))
                       (force (symbol-listp y)))
                  (symbol-listp (revappend x y)))))

(local (defthm symbol-listp-of-remove
         (implies (force (symbol-listp x))
                  (symbol-listp (remove a x)))))

(local (defthm symbol-listp-of-last
         (implies (force (symbol-listp x))
                  (symbol-listp (last x)))))

(local (defthm symbol-listp-of-set-difference-eq
         (implies (force (symbol-listp x))
                  (symbol-listp (set-difference-eq x y)))))

; Bah.  Re-prove character-listp-of-explode-atom here instead of just including
; unicode/explode-atom, because otherwise acl2's Makefile-generic wouldn't be
; able to cope with "circular" tools/ and unicode/ dependencies.

(local (defthm character-listp-of-explode-nonnegative-integer
         (equal (character-listp (explode-nonnegative-integer n base acc))
                (character-listp acc))))

(local (defthm character-listp-of-append
         (implies (and (character-listp x)
                       (character-listp y))
                  (character-listp (append x y)))))

(local (defthm character-listp-of-explode-atom
         (implies (force (print-base-p base))
                  (character-listp (explode-atom x base)))
         :hints(("Goal" :in-theory (disable explode-nonnegative-integer)))))

(local (in-theory (disable explode-atom)))



(defund defconsts-check-names (x)
  ;; Same as symbol-listp but causes warnings
  (declare (xargs :guard t))
  (if (atom x)
      (or (not x)
          (er hard? 'defconsts-check-names "Names are not a true-listp."))
    (and (or (symbolp (car x))
             (er hard? 'defconsts-check-names
                 "Not a valid name for defconsts: ~x0.~%" (car x)))
         (defconsts-check-names (cdr x)))))

(local (defthm symbol-listp-when-defconsts-check-names
         (implies (defconsts-check-names x)
                  (symbol-listp x))
         :hints(("Goal" :in-theory (enable defconsts-check-names)))))

(local (defthm symbolp-when-defconsts-check-names-singleton
         (implies (defconsts-check-names (list x))
                  (symbolp x))
         :hints(("Goal" :in-theory (enable defconsts-check-names)))))




(defund defconsts-const-name-p (x)
  ;; Recognize *foo*
  (declare (xargs :guard (symbolp x)))
  (let* ((name (symbol-name x))
         (nl   (length name)))
    (and (>= nl 3)
         (eql (char name 0) #\*)
         (eql (char name (- nl 1)) #\*))))

(defund defconsts-collect-stobj-names (x)
  (declare (xargs :guard (symbol-listp x)))
  (cond ((atom x)
         nil)
        ((or (defconsts-const-name-p (car x))
             (eq (car x) #\&))
         (defconsts-collect-stobj-names (cdr x)))
        (t
         (cons (car x)
               (defconsts-collect-stobj-names (cdr x))))))


(defund defconsts-strip-stars1 (x)
  ;; *foo* --> foo
  (declare (xargs :guard (symbolp x)
                  :guard-hints(("Goal" :in-theory (enable defconsts-const-name-p)))))
  (if (defconsts-const-name-p x)
      (let* ((name    (symbol-name x))
             (nl      (length name))
             (nostars (subseq name 1 (- nl 1))))
        (intern-in-package-of-symbol nostars x))
    x))

(defthm symbolp-of-defconsts-strip-stars1
  (implies (symbolp x)
           (symbolp (defconsts-strip-stars1 x)))
  :hints(("Goal" :in-theory (enable defconsts-strip-stars1))))


(defund defconsts-strip-stars (x)
  ;; (*foo* *bar* baz) --> (foo bar baz)
  (declare (xargs :guard (symbol-listp x)))
  (if (atom x)
      nil
    (cons (defconsts-strip-stars1 (car x))
          (defconsts-strip-stars (cdr x)))))

(defthm symbol-listp-of-defconsts-strip-stars
  (implies (symbol-listp x)
           (symbol-listp (defconsts-strip-stars x)))
  :hints(("Goal" :in-theory (enable defconsts-strip-stars))))

(defthm len-of-defconsts-strip-stars
  (equal (len (defconsts-strip-stars x))
         (len x))
  :hints(("Goal" :in-theory (enable defconsts-strip-stars))))


(defund defconsts-make-n-fresh-symbols (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      nil
    (cons (intern-in-package-of-symbol
           (concatenate 'string "defconsts-ignore-"
                        (coerce (explode-atom n 10) 'string))
           'foo)
          (defconsts-make-n-fresh-symbols (- n 1)))))

(defthm symbol-listp-of-defconsts-make-n-fresh-symbols
  (symbol-listp (defconsts-make-n-fresh-symbols n))
  :hints(("Goal" :in-theory (enable defconsts-make-n-fresh-symbols))))

(defthm len-of-defconsts-make-n-fresh-symbols
  (equal (len (defconsts-make-n-fresh-symbols n))
         (nfix n))
  :hints(("Goal" :in-theory (enable defconsts-make-n-fresh-symbols))))

(defund defconsts-replace-amps (x fresh-syms)
  ;; (*foo* *bar* & & baz) --> (*foo* *bar* fresh-syms3 fresh-syms4 baz)
  (declare (xargs :guard (and (symbol-listp x)
                              (symbol-listp fresh-syms)
                              (= (len fresh-syms) (len x)))))
  (cond ((atom x)
         nil)
        ((eq (car x) '&)
         (cons (car fresh-syms) (defconsts-replace-amps (cdr x) (cdr fresh-syms))))
        (t
         (cons (car x) (defconsts-replace-amps (cdr x) (cdr fresh-syms))))))

(defthm symbol-listp-of-defconsts-replace-amps
  (implies (and (symbol-listp x)
                (symbol-listp fresh-syms))
           (symbol-listp (defconsts-replace-amps x fresh-syms)))
  :hints(("Goal" :in-theory (enable defconsts-replace-amps))))

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


(defund defconsts-fn (consts body)
  (declare (xargs :guard t
                  :guard-debug t))
  (b* (;; Goofy thing to allow (defconsts *foo* ...) instead of (defconsts (*foo*) ...)
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

       ;; If there are any stobjs, we need to return
       ;;    (mv nil '(progn (defconst ...)) state ... stobjs ...)
       (stobjs         (defconsts-collect-stobj-names (remove '& consts)))
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

      `(make-event (time$
                    (let ((__function__
                           ;; Goofy: we bind __function__ to make it easy to
                           ;; move code between functions based on
                           ;; cutil::define and defconsts forms
                           ',(intern summary "ACL2")))
                      (declare (ignorable __function__))
                      ,form)
                    :msg "; ~s0: ~st seconds, ~sa bytes~%"
                    :args (list ,summary)))))

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
   (defthm f1 (equal *oops* '|(DEFCONSTS *OOPS* ...)|)
     :rule-classes nil)
   (defthm f2 (equal *oops2* '|(DEFCONSTS (*OOPS2* ...) ...)|)
     :rule-classes nil)))
