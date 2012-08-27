; S-Expressions for 4-Valued Logic
; Copyright (C) 2010-2012 Centaur Technology
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

; sexpr-building.lisp
;   - trivial functions for building s-expressions

(in-package "ACL2")
(include-book "sexpr-eval")
(include-book "sexpr-vars")
(include-book "sexpr-3v")
(include-book "cutil/defprojection" :dir :system)
(include-book "misc/definline" :dir :system)
;(local (include-book "sexpr-to-faig")) ;; for 3v-opt stuff
(set-inhibit-warnings "theory" "non-rec")


(defsection 4vs-constructors
  :parents (4v-sexprs)
  :short "Primitive functions for constructing @(see 4v-sexprs)."

  :long "<p>Note that all of these operations use @(see hons) so that
the S-Expressions they produce are structure shared.</p>

<p>These functions carry out a few trivial rewrites (constant folding, double
negation elimination).  An open question: how much rewriting should they do?
Right now I don't try to optimize very aggressively, e.g., @(see sexpr-and)
doesn't eat bufs.  It's not clear how much of the code from @(see
sexpr-rewrite) should be duplicated here.</p>")



(local (defthm 4v-unfloat-when-nonboolean
         (implies (and (not (equal a t))
                       (not (equal a 'f)))
                  (equal (4v-unfloat a)
                         'x))))

(local (defthm equal-of-4v-unfloat-and-4vf
         (equal (equal (4v-unfloat a) (4vf))
                (equal a (4vf)))))

(local (defthm equal-of-4v-unfloat-and-4vt
         (equal (equal (4v-unfloat a) (4vt))
                (equal a (4vt)))))

(local (defthm car-of-4v-sexpr-eval
         (equal (car (4v-sexpr-eval-list x env))
                (if (consp x)
                    (4v-sexpr-eval (car x) env)
                  nil))))

(local (in-theory (disable* 4vp
                            (:ruleset 4v-op-defs)
                            4v-lookup
                            sets::double-containment)))

(local (in-theory (enable 3v-syntax-sexprp)))



(defsection 4vs-t
  :parents (4vs-constructors)
  :short "@(call 4vs-t) returns <tt>(T)</tt>, the s-expression for a constant
true value."

  :long "<p>This is potentially nicer than using <tt>*4vt-sexpr*</tt> directly
because it can be disabled so that rules about <tt>cons</tt> will not
apply.</p>"

  (definlined 4vs-t ()
    (declare (xargs :guard t))
    *4vt-sexpr*)

  (defthm 4v-sexpr-eval-of-4vs-t
    (equal (4v-sexpr-eval (4vs-t) env)
           (4vt)))

  (defthm 4v-sexpr-vars-of-4vs-t
    (equal (4v-sexpr-vars (4vs-t))
           nil))

  (in-theory (disable (4vs-t))))



(defsection 4vs-f
  :parents (4vs-constructors)
  :short "@(call 4vs-f) returns <tt>(F)</tt>, the s-expression for a constant
false value."

  :long "<p>This is potentially nicer than using <tt>*4vf-sexpr*</tt> directly
because it can be disabled so that rules about <tt>cons</tt> will not
apply.</p>"

  (definlined 4vs-f ()
    (declare (xargs :guard t))
    *4vf-sexpr*)

  (defthm 4v-sexpr-eval-of-4vs-f
    (equal (4v-sexpr-eval (4vs-f) env)
           (4vf)))

  (defthm 4v-sexpr-vars-of-4vs-f
    (equal (4v-sexpr-vars (4vs-f))
           nil))

  (in-theory (disable (4vs-f))))



(defsection 4vs-x
  :parents (4vs-constructors)
  :short "@(call 4vs-x) returns <tt>(X)</tt>, the s-expression for a constant
unknown value."

  :long "<p>This is potentially nicer than using <tt>*4vx-sexpr*</tt>
directly because it can be disabled so that rules about <tt>cons</tt>
will not apply.</p>"

  (definlined 4vs-x ()
    (declare (xargs :guard t))
    *4vx-sexpr*)

  (defthm 4v-sexpr-eval-of-4vs-x
    (equal (4v-sexpr-eval (4vs-x) env)
           (4vx)))

  (defthm 4v-sexpr-vars-of-4vs-x
    (equal (4v-sexpr-vars (4vs-x))
           nil))

  (in-theory (disable (4vs-x))))



(defsection 4vs-z
  :parents (4vs-constructors)
  :short "@(call 4vs-z) returns <tt>(Z)</tt>, the s-expression for a constant
undriven/floating value."

  :long "<p>This is potentially nicer than using <tt>*4vz-sexpr*</tt>
directly because it can be disabled so that rules about <tt>cons</tt>
will not apply.</p>"

  (definlined 4vs-z ()
    (declare (xargs :guard t))
    *4vz-sexpr*)

  (defthm 4v-sexpr-eval-of-4vs-z
    (equal (4v-sexpr-eval (4vs-z) env)
           (4vz)))

  (defthm 4v-sexpr-vars-of-4vs-z
    (equal (4v-sexpr-vars (4vs-z))
           nil))

  (in-theory (disable (4vs-z))))



(defsection 4vs-buf
  :parents (4vs-constructors)
  :short "@(call 4vs-buf) constructs a 4v-sexpr equivalent to <tt>(buf a)</tt>."

  (defund 4vs-buf (a)
    (declare (xargs :guard t))
    (b* (((when (atom a))
          (if a (hons-list 'buf a) nil))
         (fn (car a)))
      (case fn
        ((f t x buf not and or xor iff ite ite* pullup) a)
        (t (hons-list 'buf a)))))

  (local (in-theory (enable 4vs-buf 4v-unfloat)))

  (defthm 4v-sexpr-eval-of-4vs-buf
    (equal (4v-sexpr-eval (4vs-buf a) env)
           (4v-unfloat (4v-sexpr-eval a env))))

  (defthm 4v-sexpr-vars-of-4vs-buf
    (equal (4v-sexpr-vars (4vs-buf a))
           (4v-sexpr-vars a))))

(local (defthm subsetp-equal-of-list-fix-1
         (equal (subsetp-equal (list-fix x) y)
                (subsetp-equal x y))
         :hints(("Goal" :in-theory (enable subsetp-equal)))))

(local (defthm member-equal-of-list-fix
         (iff (member-equal a (list-fix x))
              (member-equal a x))))

(local (defthm subsetp-equal-of-list-fix-2
         (equal (subsetp-equal x (list-fix y))
                (subsetp-equal x y))
         :hints(("Goal" :in-theory (enable subsetp-equal)))))


(defsection 4vs-not
  :parents (4vs-constructors)
  :short "@(call 4vs-not) constructs a 4v-sexpr equivalent to <tt>(not a)</tt>."

  (defund 4vs-not (a)
    (declare (xargs :guard t))
    (b* (((when (atom a))
          (hons-list 'not a))
         (fn (car a))
         (args (cdr a)))
      (case fn
        ;; The well-formedness stuff here looks ugly and is, but it ensures
        ;; that we get an unconditional 4v-sexpr-vars theorem even when we make
        ;; our optimizations.  The problem is, if you had an ill-formed term
        ;; like (T A), then A would still be in the 4v-sexpr-vars.
        ((t)   (if (not args)
                   *4vf-sexpr*
                 (hons-list 'not a)))
        ((f)   (if (not args)
                   *4vt-sexpr*
                 (hons-list 'not a)))
        ((x z) (if (not args)
                   *4vx-sexpr*
                 (hons-list 'not a)))
        (not   (if (and (consp args)
                        (not (cdr args)))
                   (4vs-buf (first args))
                 (hons-list 'not a)))
        (buf   (if (and (consp args)
                        (not (cdr args)))
                   (hons-list 'not (first args))
                 (hons-list 'not a)))
        (otherwise (hons-list 'not a)))))

  (local (in-theory (enable 4vs-not 4v-not)))

  (defthm 4v-sexpr-eval-of-4vs-not
    (equal (4v-sexpr-eval (4vs-not a) env)
           (4v-not (4v-sexpr-eval a env))))

  (defthm 4v-sexpr-vars-of-4vs-not
    (equal (4v-sexpr-vars (4vs-not a))
           (4v-sexpr-vars a))))


(defsection 4v-not-list
  (local (in-theory (disable 4v-not)))
  (cutil::defprojection 4v-not-list (x)
    (4v-not x)
    :guard t
    :nil-preservingp nil
    :parents (4v-operations)))



(defsection 4vs-not-list

  (cutil::defprojection 4vs-not-list (x)
    (4vs-not x)
    :guard t
    :nil-preservingp nil
    :parents (4vs-constructors))

  (defthm 4v-sexpr-eval-list-of-4vs-not-list
    (equal (4v-sexpr-eval-list (4vs-not-list x) env)
           (4v-not-list (4v-sexpr-eval-list x env)))
    :hints(("Goal" :induct (len x))))

  (defthm 4v-sexpr-vars-list-of-4vs-not-list
    (equal (4v-sexpr-vars-list (4vs-not-list x))
           (4v-sexpr-vars-list x))
    :hints(("Goal" :induct (len x)))))



(defsection 4v-and-list
  :parents (4v-operations)
  :short "@(call 4v-and-list) conjoins a list of @(see 4vp) constants."

  (defund 4v-and-list (x)
    (declare (xargs :guard t))
    (if (atom x)
        (4vt)
      (4v-and (car x)
              (4v-and-list (cdr x)))))

  (local (in-theory (enable 4v-and-list 4v-and 4v-unfloat 4v-fix)))

  (defthm 4v-and-list-when-atom
    (implies (atom x)
             (equal (4v-and-list x)
                    (4vt))))

  (defthm 4v-and-list-of-cons
    (equal (4v-and-list (cons a x))
           (4v-and a (4v-and-list x))))

  (defthm 4v-and-list-never-z
    (equal (equal (4v-and-list x) (4vz))
           nil)))



(defsection 4vs-and
  :parents (sexpr-construtors)
  :short "@(call 4vs-and) constructs a 4v-sexpr equivalent to <tt>(and a b)</tt>."

  (defund 4vs-and (a b)
    (declare (xargs :guard t))
    (cond ((or (atom a) (atom b))
           ;; Could do something special for NILs, but since they're basically
           ;; ill-formed, don't try to optimize for them.
           (cond ((equal a b) (4vs-buf a)) ;; (AND A A) = (BUF A)
                 (t           (hons-list 'and a b))))
          ((4vf-sexpr-p a)  a)           ;; (AND F B) = F
          ((4vf-sexpr-p b)  b)           ;; (AND A F) = F
          ((4vt-sexpr-p a)  (4vs-buf b)) ;; (AND T B) = (BUF B)
          ((4vt-sexpr-p b)  (4vs-buf a)) ;; (AND A T) = (BUF A)
          ((hons-equal a b) (4vs-buf a)) ;; (AND A A) = (BUF A)
          (t                (hons-list 'and a b))))

  (local (in-theory (enable 4vs-and 4v-and)))

  (defthm 4v-sexpr-eval-of-4vs-and
    (equal (4v-sexpr-eval (4vs-and a b) env)
           (4v-and (4v-sexpr-eval a env)
                   (4v-sexpr-eval b env))))

  (defthm 4v-sexpr-vars-of-4vs-and
    (subsetp-equal (4v-sexpr-vars (4vs-and a b))
                   (append (4v-sexpr-vars a)
                           (4v-sexpr-vars b)))))



(defsection 4vs-and-list
  :parents (4vs-constructors)
  :short "@(call 4vs-and-list) reduction ands together all the sexprs in the
list <tt>x</tt>, producing a single sexpr representing their conjunction."

  (defund 4vs-and-list (sexprs)
    (declare (xargs :guard t))
    (if (atom sexprs)
        *4vt-sexpr*
      (4vs-and (car sexprs)
               (4vs-and-list (cdr sexprs)))))

  (local (in-theory (enable 4vs-and-list)))

  (defthm 4v-sexpr-eval-of-4vs-and-list
    (equal (4v-sexpr-eval (4vs-and-list sexprs) env)
           (4v-and-list (4v-sexpr-eval-list sexprs env))))

  (local (defthm l0
           (implies (subsetp-equal (4v-sexpr-vars b) c)
                    (subsetp-equal (4v-sexpr-vars (4vs-and a b))
                                   (append (4v-sexpr-vars a) c)))
           :hints(("goal"
                   :in-theory (disable 4v-sexpr-vars-of-4vs-and)
                   :use ((:instance 4v-sexpr-vars-of-4vs-and))))))

  (defthm 4v-sexpr-vars-of-4vs-and-list
    (subsetp-equal (4v-sexpr-vars (4vs-and-list x))
                   (4v-sexpr-vars-list x))
    :hints(("Goal" :induct (len x)))))



(defsection 4vs-and-lists
  :parents (sexpr-constructors)
  :short "@(call 4vs-and-lists) pairwise ands together the sexprs from two
separate lists, forming a new sexpr list."

  (defund 4vs-and-lists (x y)
    (declare (xargs :guard (equal (len x) (len y))))
    (if (atom x)
        nil
      (cons (4vs-and (car x) (car y))
            (4vs-and-lists (cdr x) (cdr y))))))


(defsection 4vs-and-dumb
  :parents (sexpr-construtors)
  :short "@(call 4vs-and-dumb) constructs exactly the 4v-sexpr <tt>(and a b)</tt>."
  :long "<p>This is dumb in that it doesn't do the simple optimizations of
@(see 4vs-and), but it has a nicer @(see 4v-sexpr-vars) theorem because of
this.</p>"

  (defund 4vs-and-dumb (a b)
    (declare (xargs :guard t))
    (hons-list 'and a b))

  (local (in-theory (enable 4vs-and-dumb 4v-and)))

  (defthm 4v-sexpr-eval-of-4vs-and-dumb
    (equal (4v-sexpr-eval (4vs-and-dumb a b) env)
           (4v-and (4v-sexpr-eval a env)
                   (4v-sexpr-eval b env))))

  (defthm 4v-sexpr-vars-of-4vs-and-dumb
    (equal (4v-sexpr-vars (4vs-and-dumb a b))
           (hons-alphorder-merge (4v-sexpr-vars a)
                                 (4v-sexpr-vars b)))))


(defsection 4vs-and-list-dumb
  :parents (4vs-constructors)
  :short "@(call 4vs-and-list-dumb) reduction ands together all the sexprs in the
list <tt>x</tt>, producing a single sexpr representing their conjunction."
  :long "<p>This is dumb in that it doesn't do the simple optimizations of
@(see 4vs-and-list), but it has a nicer @(see 4v-sexpr-vars) theorem because of
this.</p>"

  (defund 4vs-and-list-dumb (sexprs)
    (declare (xargs :guard t))
    (if (atom sexprs)
        *4vt-sexpr*
      (4vs-and-dumb (car sexprs)
                    (4vs-and-list-dumb (cdr sexprs)))))

  (local (in-theory (enable 4vs-and-list-dumb)))

  (defthm 4v-sexpr-eval-of-4vs-and-list-dumb
    (equal (4v-sexpr-eval (4vs-and-list-dumb sexprs) env)
           (4v-and-list (4v-sexpr-eval-list sexprs env))))

  (defthm 4v-sexpr-vars-of-4vs-and-list-dumb
    (equal (4v-sexpr-vars (4vs-and-list-dumb x))
           (4v-sexpr-vars-list x))
    :hints(("Goal" :induct (len x)))))



(defsection 4vs-ite*-dumb
  :parents (4vs-constructors)
  :short "@(call 4vs-ite*-dumb) constructs <tt>(ITE* C A B)</tt>, i.e., the
s-expression for a conservative multiplexor."

  (definlined 4vs-ite*-dumb (c a b)
    (declare (xargs :guard t))
    (hons-list 'ite* c a b))

  (local (in-theory (enable 4vs-ite*-dumb)))

  (defthm 4v-sexpr-eval-of-4vs-ite*-dumb
    (equal (4v-sexpr-eval (4vs-ite*-dumb c a b) env)
           (4v-ite* (4v-sexpr-eval c env)
                    (4v-sexpr-eval a env)
                    (4v-sexpr-eval b env)))
    :hints(("Goal" :in-theory (enable 4vs-ite*-dumb))))

  (defthm 4v-sexpr-vars-of-4vs-ite*-dumb
    (equal (4v-sexpr-vars (4vs-ite*-dumb c a b))
           (hons-alphorder-merge (4v-sexpr-vars c)
                                 (hons-alphorder-merge (4v-sexpr-vars a)
                                                       (4v-sexpr-vars b))))
    :hints(("Goal" :in-theory (enable 4vs-ite*-dumb)))))





(defsection 4vs-or
  :parents (sexpr-construtors)
  :short "@(call 4vs-or) constructs a 4v-sexpr equivalent to <tt>(or a b)</tt>."

  (defund 4vs-or (a b)
    (declare (xargs :guard t))
    (cond ((or (atom a) (atom b))
           (cond ((equal a b) (4vs-buf a)) ;; (OR A A) = (BUF A)
                 (t           (hons-list 'or a b))))
          ((4vt-sexpr-p a)  a)             ;; (OR T B) = T
          ((4vt-sexpr-p b)  b)             ;; (OR A T) = T
          ((4vf-sexpr-p a)  (4vs-buf b)) ;; (OR F B) = (BUF B)
          ((4vf-sexpr-p b)  (4vs-buf a)) ;; (OR A F) = (BUF A)
          ((hons-equal a b) (4vs-buf a)) ;; (OR A A) = (BUF A)
          (t                (hons-list 'or a b))))

  (local (in-theory (enable 4vs-or 4v-or)))

  (defthm 4v-sexpr-eval-of-4vs-or
    (equal (4v-sexpr-eval (4vs-or a b) env)
           (4v-or (4v-sexpr-eval a env)
                  (4v-sexpr-eval b env)))))


(defsection 4vs-or-list
  :parents (sexpr-construtors)
  :short "@(call 4vs-or-list) reduction ors together all the sexprs in the
list <tt>x</tt>, producing a single sexpr representing their disjunction."

  (defund 4vs-or-list (x)
    (declare (xargs :guard t))
    (if (atom x)
        *4vf-sexpr*
      (4vs-or (car x)
                (4vs-or-list (cdr x))))))


(defsection 4vs-or-lists
  :parents (sexpr-constructors)
  :short "@(call 4vs-or-lists) pairwise ors together the sexprs from two
separate lists, forming a new sexpr list."

  (defund 4vs-or-lists (x y)
    (declare (xargs :guard (equal (len x) (len y))))
    (if (atom x)
        nil
      (cons (4vs-or (car x) (car y))
            (4vs-or-lists (cdr x) (cdr y))))))





(defsection 4vs-xor
  :parents (sexpr-constructors)
  :short "@(call 4vs-xor) constructs a sexpr representing <tt>(xor a
b)</tt>."

  (defund 4vs-xor (a b)
    (declare (xargs :guard t))
    (cond ((or (atom a) (atom b))
           ;; We probably don't want to do anything here.  (XOR A A) is
           ;; probably our best canonical form; we could try to canonicalize A
           ;; << B or something, which should be relatively cheap for atoms,
           ;; but this is a more general problem and solving it for atomic
           ;; xors probably doesn't help much.
           (hons-list 'xor a b))
          ((4vx-sexpr-p a) a)              ;; (XOR X B) = X
          ((4vx-sexpr-p b) b)              ;; (XOR A X) = X
          ((4vf-sexpr-p a) (4vs-buf b))  ;; (XOR F B) = (BUF B)
          ((4vf-sexpr-p b) (4vs-buf a))  ;; (XOR A F) = (BUF A)
          ((4vt-sexpr-p a) (4vs-not b))  ;; (XOR T B) = (NOT B)
          ((4vt-sexpr-p b) (4vs-not a))  ;; (XOR A T) = (NOT A)
          (t (hons-list 'xor a b))))

  (local (in-theory (enable 4vs-xor 4v-xor 4v-not)))

  (defthm 4v-sexpr-eval-of-4vs-xor
    (equal (4v-sexpr-eval (4vs-xor a b) env)
           (4v-xor (4v-sexpr-eval a env)
                   (4v-sexpr-eval b env)))))

(defsection 4vs-xor-lists
  :parents (sexpr-constructors)
  :short "@(call 4vs-xor-lists) pairwise xors together the sexprs from two
separate lists, forming a new sexpr list."

  (defund 4vs-xor-lists (x y)
    (declare (xargs :guard (equal (len x) (len y))))
    (if (atom x)
        nil
      (cons (4vs-xor (car x) (car y))
            (4vs-xor-lists (cdr x) (cdr y))))))





(defsection 4vs-iff
  :parents (sexpr-constructors)
  :short "@(call 4vs-iff) constructs a sexpr representing <tt>(iff a
b)</tt>."
  :long "<p>To make this better agree with @(see sexpr-rewrite), I just
implement this as the not of the <tt>xor</tt>.</p>"

  (defund 4vs-iff (a b)
    (declare (xargs :guard t))
    (4vs-not (4vs-xor a b)))

  (local (in-theory (enable 4vs-iff 4v-iff 4v-xor 4v-not)))

  (defthm 4v-sexpr-eval-of-4vs-iff
    (equal (4v-sexpr-eval (4vs-iff a b) env)
           (4v-iff (4v-sexpr-eval a env)
                   (4v-sexpr-eval b env)))))


(defsection 4vs-iff-lists
  :parents (sexpr-constructors)
  :short "@(call 4vs-iff-lists) pairwise iffs together the sexprs from the
lists x and y, forming a new sexpr list."

  (defund 4vs-iff-lists (x y)
    (declare (xargs :guard (equal (len x) (len y))))
    (if (atom x)
        nil
      (cons (4vs-iff (car x) (car y))
            (4vs-iff-lists (cdr x) (cdr y))))))





(defsection 4vs-implies
  :parents (sexpr-constructors)
  :short "@(call 4vs-implies) constructs a new sexpr representing
<tt>(implies a b)</tt>."
  :long "<p>This is just an abbreviation for <tt>(or (not a) b)</tt>, so we
leave it enabled.</p>"

  (defun 4vs-implies (a b)
    (declare (xargs :guard t))
    (4vs-or (4vs-not a) b)))


(defsection 4vs-implies-lists
  :parents (sexpr-constructors)
  :short "@(call 4vs-implies-lists) pairwise impliess together the sexprs
from the lists x and y, forming a new sexpr list."

  (defund 4vs-implies-lists (x y)
    (declare (xargs :guard (equal (len x) (len y))))
    (if (atom x)
        nil
      (cons (4vs-implies (car x) (car y))
            (4vs-implies-lists (cdr x) (cdr y))))))

