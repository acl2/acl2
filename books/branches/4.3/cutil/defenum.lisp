; CUTIL - Centaur Basic Utilities
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

(in-package "CUTIL")
(include-book "deflist")
(set-state-ok t)

(defxdoc defenum
  :parents (cutil)
  :short "Introduce an enumeration type, like an <tt>enum</tt> in C."
  :long "<p>General form:</p>
<code>
 (defenum name
   elements
   &amp;key mode         ; current defun-mode by default
        parents      ; '(acl2::undocumented) by default
        short        ; nil by default
        long         ; nil by default
        )
</code>

<p>For example,</p>
<code>
 (defenum day-p
   (:monday :tuesday :wednesday :thursday :friday :saturday :sunday))
</code>

<p>results in a new function, <tt>(day-p x)</tt>, that recognizes
<tt>:monday</tt>, <tt>:tuesday</tt>, etc.</p>

<h3>Usage and Options</h3>

<p>I often use keyword symbols as the elements, but any objects (even conses)
can be used.</p>

<p>The optional <tt>:mode</tt> keyword can be set to <tt>:logic</tt> or
<tt>:program</tt> to introduce the recognizer in logic or program mode.  The
default is whatever the current default defun-mode is for ACL2, i.e., if you
are already in program mode, it will default to program mode, etc.</p>

<p>The optional <tt>:parents</tt>, <tt>:short</tt>, and <tt>:long</tt>
parameters are like those in @(see xdoc::defxdoc).  The definition of the
function and theorems about it will automatically be appended to anything you
put into <tt>:long</tt>.</p>

<h3>Performance Notes</h3>

<p>The recognizer just tests its argument against the elements, in order.
Because of this, you might want to order your elements so that the most common
elements come first.  For instance, <tt>day-p</tt> will be fastest on
<tt>:monday</tt> and slowest on <tt>:sunday</tt>.</p>

<p>The recognizer uses <tt>EQ</tt> or <tt>EQL</tt> checks where possible, so
if your enumeration includes a mix of, say, conses and atom like symbols, you
may wish to put the atoms first.</p>

<p>Checking the argument against each element is probably a perfectly good
strategy when the number of elements is small (perhaps fewer than 20) and when
the equality checks are relatively fast (e.g., symbols, characters, numbers).
It is probably is not a good strategy otherwise.  If you want to use defenum
for something more complex, it might be best to modify it to adaptively use a
fast alist or other schemes, based on the elements it is given.</p>")

(defund defenum-members-to-tests (members xvar)
  ;; Generate ((equal xvar member1) (equal xvar member2) ...), except use EQ or
  ;; EQL instead of EQUAL where possible.
  (declare (xargs :guard t))
  (if (atom members)
      nil
    (let ((e (car members)))
      (cons (cond ((symbolp e)
                   `(eq ,xvar ',e))
                  ((eqlablep e)
                   `(eql ,xvar ',e))
                  (t
                   `(equal ,xvar ',e)))
            (defenum-members-to-tests (cdr members) xvar)))))

; (defenum-members-to-tests '(:a :b 3 5 #\a "foo" '(1 . 2)) 'x)

(defun defenum-deduce-type-set (members)
  ;; Figure out the best type set that covers all of members.
  (declare (xargs :mode :program))
  (if (atom members)
      0
    (acl2::ts-union
     (acl2::type-set-quote (car members))
     (defenum-deduce-type-set (cdr members)))))

;(acl2::decode-type-set
; (defenum-deduce-type-set '(:foo :bar 3 5)))
;  -->
; (ACL2::TS-UNION ACL2::*TS-POSITIVE-INTEGER*
;                 ACL2::*TS-NON-T-NON-NIL-SYMBOL*)


(defun defenum-fn (name members mode parents short long state)
  (declare (xargs :mode :program))
  (b* (((unless (symbolp name))
        (er hard 'deflist "Name must be a symbol, but is ~x0." name))

       (?mksym-package-symbol name)
       (x (intern-in-package-of-symbol "X" name))

       ((unless (consp members))
        (er hard 'defenum "There must be at least one member."))

       ((unless (uniquep members))
        (er hard 'defenum
            "The members must be a list of unique, but there are ~
             duplicate entries for ~x0."
            (duplicated-members members)))

       ((unless (or (eq mode :logic)
                    (eq mode :program)))
        (er hard 'defenum
            ":mode must be one of :logic or :program, but is ~x0." mode))

       (body (cons 'or (defenum-members-to-tests members x)))
       (def `(defund ,name (,x)
               (declare (xargs :guard t))
               ,body))

       (long (str::cat (or long "")
                       "<p>This is an ordinary @(see defenum).</p>"
                       "@(def " (symbol-name name) ")"))

       (doc `(defxdoc ,name
               :parents ,parents
               :short ,short
               :long ,long))

       ((when (eq mode :program))
        `(encapsulate
           ()
           (program)
           ,doc
           ,def))


       (long (str::cat long "@(gthm type-when-" (symbol-name name) ")"))

       (doc `(defxdoc ,name
               :parents ,parents
               :short ,short
               :long ,long))

       (ts (defenum-deduce-type-set members))

       ((mv ts-concl &)
        ;; Magic function from :doc type-set
        (acl2::convert-type-set-to-term x ts (acl2::ens state) (w state) nil)))

    `(encapsulate
       ()
       (logic)
       ,doc
       ,def
       (local (in-theory (enable ,name)))

       (with-output
        :off observation
        (defthm ,(mksym 'type-when- name)
          (implies (,name ,x)
                   ,ts-concl)
          :rule-classes :compound-recognizer))

       )))

(defmacro defenum (name members
                        &key
                        mode
                        (parents '(undocumented))
                        (short 'nil)
                        (long 'nil))
  `(make-event (let ((mode (or ',mode (default-defun-mode (w state)))))
                 (defenum-fn ',name ',members mode ',parents ',short ',long state))))


;; Primitive tests
(local
 (encapsulate
   ()
   (defenum day-p
     (:monday :tuesday :wednesday :thursday :friday :saturday :sunday))

   (defenum chartest-p
     (#\a #\b #\c))

   (defenum strsymtest-p
     ("foo" "bar" foo bar))

   (defenum universal-ts-test-p
     (0 1 -1 1/2 -1/2 #c(3 4) nil t foo (1 . 2) (1) "foo" #\a))))

