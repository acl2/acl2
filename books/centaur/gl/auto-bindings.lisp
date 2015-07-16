; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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
; auto-bindings.lisp
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "GL")
(include-book "gobject-types")
(include-book "../misc/numlist")
(include-book "std/util/bstar" :dir :system)
(program)

(defxdoc auto-bindings
  :parents (reference shape-specs)
  :short "Simplified shape specifiers for @(':g-bindings')."
  :long "<p>The @('auto-bindings') function lets you create simple @(see
shape-specs) in an easy way.  Here is an example:</p>

@({
 (def-gl-thm foo
   ...
   :g-bindings (auto-bindings               ; expands to:
                (:nat opcode 8)             ; g-number with indices 0-8
                (:int multiplier 16)        ; g-number with indices 9-25
                (:bool enable)              ; g-boolean with index 26
                (:mix (:nat a-bus 128)      ; }  g-numbers whose indices
                      (:nat b-bus 128)      ; }  are interleaved, 27 to 414
                      (:nat c-bus 128))     ; }
                (:nat fixup-bits 4)         ; g-number with indices 415-420
                ))
})

<p>This is good because</p>

<ul>

<li>you don't have to think about sign bits and do a bunch of stupid arithmetic
to figure out the next free index, and</li>

<li>you can painlessly extend the bindings when you want to add a new variable
without having to update a bunch of indices.</li>

</ul>

<p>Auto-bindings are more limited than shape-specs.  Except for the special
@(':mix') command, you can only write:</p>

@({
    (:bool var)  -- expands to a g-boolean shape-specifier
    (:int var n) -- expands to a g-integer with n bits (signed 2's complement)
    (:nat var n) -- equivalent to (:int var (+ 1 n))
})

<p>The @(':mix') command cannot be nested and all of its elements must be
numbers with the same size.  That is, think of a @(':nat') as just an
abbreviation for an @(':int') with one more variable.</p>")

(defun auto-bind-xlate (x inside-mix-p)
  ;; Syntax check that X is (:nat ...), (:int ...), or (:bool ...)
  ;; Converts (:nat ...) into (:int ...) with extra var.
  ;; Converts (:bool var) into (:bool var 1).
  (if (not (true-listp x))
      (er hard? 'auto-bind-xlate "Auto-binding not even a true-listp: ~x0" x)
    (case (first x)
      (:bool
       (cond (inside-mix-p
              (er hard? 'auto-bind-xlate "Auto-bindings of :bool aren't allowed inside mix: ~x0" x))
             ((and (= (len x) 2)
                   (acl2::legal-variablep (second x)))
              (list :bool (second x) 1))
             (t
              (er hard? 'auto-bind-xlate "Auto-binding is invalid: ~x0" x))))
      ((:nat :int)
       (if (and (= (len x) 3)
                (acl2::legal-variablep (second x))
                (posp (third x)))
           (list :int (second x) (if (eq (first x) :nat)
                                     (+ 1 (third x))
                                   (third x)))
         (er hard? 'auto-bind-xlate "Auto-binding is invalid: ~x0" x)))
      (otherwise
       (er hard? 'auto-bind-xlate "Auto-binding has unrecognized type: ~x0" x)))))

#||
(auto-bind-xlate '(:bool foo) nil)
(auto-bind-xlate '(:bool foo) t)
(auto-bind-xlate '(:nat bar 5) nil)
(auto-bind-xlate '(:int baz 5) nil)|
||#

(defun auto-bind-lens-ok (len x)
  ;; X has already been translated, so :NAT and :INT agree.
  ;; Make sure all have length LEN.
  (cond ((atom x)
         nil)
        ((equal len (third (car x)))
         (auto-bind-lens-ok len (cdr x)))
        (t
         (er hard? 'auto-bind-lens-ok
             "Lengths inside :mix must agree; expected length ~x0 but found ~x1 for ~x2."
             len (third (car x)) (car x)))))

(defun auto-bind-xlate-list (x inside-mix-p)
  ;; Expand out (:nat ...) into (:int ...), make sure all uses of :mix are okay.
  (cond ((atom x)
         (if (null x)
             nil
           (cw "Warning: weird final cdr of auto-bindings: ~x0.~%" x)))
        ((and (consp (car x))
              (eq (caar x) :mix))
         (cond (inside-mix-p
                (er hard? 'auto-bind-xlate-list "Nested :mix commands are not supported."))
               ((not (cdar x))
                (progn$
                 (cw "Warning: ignoring empty :mix in auto-bindings~%")
                 (auto-bind-xlate-list (cdr x) inside-mix-p)))
               (t
                (let ((x-guts (auto-bind-xlate-list (cdar x) t)))
                  (progn$
                   (auto-bind-lens-ok (third (car x-guts)) (cdr x-guts))
                   (cons (cons :mix x-guts)
                         (auto-bind-xlate-list (cdr x) inside-mix-p)))))))
        (t
         (cons (auto-bind-xlate (car x) inside-mix-p)
               (auto-bind-xlate-list (cdr x) inside-mix-p)))))

#||
(auto-bind-xlate-list
 '((:bool foo)
   (:int a 6)
   (:nat b 5)
   (:mix (:int x 3)
         (:nat y 2))
   (:bool eep))
 nil)
||#

(defun auto-bind-generate (x free-idx by)
  ;; X is a translated auto-bind entry, i.e., a bool or int with its length available
  ;; Returns a singleton LIST of bindings so it can be appended (to make :mix easy)
  (b* (((list type var len) x))
    (list
     (case type
       (:bool `(,var ,(g-boolean free-idx)))
       (:int  `(,var ,(g-number (list (numlist free-idx by len)))))
       (otherwise
        (er hard? 'auto-bind-generate "Should never happen: not translated: ~x0" x))))))

#||
(auto-bind-generate '(:int a 5) 0 2)
(auto-bind-generate '(:bool b 1) 0 1)
||#

(defun auto-bind-mix (x free-idx by)
  ;; X is a mix-free translated list of auto binds that we want to interleave
  ;; BY is the initial (len x)
  (if (atom x)
      nil
    (append (auto-bind-generate (car x) free-idx by)
            (auto-bind-mix (cdr x) (+ 1 free-idx) by))))

#||
(auto-bind-mix '((:int a 5) (:int b 5) (:int c 5)) 0 3)
||#

(defun auto-bind-main (x free-idx)
  ;; X is a translated list that might have mixes
  (cond ((atom x)
         nil)
        ((eq (caar x) :mix)
         (let* ((entries   (cdar x))
                (nentries  (len entries))
                (indiv-len (third (car entries))))
           ;; Individual lengths must all agree
           (append (auto-bind-mix entries free-idx nentries)
                   (auto-bind-main (cdr x) (+ free-idx (* indiv-len nentries))))))
        (t
         (append (auto-bind-generate (car x) free-idx 1)
                 (auto-bind-main (cdr x) (+ free-idx (third (car x))))))))

#||
(auto-bind-main '((:BOOL FOO 1)
                  (:INT A 6)
                  (:INT B 6)
                  (:MIX (:INT X 3) (:INT Y 3))
                  (:BOOL EEP 1))
                0)
||#


(defun auto-bindings-fn (x)
  (auto-bind-main (auto-bind-xlate-list x nil) 0))

(defmacro auto-bindings (&rest args)
  `(auto-bindings-fn '(,@args)))

#||
(auto-bindings (:nat opcode 8)             ; g-number with indices 0-8
               (:int multiplier 16)        ; g-number with indices 9-25
               (:bool enable)              ; g-boolean with index 26
               (:mix (:nat a-bus 128)      ; }  g-numbers whose indicies
                     (:nat b-bus 128)      ; }  are interleaved, 27 to 414
                     (:nat c-bus 128))     ; }
               (:nat fixup-bits 4)         ; g-number with indices 415-420
               )
||#
