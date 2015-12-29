; Rob Sumners

#||
Note: The license below is based on the template at:
http://opensource.org/licenses/BSD-3-Clause

Copyright (C) 2013, Regents of the University of Texas
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

o Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

o Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution.

o Neither the name of the University of Texas, Austin nor the names of
  its contributors may be used to endorse or promote products derived
  from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

||#

(in-package "ACL2")
(include-book "total-order")

(defxdoc misc/records
  :parents (alists)
  :short "A @('misc/record') is an <see topic='@(url alists)'>alist</see>-like
data structure that associates keys to values, but features efficient,
unconditional rewrite rules about its @('get') and @('set') operations."

  :long "<h3>Introduction</h3>

<p>Note: See also the following paper:</p>

<blockquote> Matt Kaufmann and Rob Sumners.  <a
href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2002/contrib/kaufmann-sumners/rcd.pdf'>Efficient
Rewriting of Data Structures in ACL2</a>.  In: Proceedings of <a
href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2002/'>ACL2 Workshop
2002</a>.  (<a
href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2002/contrib/kaufmann-sumners/rcdsld.pdf'>Slides</a>)</blockquote>

<p>We define properties of a generic record accessor function and updater
function.  The basic functions are:</p>

<ul>

<li>@('(g a r)') &mdash; returns the value at address @('a') in record
@('r')</li>

<li>@('(s a v r)') &mdash; returns a new record by setting address @('a') to
value @('v') in record @('r')</li>

</ul>

<p>The following main lemmas are ``exported'' about record @(see g)et and @(see
s)et:</p>

@({
    (defthm g-same-s
      (equal (g a (s a v r))
             v))

    (defthm g-diff-s
      (implies (not (equal a b))
               (equal (g a (s b v r))
                      (g a r))))

    (defthm s-same-g
      (equal (s a (g a r) r)
             r))

    (defthm s-same-s
      (equal (s a y (s a x r))
             (s a y r)))

    (defthm s-diff-s
      (implies (not (equal a b))
               (equal (s b y (s a x r))
                      (s a x (s b y r))))
      :rule-classes ((:rewrite :loop-stopper ((b a s)))))
})

<p>We also include some auxiliary lemmas which have proven useful.</p>

@({
    (defthm access-of-nil-is-nil
      (not (g a nil)))

    (defthm record-set-cannot-be-nil
      (implies v (s a v r)))

    (defthm record-get-non-nil-cannot-be-nil
      (implies (g a r) r))
})

<h3>Extensions and Related Books</h3>

<p>The @('misc/records') book has been widely popular, especially for
representing memories and heaps.  This popularity has led to some variants and
extensions.</p>

<p>Records make no distinction between addresses that are unbound versus
addresses that are bound to @('nil').  This generally makes it difficult to
reason about the domain of a record, and difficult to iterate through the keys
of a record.  The @('coi/records') books add several theorems, as well as
functions like @('rkeys') and useful lemmas like @('rkeyquiv-by-multiplicity')
that allow you to prove records are equal by showing that they agree for any
arbitrary key in a ``pick-a-point'' fashion.  These are generally not well
documented, so see the books themselves for details.</p>

<p>The @(see memory) library defines @('memory') data structures which are very
similar to @('misc/records') and provide the same read-over-write theorems, but
which are intended to be more efficient for representing processor memories.
These functions have restrictive guards that require addresses must be natural
numbers below @($2^n$) for some @($n$), but use a tree-like structure for
@($O(\\log_2 n)$) performance.</p>

<p>The @(see defrstobj) library allows certain @(see stobj)s to be reasoned
about as if they were @(see misc/records).  This may be useful for developing
efficient processor models.</p>

<p>The keys and values of @('misc/records') are essentially untyped.  The book
@('coi/records/defrecord') provides a way to introduce alternate ``typed''
records.  See also: David Greve and Matthew Wilding.  <a
href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2003/contrib/greve-wilding_defrecord/defrecord.pdf'>Typed
ACL2 Records</a>.  ACL2 Workshop 2003.  An alternative typed record
implementation is also provided by the @(see defrstobj) books, see @(see
def-typed-record).</p>


<h3>Implementation Notes</h3>

<p>We normalize the record structures (which allows the equality based rewrite
rules) as alists where the keys (cars) are ordered using the total-order @(see
<<). We define a set of ``-aux'' functions which assume well-formed records,
defined by @('rcdp'), and then prove the desired properties using hypothesis
assuming well-formed records.</p>

<p>We then remove these well-formed record hypothesis by defining an invertible
mapping, @('acl2->rcd') taking any ACL2 object and returning a well-formed
record. We then prove the desired properties using the proper translations of
the -aux functions to the acl2 objects, and subsequently remove the well-formed
record hypothesis.</p>")

(defxdoc g
  :parents (misc/records)
  :short "Basic accessor for @(see misc/records)."
  :long "<p>@('(g a r)') returns the value stored at address @('a') in record
@('r').</p>

<p>This is essentially similar to a function like @(see assoc) for @(see
alists), except that @('misc/records') do not distinguish between keys that are
unbound and keys that are bound to @('nil'), so @('g') just returns the value
instead of a @('(key . value)') pair.</p>")

(defxdoc s
  :parents (misc/records)
  :short "Basic update function for @(see misc/records)."
  :long "<p>@('(s a v r)') ``modifies'' the record @('r') by installing the
value @('v') at address @('a').  This produces a new record.</p>

<p>This is essentially similar to a function like @(see acons) for @(see
alists), but its careful definition supports the lemmas described in @(see
misc/records).</p>")


;; BEGIN records definitions.

(defun rcdp1 (x)

; Tail-recursive version of rcdp for alistp argument.

  (declare (xargs :guard (alistp x)))
  (or (endp x)
      (and (cdar x)
	   (or (null (cdr x))
               (and (<< (caar x) (caadr x))
                    (rcdp1 (cdr x)))))))

(defun rcdp (x)
  (declare (xargs :guard t))
  (mbe :logic (or (null x)
                  (and (consp x)
                       (consp (car x))
                       (rcdp (cdr x))
                       (cdar x)
                       (or (null (cdr x))
                           (<< (caar x) (caadr x)))))

; Faster version that is tail recursive.  See also
; books/defexec/other-apps/records/records.lisp for related approaches to fast
; executability for records.

       :exec (and (alistp x)
                  (rcdp1 x))))

(defun ifrp (x) ;; ill-formed rcdp
  (declare (xargs :guard t))
  (or (not (rcdp x))
      (and (consp x)
           (null (cdr x))
           (consp (car x))
           (null (caar x))
           (ifrp (cdar x)))))

(defun acl2->rcd (x)  ;; function mapping acl2 objects to well-formed records.
  (declare (xargs :guard t))
  (if (ifrp x) (list (cons nil x)) x))

(defun rcd->acl2 (x)  ;; inverse of acl2->rcd.
  (declare (xargs :guard (rcdp x)))
  (if (ifrp x) (cdar x) x))

(defun g-aux (a x) ;; record g(et) when x is a well-formed record.
  (declare (xargs :guard (rcdp x)))
  (cond ((or (endp x)
             (<< a (caar x)))
         nil)
        ((equal a (caar x))
         (cdar x))
        (t
         (g-aux a (cdr x)))))

(defun g (a x) ;; the generic record g(et) which works on any ACL2 object.
  (declare (xargs :guard t))
  (g-aux a (acl2->rcd x)))

(defun s-aux (a v r) ;; record s(et) when x is a well-formed record.
  (declare (xargs :guard (rcdp r)))
  (cond ((or (endp r)
             (<< a (caar r)))
         (if v (cons (cons a v) r) r))
        ((equal a (caar r))
         (if v (cons (cons a v) (cdr r)) (cdr r)))
        (t
         (cons (car r) (s-aux a v (cdr r))))))

;; we need the following theorems in order to get the guard for s to verify.

(local
(defthm s-aux-is-bounded
  (implies (and (rcdp r)
                (s-aux a v r)
                (<< e a)
                (<< e (caar r)))
           (<< e (caar (s-aux a v r))))))

(local
(defthm s-aux-preserves-rcdp
  (implies (rcdp r)
           (rcdp (s-aux a v r)))))

(defun s (a v x) ;; the generic record s(et) which works on any ACL2 object.
  (declare (xargs :guard t))
  (rcd->acl2 (s-aux a v (acl2->rcd x))))


;;;; basic property of records ;;;;

(local
(defthm rcdp-implies-true-listp
  (implies (rcdp x)
           (true-listp x))
  :rule-classes (:forward-chaining
                 :rewrite)))


;;;; initial properties of s-aux and g-aux ;;;;

(local
(defthm g-aux-same-s-aux
  (implies (rcdp r)
           (equal (g-aux a (s-aux a v r))
                  v))))

(local
(defthm g-aux-diff-s-aux
  (implies (and (rcdp r)
                (not (equal a b)))
           (equal (g-aux a (s-aux b v r))
                  (g-aux a r)))))

(local
(defthm s-aux-same-g-aux
  (implies (rcdp r)
           (equal (s-aux a (g-aux a r) r)
                  r))))

(local
(defthm s-aux-same-s-aux
  (implies (rcdp r)
           (equal (s-aux a y (s-aux a x r))
                  (s-aux a y r)))))

(local
(defthm s-aux-diff-s-aux
  (implies (and (rcdp r)
                (not (equal a b)))
           (equal (s-aux b y (s-aux a x r))
                  (s-aux a x (s-aux b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a s))))))

(local
(defthm s-aux-non-nil-cannot-be-nil
  (implies (and v (rcdp r))
           (s-aux a v r))))

(local
(defthm g-aux-is-nil-for-<<
  (implies (and (rcdp r)
                (<< a (caar r)))
           (equal (g-aux a r) nil))))


;;;; properties of acl2->rcd and rcd->acl2 ;;;;

(local
(defthm acl2->rcd-rcd->acl2-of-rcdp
  (implies (rcdp x)
           (equal (acl2->rcd (rcd->acl2 x))
                  x))))

(local
(defthm acl2->rcd-returns-rcdp
  (rcdp (acl2->rcd x))))

(local
(defthm acl2->rcd-preserves-equality
  (iff (equal (acl2->rcd x) (acl2->rcd y))
       (equal x y))))

(local
(defthm rcd->acl2-acl2->rcd-inverse
  (equal (rcd->acl2 (acl2->rcd x)) x)))

(local
(defthm rcd->acl2-of-record-non-nil
  (implies (and r (rcdp r))
           (rcd->acl2 r))))

(in-theory (disable acl2->rcd rcd->acl2))


;;;; final (exported) properties of record g(et) and s(et) ;;;;

;; NOTE that these theorems basically follow from the "equivalent" properties
;; for s-aux and g-aux with rcdp hypothesis, and the lemmas about the acl2->rcd
;; and its inverse rcd->acl2. If the user wanted to add to the following set of
;; exported theorems, they should add the corresponding lemma about s-aux and
;; g-aux using rcdp hypothesis and then add the theorem here about the generic
;; s(et) and g(et) they wish to export from the book.

(defthm g-same-s
  (equal (g a (s a v r))
         v))

(defthm g-diff-s
  (implies (not (equal a b))
           (equal (g a (s b v r))
                  (g a r))))

;;;; NOTE: The following can be used instead of the above rules to force ACL2
;;;; to do a case-split. We disable this rule by default since it can lead to
;;;; an expensive case explosion, but in many cases, this rule may be more
;;;; effective than two rules above and should be enabled.

(defthm g-of-s-redux
  (equal (g a (s b v r))
         (if (equal a b) v (g a r))))

(in-theory (disable g-of-s-redux))

(defthm s-same-g
  (equal (s a (g a r) r)
         r))

(defthm s-same-s
  (equal (s a y (s a x r))
         (s a y r)))

(defthm s-diff-s
  (implies (not (equal a b))
           (equal (s b y (s a x r))
                  (s a x (s b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a s)))))

;; the following theorems are less relevant but have been useful in dealing
;; with a default record of NIL.

(defthm g-of-nil-is-nil
  (not (g a nil)))

(defthm s-non-nil-cannot-be-nil
  (implies v (s a v r))
  :hints (("Goal"
           :in-theory (disable rcd->acl2-of-record-non-nil)
           :use (:instance rcd->acl2-of-record-non-nil
                           (r (s-aux a v (acl2->rcd r)))))))

(defthm non-nil-if-g-non-nil
  (implies (g a r) r)
  :rule-classes :forward-chaining)

;; We disable s and g, assuming the rules proven in this book are sufficient to
;; manipulate record terms which are encountered.

(in-theory (disable s g))

;; Contributed by Sandip Ray (who isn't sure that he is the one who originally
;; wrote this), but renamed here to record-update to avoid name conflicts.

(defun record-update-macro (upds result)
  (declare (xargs :guard (keyword-value-listp upds)))
  (if (endp upds) result
    (record-update-macro (cddr upds)
                         (list 's (car upds) (cadr upds) result))))

(defmacro record-update (old &rest updates)
  (declare (xargs :guard (keyword-value-listp updates)))
  (record-update-macro updates old))
