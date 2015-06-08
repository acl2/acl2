; Centaur Miscellaneous Books
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "std/util/define" :dir :system)
(include-book "tools/include-raw" :dir :system)
(defttag sneaky-load)

(remove-untouchable 'read-acl2-oracle t)

(defsection sneaky
  :parents (debugging)
  :short "A debugging tool for ACL2 programs.  The sneaky functions allow you
to save and mutate global variables, even without access to @(see state)."

  :long "<h3>Introductory example</h3>

@({
    ACL2 !> (defun my-function (x y)           ;; note: no state
              (b* ((sum     (+ x y))
                   (product (* x y)))
                (sneaky-save :sum sum)         ; save the latest sum
                (sneaky-save :product product) ; save the latest product
                (sneaky-incf :calls 1)         ; count how many calls there were
                (list sum product)))

    ACL2 !> (my-function 1 2)
    (3 2)

    ACL2 !> (my-function 3 4)
    (7 12)

    ACL2 !> (defconsts (*sum* state)           ;; *sum* is 7
              (sneaky-load :sum state))        ;; (its most recent value)

    ACL2 !> (defconsts (*product* state)       ;; *product* is 7
              (sneaky-load :product state))    ;; (its most recent value)

    ACL2 !> (defconsts (*calls* state)         ;; *calls* is 2
              (sneaky-load :product state))    ;; (we called my-function twice)
})

<h3>Motivation</h3>

<p>When you are debugging a large program, you may want to get a hold of
internal values from some function that is somehow \"deep\" inside your
computation.  Here are some ways you might do this:</p>

<ul>

<li>Printing.  You could, perhaps via @(see redef), add @(see cw) statements to
print out the desired values. This is easy and works well when your values are
small enough to print, and your function is called infrequently enough that the
printing is not unmanageable.</li>

<li>Tracing.  If the values you want to see are inputs or outputs of a
function, you could perhaps use @(see trace$).  This may avoid needing to
rebuild or use @(see redef).  Like printing, this is likely to work well for
inspecting small values and infrequently called functions.</li>

<li>Globals.  If your functions involves @(see state), you might be able to
just @(see assign) the values of interest to some new state globals.  You could
then extract and inspect them using @(see @).  This approach may work well even
for large values or frequently called functions, but requires access to
state.</li>

</ul>

<p>Unfortunately, if your program is made up of ordinary, pure ACL2 functions
that do not involve @(see state), then using globals might require adding state
all throughout the call tree.  This could be really difficult, especially for a
one-off investigation.</p>

<p>The <b>sneaky</b> mechanism allows you to work around this limitation: it is
very similar to using globals, but allows you to avoid state.</p>

<h3>Implementation</h3>

<p>The sneaky book requires a trust tag.  In raw Lisp, we add a Common Lisp
variable, the @('*sneaky-state*'), which is a hash table associating names with
values.</p>

<p>The main sneaky operations, like @(see sneaky-save), @(see sneaky-push), and
@(see sneaky-incf), allow you to manipulate the values in this hash table, but
only indirectly.  This keeps the @('*sneaky-state*') as a purely Common Lisp
variable that exists outside of ACL2, so the effects of manipulating this state
is logically invisible.  That is, in the logic, all of these functions just
return @('nil').</p>

<p>Meanwhile, to be able to retrieve values, the special operations @(see
sneaky-load) and @(see sneaky-alist) allow you to access the
@('*sneaky-state*').  However, in the logic these functions just read from the
ACL2 oracle.  So, even though a sequence like:</p>

@({
    (sneaky-save :foo 5)
    (sneaky-load :foo state)   ;; should always return (mv '5 state)
})

<p>There is no logical connection between the sneaky save/load, so you should
never be able to prove theorems such as</p>

@({
    (defthm unprovable
      (progn$ (sneaky-save :foo 5)
              (equal (mv-nth 0 (sneaky-load :foo state)) 5)))
})")

(local (xdoc::set-default-parents sneaky))

(define sneaky-mutate
  :short "Low-level way to modify the sneaky store."
  ((fnname   symbolp    "The true mutator function to invoke.")
   (get-keys true-listp "The keys whose values will be retrieved and passed
                         to @('fnname') as its first argument.")
   (user-arg            "Arbitrary additional information to pass to the
                         @('fnname') as its second argument."))
  (declare (ignorable fnname get-keys user-arg))
  :long "<p><b>Warning</b>: this is a very low-level function.  Most of the
time you will want to use higher-level functions like @(see sneaky-save), @(see
sneaky-push), and @(see sneaky-incf) instead.</p>

<p>In the ACL2 logic, this function simply returns @('nil').  Under the hood,
it can cause (logically invisible) side-effects, typically modifying the hidden
\"sneaky store.\"</p>

<p>The particular details of these side-effects depend upon the @('fnname')
argument passed in.  As an example, the definition of @(see sneaky-push) is the
following:</p>

@({
    (defun sneaky-push (name new-elem)
      (sneaky-mutate 'sneaky-push-mutator (list name) (cons name new-elem)))
})

<p>The symbol @('sneaky-push-mutator') refers to the following function:</p>

@({
    (defun sneaky-push-mutator (stored-vals name-elem-pair)
      (list (cons (car name-elem-pair)
                  (cons (cdr name-elem-pair) (car stored-vals)))))
})

<p>What is going on here?  @('Sneaky-push') accesses a value stored under the
name @('name'), and re-stores it with @('new-elem') consed onto it.  How does
this occur?  A call of</p>

@({
   (sneaky-mutate fnname get-keys user-arg)
})

<p>calls the function @('f') named by @('fnname'), in this case
@('sneaky-push-mutator').  @('f') must always have two arguments:</p>

<ol>

<li>The list of values currently associated with @('get-keys').  That is,
    @('sneaky-mutate') will look up each key in @('get-keys') and will
    send the resulting values to @('fnname').</li>

<li>An arbitrary additional argument, provided by @('user-arg').</li>

</ol>

<p>So in the case of @('sneaky-push'), the two arguments passed to
@('sneaky-push-mutator') are:</p>

<ol>

<li>A list containing the stored value that was previously associated with
    @('name'), and</li>

<li>The cons of @('name') itself onto @('new-elem').</li>

</ol>

<p>@('f') must return a single value, which should be an association list.
This alist will be used to update the hidden \"sneaky store.\" In particular,
the store will be modified by assigning each key in the alist to its
corresponding value.</p>

<p>In the case of @('sneaky-push'), the stored value associated with @('name')
is changed to be the cons of @('new-elem') onto the previous stored value; that
is, @('name') gets @('new-elem') pushed onto it.</p>"

  (progn$
   (raise "Under-the-hood definition not yet installed")
   nil))

(define sneaky-load (name state)
  :short "Load a value that was previously saved into the sneaky store."
  :long "<p>Example:</p>

@({
    (sneaky-save 'foo 3)
    (sneaky-load 'foo state) --> (mv 3 state)
})

<p>In the logic, this function reads from the ACL2 oracle.  Under the hood, we
redefine it so that it reads from a hash table and allows you to access the
values saved by, e.g., @(see sneaky-save) and @(see sneaky-push).</p>"

  (declare (ignore name))
  :returns (mv value state)
  (b* ((- (raise "Under-the-hood definition not yet installed"))
       ((mv ?err val state) (read-acl2-oracle state)))
    (mv val state)))

(define sneaky-alist (state)
  :short "Load an alist containing all values previously saved into the sneaky
store."
  :long "<p>Example:</p>

@({
    (sneaky-save 'foo 3)
    (sneaky-alist state) --> (mv '((foo . 3)) state)
})

<p>In the logic, this function reads from the ACL2 oracle.  Under the hood, we
redefine it so that it maps over a hash table and returns the values saved by,
e.g., @(see sneaky-save) and @(see sneaky-push).</p>"
  :returns (mv alist state)
  (b* ((- (raise "Under-the-hood definition not yet installed"))
       ((mv ?err val state) (read-acl2-oracle state)))
    (mv val state)))

(define sneaky-load-list (keys state)
  :short "Load a list of values that were previously saved into the sneaky
store."
  :long "<p>See @(see sneaky-load); this just loads a list of values instead of
a single value.</p>"
  :returns (mv (values true-listp :rule-classes :type-prescription)
               state)
  (b* (((when (atom keys))
        (mv nil state))
       ((mv first state) (sneaky-load (car keys) state))
       ((mv rest state)  (sneaky-load-list (cdr keys) state)))
    (mv (cons first rest) state)))


(define sneaky-delete (key)
  :short "Delete the data stored under a key from the sneaky store."
  :ignore-ok t :irrelevant-formals-ok t
  (raise "Under-the-hood definition not yet installed"))

(define sneaky-clear ()
  :short "Clear all data stored in the sneaky store."
  (raise "Under-the-hood definition not yet installed"))


; (depends-on "sneaky-raw.lsp")
(include-raw "sneaky-raw.lsp")


(define sneaky-save-mutator (ignored (val consp))
  :parents (sneaky-save)
  (declare (ignore ignored))
  (list val))

(define sneaky-save (name what)
  :short "Assign a value into the sneaky store."
  :long "<p>Example:</p>

@({
    (sneaky-save 'foo 3)
    (sneaky-load 'foo state) --> (mv 3 state)
})

<p>In the logic, @('sneaky-save') just returns @('nil').  Under the hood, we
update the sneaky store, e.g., by associating @('foo') with @('3').</p>

<p>See also @(see sneaky-mutate) for a more general way of manipulating
the sneaky store.</p>"
  :returns nil
  (sneaky-mutate 'sneaky-save-mutator nil (cons name what)))

(define sneaky-push-mutator ((previous consp)
                             (name-head consp))
  :parents (sneaky-push)
  (list (cons (car name-head)
              (cons (cdr name-head) (car previous)))))

(define sneaky-push (name what)
  :parents (sneaky)
  :short "Extend a value in the sneaky store."
  :long "<p>Example:</p>

@({
 (sneaky-save 'foo '(3))
 (sneaky-push 'foo 4)
 (sneaky-load 'foo state) --> (mv '(4 3) state)
})

<p>In the logic, @('sneaky-push') just returns @('nil').  Under the hood, we
update the sneaky store, updating @('name') by \"pushing\" a new value onto its
current value.  The accumulated values can later be accessed with @(see
sneaky-load).  See also @('sneaky-save').</p>"
  :returns nil
  (sneaky-mutate 'sneaky-push-mutator
                 (list name) (cons name what)))


(define sneaky-incf-mutator ((val consp)
                             (name-amount consp))
  :parents (sneaky-incf)
  :guard (acl2-numberp (cdr name-amount))
  (list (cons (car name-amount)
              (+ (cdr name-amount) (fix (car val))))))

(define sneaky-incf (name &optional ((amount acl2-numberp) '1))
  :short "Increment a value in the sneaky store."
  :long "<p>Example:</p>
@({
   (sneaky-save 'foo 3)
   (sneaky-incf 'foo)   ;; increment by 1
   (sneaky-incf 'foo 2) ;; increment by 2
   (sneaky-load 'foo state) --> (mv 6 state)
})

<p>In the logic, @('sneaky-incf') just returns @('nil').  Under the hood, we
update the sneaky store, incrementing the value of @('name') by the indicated
amount.  The accumulated values can later be accessed with @(see sneaky-load).
See also @('sneaky-save').</p>"
  :returns nil
  (sneaky-mutate 'sneaky-incf-mutator
                 (list name) (cons name amount)))


(local (defun fancy-mutator (prev user)
         (declare (xargs :guard (and (consp prev)
                                     (consp (car prev))
                                     (consp user)
                                     (consp (cdr user)))))
         (b* (((list* name1 name2 userval) user))
           (list (cons name1 (+ (fix (caar prev))
                                (fix (cdar prev))
                                (fix userval)))
                 (cons name2 (car prev))))))

(local
 (make-event
  (b* ((- (sneaky-save 'a 1))
       ((mv a0 state) (sneaky-load 'a state))
       (- (or (= a0 1)
              (er hard 'sneaky-tests "A0 failed~%")))
       (- (sneaky-incf 'a 3))
       ((mv a1 state) (sneaky-load 'a state))
       (- (or (= a1 4)
              (er hard 'sneaky-tests "A1 failed~%")))
       (- (sneaky-push 'a 5))
       ((mv a2 state) (sneaky-load 'a state))
       (- (or (equal a2 '(5 . 4))
              (er hard 'sneaky-tests "A2 failed~%")))
       (- (sneaky-mutate 'fancy-mutator
                         '(a) '(b c . 6)))
       ((mv alist state) (sneaky-alist state))
       (- (or (and (equal (assoc 'a alist) '(a 5 . 4))
                   (equal (assoc 'b alist) '(b . 15))
                   (equal (assoc 'c alist) '(c 5 . 4)))
              (er hard 'sneaky-alist "fancy-mutator failed: ~x0~%" alist))))
    (value '(value-triple :ok)))))


(define sneaky-pop-mutator ((stored-vals consp) name)
  :parents (sneaky-pop)
  (b* ((old-val (car stored-vals))
       ((when (atom old-val))
        (cw "; Sneaky-pop of empty ~x0: ~x1~%" name old-val)
        (list (cons name nil)))
       (new-val (cdr old-val)))
    (list (cons name new-val))))

(define sneaky-pop (name)
  :short "Pop the @(see car) off a list in the sneaky store."
  :long "<p>Example:</p>
@({
   (sneaky-save 'foo '(1 2 3))
   (sneaky-pop 'foo)
   (sneaky-load 'foo state) --> (mv '(2 3) state)
})

<p>In the logic, @('sneaky-pop') just returns @('nil').  Under the hood, we
update the sneaky store, removing the first element of the value of
@('name').</p>"
  :returns nil
  (declare (xargs :guard t))
  (sneaky-mutate 'sneaky-pop-mutator (list name) name))


(define sneaky-cw-mutator ((stored-vals consp) name)
  :parents (sneaky-cw)
  (declare (ignorable name))
  (cw "~x0" (car stored-vals)))

(define sneaky-cw (name)
  :short "Print a value from the sneaky store."
  :long "<p>Example:</p>
@({
    (sneaky-save 'foo 3)
    (sneaky-cw 'foo)     ; prints 3, returns nil
})

<p>In the logic, @('sneaky-cw') just returns nil.  Under the hood, we look
up the value of @('name') in the sneaky store and print it to the comment
window, e.g., using @(see cw).</p>"
  (sneaky-mutate 'sneaky-cw-mutator (list name) name))
