; Centaur Miscellaneous Books
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "tools/bstar" :dir :system)

(defttag sneaky-load)

(remove-untouchable 'read-acl2-oracle t)



(defund sneaky-mutate (fnname get-keys user-arg)
  (declare (xargs :guard (and (symbolp fnname)
                              (true-listp get-keys)))
           (ignorable fnname get-keys user-arg))
  ":Doc-Section Miscellaneous
Low-level access to the sneaky-state.~/

This is a low-level function for accessing and updating values that are saved
in an extralogical store.  In many cases, the simpler functions
~c[sneaky-save], ~c[sneaky-push], and ~c[sneaky-incf] suffice instead.

In the ACL2 logic, this function simply returns NIL, but what it actually does
depends on the ~c[FNNAME] argument passed in.  For example, the definition of
~c[sneaky-push] is the following:
~bv[]
 (defun sneaky-push (name new-elem)
   (sneaky-mutate 'sneaky-push-mutator (list name) (cons name new-elem)))
~ev[]
The symbol ~c[sneaky-push-mutator] refers to the following function:
~bv[]
 (defun sneaky-push-mutator (stored-vals name-elem-pair)
   (list (cons (car name-elem-pair)
               (cons (cdr name-elem-pair) (car stored-vals)))))
~ev[]

What is going on here?  Sneaky-push accesses a value stored under the name
~c[NAME], and re-stores it with ~c[NEW-ELEM] consed onto it.  How does this
occur?  A call
~bv[]
 (sneaky-mutate fnname get-keys user-arg)
~ev[]
calls the function ~c[f] named by ~c[fnname], in this case
~c[sneaky-push-mutator].  ~c[f] must always have two arguments.  The
first argument is the list of values currently associated with ~c[get-keys];
that is, ~c[sneaky-mutate] will look up each key in the store and pass a list
containing these stored values.  ~c[user-arg] is always passed as the second
argument.  So the two argments passed to ~c[sneaky-push-mutator] are a list
containing the stored value associated with ~c[name], and the cons of ~c[name]
itself onto ~c[new-elem].

~c[f] must return a single value, which should be an alist.  The store will be
updated by setting the keys of the alist to their corresponding values.  So in
the example above, the stored value associated with ~c[name] is updated to be
the cons of ~c[new-elem] onto the previous stored value; that is, ~c[name] gets
~c[new-elem] pushed onto it.~/~/"
  (prog2$
   (er hard? 'sneaky-mutate "Under-the-hood definition not yet installed")
   nil))


(defund sneaky-load (name state)

  ":Doc-Section Miscellaneous

Load a value that was previously saved using ~ilc[sneaky-save] or
~ilc[sneaky-push].~/

Example:
~bv[]
 (sneaky-save 'foo 3)
 (sneaky-load 'foo state) --> (mv 3 state)
~ev[]

In the logic, this function reads from the acl2-oracle.  Under the hood, we
redefine it so that it reads from a hash table and allows you to access the
values saved by ~ilc[sneaky-save] and ~ilc[sneaky-push].~/~/"

  (declare (xargs :guard t
                  :stobjs state)
           (ignore name))
  (prog2$
   (er hard? 'sneaky-load "Under-the-hood definition not yet installed")
   (mv-let (err val state)
           (read-acl2-oracle state)
           (declare (ignore err))
           (mv val state))))

(defund sneaky-alist (state)

  ":Doc-Section Miscellaneous

Load an alist containing all values previously saved using ~ilc[sneaky-save] or
~ilc[sneaky-push].~/

Example:
~bv[]
 (sneaky-save 'foo 3)
 (sneaky-alist state) --> (mv '((foo . 3)) state)
~ev[]

In the logic, this function reads from the acl2-oracle.  Under the hood, we
redefine it so that it maps over a hash table and returns the values saved by
~ilc[sneaky-save] and ~ilc[sneaky-push].~/~/"

  (declare (xargs :guard t
                  :stobjs state))
  (prog2$
   (er hard? 'sneaky-alist "Under-the-hood definition not yet installed")
   (mv-let (err val state)
           (read-acl2-oracle state)
           (declare (ignore err))
           (mv val state))))

(defun sneaky-load-list (keys state)
  (declare (xargs :guard t
                  :stobjs state))
  (if (atom keys)
      (mv nil state)
    (mv-let (val state)
      (sneaky-load (car keys) state)
      (mv-let (rest state)
        (sneaky-load-list (cdr keys) state)
        (mv (cons val rest)
            state)))))

(progn!
 (set-raw-mode t)

 (defvar *sneaky-state*
   (make-hash-table))

 ;; (defun sneaky-save (name what)
 ;;   (setf (gethash name *sneaky-load-table*) what)
 ;;   nil)

 ;; (defun sneaky-push (name what)
 ;;   (let ((val (gethash name *sneaky-load-table*)))
 ;;     (setf (gethash name *sneaky-load-table*)
 ;;           (cons what val)))
 ;;   nil)

 ;; (defun sneaky-incf-fn (name amount)
 ;;   (setf (gethash name *sneaky-load-table*)
 ;;         (+ (fix (gethash name *sneaky-load-table*))
 ;;            amount))
 ;;   nil)

 (defun sneaky-load (name state)
   (unless (live-state-p state)
     (er hard? 'sneaky-load "sneaky-load should only be used on live states"))
   (let ((val (gethash name *sneaky-state*)))
     (mv val state)))

 (defun sneaky-alist (state)
   (unless (live-state-p state)
     (er hard? 'sneaky-load "sneaky-load should only be used on live states"))
   (let (al)
     (maphash (lambda (k v)
                (push (cons k v) al))
              *sneaky-state*)
     (mv al state)))


 (defun sneaky-mutate (fnname get-keys user-arg)
   (b* ((st *the-live-state*)
        (world (w st))
        (stobjs-in (fgetprop fnname 'stobjs-in :none world))
        (stobjs-out (fgetprop fnname 'stobjs-out :none world))
        ((when (not (equal stobjs-in '(nil nil))))
         (er hard 'sneaky-mutate
             "FNNAME must be an ACL2 function symbol of 2 non-stobj args; ~x0 is not~%"
             fnname))
        ((when (not (equal stobjs-out '(nil))))
         (er hard 'sneaky-mutate
             "FNNAME must be an ACL2 function symbol that returns a single value; ~x0 is not~%"
             fnname))
        (get-ins (loop for key in get-keys collect
                       (gethash key *sneaky-state*)))
        (starfn (*1*-symbol fnname))
        (result (funcall starfn get-ins user-arg)))
     (loop while (consp result) do
           (b* ((head (car result)))
             (when (consp head)
               (setf (gethash (car head) *sneaky-state*) (cdr head)))
             (setq result (cdr result))))
     nil)))



(defun sneaky-save-mutator (ignored val)
  (declare (ignore ignored)
           (xargs :guard (consp val)))
  (list val))

(defun sneaky-save (name what)
  ":Doc-Section Miscellaneous

Save a value for later retrieval by ~ilc[sneaky-load].~/

Example:
~bv[]
 (sneaky-save 'foo 3)
 (sneaky-load 'foo state) --> (mv 3 state)
~ev[]

In the logic, ~c[sneaky-save] just returns ~c[nil].  Under the hood, we update
a hash table, e.g., by associating ~c[foo] with ~c[3].

This function is mainly intended for debugging.  Particularly, suppose you want
to inspect some intermediate value from a function that is somehow \"deep\"
inside your computation.  If your function doesn't involve state, you can't use
state globals.  Adding state throughout the call tree could be really
difficult, especially for a one-off investigation.  In this kind of scenario,
~c[sneaky-save] and ~c[sneaky-load] may be very handy.

See also ~il[sneaky-mutate] for a more general way of manipulating
sneakily saved values.~/~/"
  (declare (xargs :guard t))
  (sneaky-mutate 'sneaky-save-mutator
                 nil (cons name what)))

(defun sneaky-push-mutator (previous name-head)
  (declare (xargs :guard (and (consp previous)
                              (consp name-head))))
  (list (cons (car name-head)
              (cons (cdr name-head) (car previous)))))

(defun sneaky-push (name what)
  ":Doc-Section Miscellaneous

Extend a value for later retrieval by ~ilc[sneaky-load].~/

Example:
~bv[]
 (sneaky-save 'foo '(3))
 (sneaky-push 'foo 4)
 (sneaky-load 'foo state) --> (mv (4 3) state)
~ev[]

In the logic, ~c[sneaky-push] just returns ~c[nil].  Under the hood, we update
a hash table by \"pushing\" a new value onto its current value.  The
accumulated values can later be accessed with ~ilc[sneaky-load].  See also
~c[sneaky-save].

See also ~il[sneaky-mutate] for a more general way of manipulating
sneakily saved values.~/~/"
  (declare (xargs :guard t))
  (sneaky-mutate 'sneaky-push-mutator
                 (list name) (cons name what)))



(defun sneaky-incf-mutator (val name-amount)
  (declare (xargs :guard (and (consp val)
                              (consp name-amount)
                              (acl2-numberp (cdr name-amount)))))
  (list (cons (car name-amount)
              (+ (cdr name-amount) (fix (car val))))))

(defun sneaky-incf-fn (name amount)
  (declare (xargs :guard (acl2-numberp amount)))
  (sneaky-mutate 'sneaky-incf-mutator
                 (list name) (cons name amount)))


(defmacro sneaky-incf (name &optional (amount '1))
  ":Doc-Section Miscellaneous

Increment a value for later retrieval by ~ilc[sneaky-load].~/

Example:
~bv[]
 (sneaky-save 'foo 3)
 (sneaky-incf 'foo 4)
 (sneaky-load 'foo state) --> (mv 7 state)
~ev[]

In the logic, ~c[sneaky-incf] just returns ~c[nil].  Under the hood, we update
a hash table by incrementing a currently saved value.  The accumulated values
can later be accessed with ~ilc[sneaky-load].  See also ~c[sneaky-save].

See also ~il[sneaky-mutate] for a more general way of manipulating
sneakily saved values.~/~/"
  `(sneaky-incf-fn ,name ,amount))


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




(defun sneaky-pop-mutator (stored-vals name)
  (declare (xargs :guard (consp stored-vals)
                  :guard-debug t))
  (b* ((old-val (car stored-vals))
       ((when (atom old-val))
        (cw "; Sneaky-pop of empty ~x0: ~x1~%" name old-val)
        (list (cons name nil)))
       (new-val (cdr old-val)))
    (list (cons name new-val))))

(defun sneaky-pop (name)
  (declare (xargs :guard t))
  (sneaky-mutate 'sneaky-pop-mutator (list name) name))


(defun sneaky-cw-mutator (stored-vals name)
  (declare (xargs :guard (consp stored-vals))
           (ignorable name))
  (cw "~x0" (car stored-vals)))

(defun sneaky-cw (name)
  (declare (xargs :guard t))
  (sneaky-mutate 'sneaky-cw-mutator (list name) name))
