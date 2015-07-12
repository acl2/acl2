; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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

; Jared: what's this file for?  It's not certifiable, so I'm
; renaming it to a .lsp extension for Make compatibility
(error "is anyone using this?  If so please remove this message.")
#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
;; gacc-definitions.lisp
;; John D. Powell
;(in-package "GACC")

;;
;; This file isolates gacc definitions and types. The file currently
;; contains the following ACL2 constructs as they occur in the gacc book:
;; - defun
;; - defund
;; - defstub
;; - defchoose
;; - defthm
;; - in-theory
;;

(error "Is anyone using this?  If so please remove this message.")

;bzo
(defthm append-nil
  (implies
   (true-listp x)
   (equal (append x nil) x)))

(defthm single-record-reduction
  (iff (equal r1 r2)
       (and (equal (g a r1) (g a r2))
            (equal (s a 0 r1) (s a 0 r2))))
  :rule-classes nil)

;;
;; This function allows us to read out a set of index locations from a
;; record.
;;

(defun g* (list r)
  (declare (type t list r))
  (if (consp list)
      (cons (g (car list) r)
            (g* (cdr list) r))
    nil))

(defthm g*-extensionality-2
  (implies
   (equal x y)
   (iff (equal (g* a x)
               (g* a y)) t)))

(defthm g*-list-equal-reduction
  (implies
   (equal (g* list r1)
          (g* list r2))
   (iff (equal (g* list (clr a r1))
               (g* list (clr a r2))) t))
  :hints (("goal" :in-theory (enable g-of-s-redux))))

;;
;; This function zero's out a set of index locations in a record.
;;

(defun z* (list r)
  (declare (type t list r))
  (if (consp list)
      (let ((r (clr (car list) r)))
        (z* (cdr list) r))
    r))

;;
;; A guardless version of member - remove this, not that we have memberp bzo
;;

(defun memberx (a list)
  (declare (type t a list))
  (if (consp list)
      (if (equal a (car list)) t
        (memberx a (cdr list)))
    nil))

(defthm z*-list-of-s
  (implies
   (memberx a list)
   (equal (z* list (s a v r))
          (z* list r)))
  :hints (("Subgoal *1/2" :cases ((equal a (car list))))))

(defthm z*-list-of-clr
  (implies
   (memberx a list)
   (equal (z* list (clr a r))
          (z* list r)))
  :hints (("Subgoal *1/2" :cases ((equal a (car list))))))

(defun z*-induction (list r1 r2)
  (declare (type t list r1 r2))
  (if (consp list)
      (let ((r1 (clr (car list) r1))
            (r2 (clr (car list) r2)))
        (z*-induction (cdr list) r1 r2))
    (cons r1 r2)))


;;
;; Useful theorem ..
;;

(defthm generalized-record-reduction
  (iff (equal r1 r2)
       (and (equal (g* list r1) (g* list r2))
            (equal (z* list r1) (z* list r2))))
  :hints (("goal" :induct (z*-induction list r1 r2)))
  :rule-classes nil)

;; A little trick we play to keep from exposing undesired consp's to
;; the theorem prover.  A non-consp spec is interpreted to mean an
;; atomic location in the record.

(defun sconsp (spec)
  (declare (type t spec))
  (consp spec))

(defthm consp-implies-sconsp
  (implies
   (consp x)
   (sconsp x)))

(defthm not-consp-implies-not-sconsp
  (implies
   (not (consp x))
   (not (sconsp x))))

(in-theory
 (disable
  sconsp
  ))

;; c* is a function that combines (what in gacc we call) g* and s*
;; into a single function that can be viewed as a copy from one record
;; to another under the control of a "spec"

(defun c* (spec r1 r2)
  (declare (type t spec r1 r2))
  (if (consp spec)
      (if (consp (car spec))
          (let ((v1 (g (caar spec) r1))
                (v2 (g (caar spec) r2)))
            (let ((v (if (sconsp (cdar spec)) (c* (cdar spec) v1 v2) v1)))
              (let ((r2 (s (caar spec) v r2)))
                (c* (cdr spec) r1 r2))))
        (c* (cdr spec) r1 r2))
    r2))

(defthm open-c*
  (and
   (implies
    (consp spec)
    (equal (c* spec r1 r2)
           (if (consp (car spec))
               (let ((v1 (g (caar spec) r1))
                     (v2 (g (caar spec) r2)))
                 (let ((v (if (sconsp (cdar spec)) (c* (cdar spec) v1 v2) v1)))
                   (let ((r2 (s (caar spec) v r2)))
                     (c* (cdr spec) r1 r2))))
             (c* (cdr spec) r1 r2))))
   (implies
    (not (consp spec))
    (equal (c* spec r1 r2) r2))))

(in-theory
 (disable
  c*
  ))

(defun keys (spec)
  (declare (type t spec))
  (if (consp spec)
      (if (consp (car spec))
          (cons (caar spec)
                (keys (cdr spec)))
        (keys (cdr spec)))
    nil))

;; A useful, common sense sort of predicate for specs.

(defun unique-spec (spec)
  (declare (type t spec))
  (if (consp spec)
      (if (consp (car spec))
          (and (not (memberx (caar spec) (keys (cdr spec))))
               (implies (sconsp (cdar spec))
                        (unique-spec (cdar spec)))
               (unique-spec (cdr spec)))
        (unique-spec (cdr spec)))
    t))

(defun c*-induction (spec r1 r2)
  (declare (type t spec r1 r2))
  (if (consp spec)
      (if (consp (car spec))
          (let ((v1 (g (caar spec) r1))
                (v2 (g (caar spec) r2)))
            (let ((v (if (sconsp (cdar spec)) (c* (cdar spec) v1 v2) v1)))
              (let ((r2 (s (caar spec) v r2)))
                (c*-induction (cdr spec) r1 r2))))
        (c*-induction (cdr spec) r1 r2))
    r2))

;;
;; There are several things we will need to prove about c*.
;; Here are the ones we needed for these examples.
;;

(defthm not-member-c*-s
  (implies
   (not (memberx a (keys spec)))
   (equal (c* spec r1 (s a v r2))
          (s a v (c* spec r1 r2))))
  :hints (("goal" :induct (c*-induction spec r1 r2))))

(defthm not-member-c*-s-left
  (implies
   (not (memberx a (keys spec)))
   (equal (c* spec (s a v r1) r2)
          (c* spec r1 r2)))
  :hints (("goal" :induct (c*-induction spec r1 r2))))


(defun c*-c*-induction (spec r1 r2 r3)
  (declare (type t spec r1 r2 r3))
  (if (consp spec)
      (if (consp (car spec))
          (let ((v1 (g (caar spec) r1))
                (v2 (g (caar spec) r2))
                (v3 (g (caar spec) r3)))
            (let ((v (if (sconsp (cdar spec))
                         (c*-c*-induction (cdar spec) v1 v2 v3)
                       (cons v1 v1))))
              (let ((v1 (car v))
                    (v2 (cdr v)))
                (let ((r2 (s (caar spec) v1 r2))
                      (r3 (s (caar spec) v2 r3)))
                  (c*-c*-induction (cdr spec) r1 r2 r3)))))
        (c*-c*-induction (cdr spec) r1 r2 r3))
    (cons r2 r3)))

(defthm cdr-c*-c*-induction
  (equal (cdr (c*-c*-induction spec r1 r2 r3))
         (c* spec r1 r3)))

(defthm c*-c*-reduction
  (implies
   (unique-spec spec)
   (equal (c* spec (c* spec r1 r2) r3)
          (c* spec r1 r3)))
  :hints (("goal" :induct (c*-c*-induction spec r1 r2 r3))))

;;
;; Here is a simple example of using these techniques to
;; specify the d/u characteristics of a function.
;;

;; The records we are considering are stricly untyped.  We use "type"
;; predicates to limit the applicablity of the various theorems we
;; will want to apply.  The existentionality theorem, in particular,
;; is a _very_ strong theorem and we want to target its application
;; and minimize the overhead required for false attempts. For this
;; reason we invent a simple "type" system.

(defun type-b (x)
  (declare (type t x)
           (ignore x))
  t)

(defthm type-b-forward
  (implies
   (not (type-b x))
   nil)
  :rule-classes (:forward-chaining))

(defthm type-b-s
  (iff (type-b (s a v r))
       (type-b r)))

(defthm type-b-c*
  (iff (type-b (c* spec r1 r2))
       (type-b r1)))

;; The type "spec" is an outline of how we conceptualize the data
;; structure.  For this type, we imagine a simple record with three
;; fields.

(defun type-b-spec ()
  (declare (xargs :verify-guards t))
  `(
    (:slota)
    (:slotb)
    (:slotc)
    ))

(defthm unique-spec-type-b-spec
  (unique-spec (type-b-spec)))

(defthm true-listp-type-b-spec
  (true-listp (type-b-spec)))

(defthm sconsp-type-b-spec
  (sconsp (type-b-spec)))

;;
;; The type "keys" are simply the names of the slots in the top level
;; record.
;;

(defun type-b-keys ()
  (declare (xargs :verify-guards t))
  `(:slota :slotb :slotc))

(defthm type-b-extensionality
  (implies
   (and
    (type-b r1)
    (type-b r2))
   (iff (equal r1 r2)
        (and (equal (g* (type-b-keys) r1)
                    (g* (type-b-keys) r2))
             (equal (z* (type-b-keys) r1)
                    (z* (type-b-keys) r2)))))
  :hints (("goal" :in-theory nil
           :use ((:instance generalized-record-reduction (list (type-b-keys)))))))

;; We can't verify guards here because we don't know the type of g.
;; Don't worry, we'll get to that later.

(defun goo (r)
  (let* (
         (r (s :slotb (- (g :slotb r) (g :slotc r)) r))
         (r (s :slota (1+ (g :slota r)) r))
         (r (s :slotc (+ (g :slota r) (g :slotb r)) r))
         )
    r))

(defun goo@ (r) (goo r))

(defthm type-b-goo
  (type-b (goo r)))

(in-theory
 (disable
  type-b
  (type-b)
  (:type-prescription type-b)
  ))

(in-theory
 (disable
  type-b-spec
  ))

;; Note that proving the following should allow us to conclude
;;
;; (= (z* spec (goo r)) (z* spec r))
;;
;; for any spec of which (type-b-spec) is a subset (subbag-p?). (yay)

(defthm goo-du
  (implies
   (type-b r)
   (equal (goo r)
          (c* (type-b-spec) (goo@ (c* (type-b-spec) r nil)) r))))

(in-theory
 (disable
  (type-b-spec)
  (:type-prescription type-b-spec)
  ))

(in-theory
 (disable
  goo
  goo@
  ))

;;
;; A more complex example involving recursive types and using the
;; theorem we proved above.
;;

(defun type-a (x)
  (declare (type t x)
           (ignore x))
  t)

(defthm type-a-forward
  (implies
   (not (type-a x))
   nil)
  :rule-classes (:forward-chaining))

(defthm type-a-s
  (iff (type-a (s a v r))
       (type-a r)))

(defthm type-a-c*
  (iff (type-a (c* spec r1 r2))
       (type-a r1)))

;; The type spec includes a recursive data structure and field
;; containing the data structure we described above.

(defun type-a-spec (n)
  (declare (type (integer 0 *) n))
  (if (zp n) nil
    `(
      (:slot1 ,@(type-a-spec (1- n)))
      (:slot2 ,@(type-b-spec))
      (:slot3))))

(defthm true-listp-type-a-spec
  (true-listp (type-a-spec n)))

(defthm sconsp-type-a-spec
  (implies
   (not (zp n))
   (sconsp (type-a-spec n))))

(defthm unique-spec-type-a-spec
  (unique-spec (type-a-spec n)))

;; A declarative statement about the contents of a type-a record.
;; Note that we don't have a type-a statement for :slot1.  This
;; helps us restrain the application of some of our rules in the
;; recursive case

(defthm type-a-body
  (implies
   (type-a r1)
   (and (type-b (g :slot2 r1))
        )))

(defun type-a-keys ()
  (declare (xargs :verify-guards t))
  `(:slot1 :slot2 :slot3))

(defthm type-a-extensionality
  (implies
   (and
    (type-a r1)
    (type-a r2))
   (iff (equal r1 r2)
        (and (equal (g* (type-a-keys) r1)
                    (g* (type-a-keys) r2))
             (equal (z* (type-a-keys) r1)
                    (z* (type-a-keys) r2)))))
  :hints (("goal" :in-theory nil
           :use ((:instance generalized-record-reduction (list (type-a-keys)))))))

(defun foo (n r)
  (if (zp n) r
    (let* ((r (s :slot1 (foo (1- n) (g :slot1 r)) r))
           (r (s :slot3 (1- (g :slot3 r)) r))
           (r (s :slot2 (goo (g :slot2 r)) r))
           )
      r)))

(defun foo@ (n r)
  (foo n r))

;; This rule is formulated to limit applicability in recursive
;; proofs.

(defthm type-a-foo
  (implies
   (not (zp n))
   (type-a (foo n r1))))

(in-theory
 (disable
  type-a
  (type-a)
  (:type-prescription type-a)
  ))

(defthm foo-du
  (implies
   (type-a r)
   (equal (foo n r)
          (c* (type-a-spec n) (foo@ n (c* (type-a-spec n) r nil)) r)))
  :hints (("goal" :induct (foo n r))))

;; These rules should be added to defthing ..

(defthm g-s-int-equality
  (implies
   (equal (g-int x) (g-int y))
   (iff (equal (s-int 0 x) (s-int 0 y))
        (equal x y)))
  :hints (("goal" :in-theory (enable g-int s-int))))

(defun fix-list (list)
  (declare (type t list))
  (if (true-listp list) list nil))

(defthm g-s-list-equality
  (implies
   (equal (g-list x) (g-list y))
   (iff (equal (s-list 0 x) (s-list 0 y))
        (equal x y)))
  :hints (("goal" :in-theory (enable g-list s-list))))


;; This is how we generalize the typed record stuff to
;; finite records of mixed-type ..

(defun key-get (key v)
  (declare (type t key v))
  (case key
        (:key1 (k1-get v))
        (:key2 (k2-get v))
        (t     v)))

(defun key-set (key value g)
  (declare (type t key value g))
  (case key
        (:key1 (k1-set value g))
        (:key2 (k2-set value g))
        (t     value)))

(defun key-fix (key value)
  (declare (type t key value))
  (case key
        (:key1 (k1-fix value))
        (:key2 (k2-fix value))
        (t      value)))

(defun g+ (key r)
  (declare (type t key r))
  (key-get key (g key r)))

(defun s+ (key v r)
  (declare (type t key r))
  (s key (key-set key v (g key r)) r))


;;
;; A new type ..
;;

(defun type-c (x)
  (declare (type t x)
           (ignore x))
  t)

(defthm type-c-forward
  (implies
   (not (type-c x))
   nil)
  :rule-classes (:forward-chaining))

(defthm type-c-s
  (iff (type-c (s a v r))
       (type-c r)))

(defthm type-c-c*
  (iff (type-c (c* spec r1 r2))
       (type-c r1)))

(defun type-c-spec ()
  (declare (xargs :verify-guards t))
  `(
    (:key1)
    (:key2)
    ))

(defthm unique-spec-type-c-spec
  (unique-spec (type-c-spec)))

(defthm true-listp-type-c-spec
  (true-listp (type-c-spec)))

(defthm sconsp-type-c-spec
  (sconsp (type-c-spec)))

(defun type-c-keys ()
  (declare (xargs :verify-guards t))
  `(:key1 :key2))

(defthm type-c-extensionality
  (implies
   (and
    (type-c r1)
    (type-c r2))
   (iff (equal r1 r2)
        (and (equal (g* (type-c-keys) r1)
                    (g* (type-c-keys) r2))
             (equal (z* (type-c-keys) r1)
                    (z* (type-c-keys) r2)))))
  :hints (("goal" :in-theory nil
           :use ((:instance generalized-record-reduction (list (type-c-keys)))))))


(defthm integerp-implies-acl2-numberp
  (implies
   (integerp x)
   (acl2-numberp x)))

(defun hoo (r)
  (declare (type t r))
  (let* ((r (s+ :key1 (+ (g+ :key1 r) 2) r))
         (r (s+ :key2 (append (g+ :key2 r) (g+ :key2 r)) r)))
    r))

(defun hoo@ (r)
  (declare (type t r))
  (hoo r))

(defthm type-c-hoo
  (type-c (hoo r)))

(in-theory
 (disable
  type-c
  (type-c)
  (:type-prescription type-c)
  ))

(in-theory
 (disable
  type-c-spec
  ))

(defthm hoo-du
  (implies
   (type-c r)
   (equal (hoo r)
          (c* (type-c-spec) (hoo@ (c* (type-c-spec) r nil)) r))))

(in-theory
 (disable
  (type-c-spec)
  (:type-prescription type-c-spec)
  ))

(in-theory
 (disable
  hoo
  hoo@
  ))


;; Generalized Accessors
;;
;; Predicates over the state are representative of the class of
;; functions we call generalized accessors.  These functions pick
;; apart the state and return some new value (a boolean in the
;; case of predicates).  We can characterize the "use" pattern of
;; such generalized accessors as follows:

;bzo
(defthm integerp-implies-rationalp
  (implies
   (integerp x)
   (rationalp x)))

(defun a-predicate (r)
  (declare (type t r))
  (<= 0 (g+ :key1 r)))

(defun a-predicate@ (r)
  (declare (type t r))
  (a-predicate r))

(defthm a-predicate-u
  (implies
   (type-c r)
   (equal (a-predicate  r)
          (a-predicate@ (c* '((:key1)) r nil)))))

;; Generalized Updaters (raw)
;;
;; Functions that update the value of a record can also be
;; characterized.  Making the operation of such functions explicit
;; enables us to better compose them with other functions.

(defun impose-value (v r)
  (declare (type t v r))
  (s :key2 v r))

(defun impose-value@ (v r)
  (declare (type t v r))
  (impose-value v r))

(defthm impose-value-d
  (implies
   (type-c r)
   (equal (impose-value v r)
          (c* '((:key2)) (impose-value@ v nil) r))))

;; Generalized Updaters (typed)
;;
;; Note that the "typed" records care about the shape of the "value
;; container" that lives in the raw record data structure.  Thus,
;; typed definition (s+) implicitly requires use as well.

(defun impose-typed-value (v r)
  (declare (type t v r))
  (s+ :key2 v r))

(defun impose-typed-value@ (v r)
  (declare (type t v r))
  (impose-typed-value v r))

(defthm impose-typed-value-d
  (implies
   (type-c r)
   (equal (impose-typed-value v r)
          (c* '((:key2)) (impose-typed-value@ v (c* '((:key2)) r nil)) r))))


;;
;; Paths
;;

;; It is also possible to specify indicies into hierarcial data
;; structures.  Rather than using an atom as a key, we can use
;; a list of atoms which are applied recursively.

(defun g-path (path r)
  (if (consp path)
      (g-path (cdr path) (g (car path) r))
    r))

(defun s-path (path v r)
  (if (consp path)
      (s (car path) (s-path (cdr path) v (g (car path) r)) r)
    v))

;; Hierarcical paths make some things potentially more difficult .. like
;; describing address orthoganality.  Special functions may need to be
;; be defined for talking about sub/super-paths ..
;;
;; Perhaps we can deal with some of these issues by flattening (smashing) the
;; hierarcial addresses (path) outright ..

;; smash produces a list of all of the possible addresses affected by
;; g-path/s-path ..

(defun smash (path)
  (if (consp path)
      (cons path (smash (cdr path)))
    nil))

;; Note : (unique (smash path))

;; The question is: should g-path/s-path be treated as atomic?
;; Or should they open up?

#|
(defthm g-g-composition
  (equal (g a (g b r))
         (g-path (list a b) r)))

(defthm g-path-g-composition
  (equal (g-path path (g a r))
         (g-path (cons a path) r)))

(defthm g-g-path-composition
  (equal (g a (g-path path r))
         (g (append path '(,a)) r)))

(defthm g-over-s-path
  (equal (g a (s-path (cons a list) v r))
         (s-path list v (g a r))))

(defthm g-path-over-s-path
  (equal (g-path path1 (s-path (append path1 list) v r))
         (s-path list v (g-path path1 r))))

(defthm g-path-of-s-path
  (equal (g-path (append path1 list) (s-path path1 v r))
         (g-path list v)))

(defthm s-s-composition
  (implies
   (equal rx (g a r))
   (equal (s a (s b v rx) r)
          (s-path (list a b) v r))))

(defthm s-s-path-composition
  (implies
   (equal rx (g a r))
   (equal (s a (s-path path1 v rx) r)
          (s-path (cons a path1) v r))))

(defthm s-path-s-composition
  (implies
   (equal rx (g-path path1 r))
   (equal (s-path path1 (s a v rx) r)
          (s-path (append path1 `(,a)) v r))))

(defthm s-path-s-path-composition
  (implies
   (equal rx (g-path path1 r))
   (equal (s-path path1 (s-path path2 v rx) r)
          (s-path (append path1 path2) v r))))


|#

#|

;; The map function (m* here) is a generalized copy command that enables
;; us to change levels of abstraction.

(defun m* (list1 r1 list2 r2)
  (if (and (consp list1)
           (consp list2))
      (let ((v1 (g-path (car list1) r1)))
        (let ((r2 (s-path (car list2) v1 r2)))
          (m* (cdr list1) (cdr list2) r2)))
    r2))

(defun remap (a list1 list2)
  (if (consp list1)
      (if (equal a (car list1))
          (car list2)
        (remap a (cdr list1) (cdr list2)))
    list2))

(defun g* (list ram)
  (if (consp list)
      (cons (g-path (car list) ram)
            (g* (cdr list) ram))
    nil))

(defun s* (list1 list2 ram)
  (if (and (consp list1)
           (consp list2))
      (let ((ram (s-path (car list1) (car list2) ram)))
        (s* (cdr list1) (cdr list2) ram))
    ram))

;; Or, perhaps it would be easer to just generalize the copy function to take
;; a list of address pairs (from -> to).  Lets call this new function c*

(defun c* (pair r1 r2)
  (if (consp pair)
      (let ((v1 (g-path (car (car pair)) r1)))
        (let ((r2 (s-path (cdr (car pair)) v1 r2)))
          (c* (cdr pair) r1 r2)))
    r2))

;; Here is your idealized, general mapping function.
;;
;; Presumably (perm (def m) d) and (perm (use m) u)
;;
;; This function extracts data from a low level record (r1) using
;; access patterns that are familiar to the low level world,
;; translates them into the high level record using the utility
;; mapping function, and then applies them to the high level record
;; (r2) using patterns familiar to that level.

(defun m* (m u r1 d r2)
  (c* (pair d) (c* m (c* (pair u) r1 nil) nil) r2))

;; The primary limitation: the whole process is a 1 to 1 mapping.  Thus
;; there is no built-in provision for widening/narrowing.  Of course,
;; widening and narrowing involve function application.  Thus it would
;; be easy to imagine the following scenario in which we have an
;; intermediate representation that is widened or narrowed as necessary
;; (by mapfn) before being copied to its final destination.

(defun map< (a m)
  (remap a (def m) (use m)))

(defun map> (a m)
  (remap a (use m) (def m)))

;; Some questions:
;;
;; 1. can we eliminate (perm ..) hypothesis in these functions to make
;; them more efficient to reason about?
;;
;; 2. can we say things about the uniqeness of (map> a m) without
;; fully evaluating it if we know stuff about, say m?

|#

#|

;; The next issue is how to represent virtual data structures.
;; Virtual data structures are data structures implemented within
;; other data structures.  A stack in a linear address space is an
;; example of a virtual data structure.
;;
;; What may be needed is a generalized "map" function that can
;; move data from one data structure into another data structure.
;; Lift and push functions may be sufficient for this task.  The
;; most general lift function might just extract a set of addresses
;; into a list.  The push function might just map a list of values
;; into new address locations.  Of course, c* could be implemented
;; using lift and push, just as we do it now.  We could then develop
;; intermediate functions that would massage the data into a form
;; that makes sense to us.

(defun points (spec)
  (if (consp spec)
      (if (consp (car spec))
          (let ((v1 (g (caar spec) r1)))
            (let ((n (if (sconsp (cdar spec)) (lift (cdar spec) v1) 1)))
              (+ n  (points (cdr spec)))))
        (points (cdr spec)))
    0))

(defun lift (spec r1)
  (if (consp spec)
      (if (consp (car spec))
          (let ((v1 (g (caar spec) r1)))
            (let ((v (if (sconsp (cdar spec)) (lift (cdar spec) v1) `(,v1))))
              (append v (lift (cdr spec) r1))))
        (lift (cdr spec) r1))
    nil))

(defun spoints (spec)
  (if (sconsp spec) (points spec) 1))

(defun push (spec list r1)
  (if (consp spec)
      (if (consp (car spec))
          (let ((v1 (g (caar spec) r1)))
            (let ((r1 (if (sconsp (cdar spec))
                          (push (cdar spec) list r1)
                        (s (caar spec) (car list) r1)))
                  (list (nthcdr (spoints (cdar spec)) list)))
              (push (cdr spec) list r1)))
        (push (cdr spec) list r1))
    r1))

(defun flat-keys (spec)
  (if (consp spec)
      (if (consp (car spec))
          (cons (caar spec)
                (flat-keys (cdr spec)))
        (flat-keys (cdr spec)))
    nil))

(defthm g-over-push
  (equal (g a (push spec list r1))
         (if (member a (flat-keys spec))
             (push (get a spec) (nthcdr (points (spec-head a spec)) list) (g a r1))
           (g a r1))))

(defthm lift-s
  (equal (lift spec (s a v r))
         (if (member a (flat-keys spec))
             (update-nth (location a spec) v (lift spec r))
           (lift spec r))))

|#


#|

  Security Policy Exploration

(defthm
  (implies
   (equal (c* (dia seg) st1 nil)
          (c* (dia seg) st2 nil))
   (equal (c* (dia seg) (step st1) nil)
          (c* (dia seg) (step st2) nil))))

(defthm
  (implies
   (equal (c* (dia seg) st1 nil)
          (c* (dia seg) st2 nil))
   (equal (c* (dia seg) (c* def (step (c* use st nil)) st) nil)
          (c* (dia seg) (c* def (step (c* use st nil)) st) nil))))

(defthm
  (implies
   (equal (c* (dia seg) st1 nil)
          (c* (dia seg) st2 nil))
   (equal (c* (dia seg) (step (c* use st1 nil)) nil)
          (c* (dia seg) (step (c* use st2 nil)) nil))))

(defthm
  (implies
   (equal (c* (dia seg) st1 nil)
          (c* (dia seg) st2 nil))
   (equal (c* (dia seg) (step (c* use st2 nil)) nil)
          (c* (dia seg) (step (c* use st2 nil)) nil))))


|#



#|-*-Lisp-*-==================================================================|#
#|                                                                              |#
#|                                                                              |#
#|                                                                              |#
#|                                                                              |#
#| coi: Computational Object Inference                                       |#
#|============================================================================|#

;; I like this function better than the very similar gacc::blk.  I'd like to
;; change gacc::blk to act like this function.  -ews

;do we want this, or the wrapped version, or both?
;what should this do when base is not an integerp?
;previously we got gross behavior like (addr-range t 4) = '(t 1 2 3). Now we call ifix on base.
(defund addr-range (base k)
  (declare (type t base)
           (type (integer 0 *) k)
           (xargs :measure (acl2-count k)))
  (if (zp k)
      nil
    (cons (ifix base)
          (addr-range (+ 1 (ifix base)) (1- k)))))

;consider disabling (:executable-counterpart addr-range) as we do for gacc::sblk?

(defthm addr-range-when-size-is-not-an-integerp
  (implies (not (integerp size))
           (equal (addr-range base size)
                  nil))
  :hints (("Goal" :in-theory (enable addr-range))))

(defthm addr-range-when-size-is-not-positive
  (implies (<= size 0)
           (equal (addr-range base size) nil))
  :hints (("Goal" :in-theory (enable addr-range))))

(defthm addr-range-when-base-is-not-an-integerp
  (implies (not (integerp base))
           (equal (addr-range base size)
                  (addr-range 0 size)))
  :hints (("Goal" :in-theory (enable addr-range))))

(defthm addr-range-when-size-is-0
  (equal (addr-range base 0)
         nil)
  :hints (("Goal" :in-theory (enable addr-range))))

(defthm addr-range-when-size-is-1
  (equal (addr-range base 1)
         (list (ifix base)))
  :hints (("Goal" :expand (addr-range base 1)
           :in-theory (enable addr-range))))

(defthm consp-of-addr-range
  (equal (consp (addr-range base size))
         (and (integerp size)
              (< 0 size)))
  :hints (("Goal" :in-theory (enable addr-range))))

(defthm addr-range-iff
  (iff (addr-range ptr size)
       (not (zp size)))
  :hints (("Goal" :in-theory (enable addr-range))))

(defthm len-of-addr-range
  (equal (len (addr-range base size))
         (nfix size))
  :hints (("Goal" :in-theory (enable addr-range))))

(defthm car-of-addr-range
  (equal (car (addr-range base size))
         (if (zp size)
             nil
           (ifix base)))
  :hints (("Goal" :in-theory (enable addr-range))))

(defthm cdr-of-addr-range
  (equal (cdr (addr-range ad numbytes))
         (if (zp numbytes)
             nil
           (addr-range (+ 1 (ifix ad)) (+ -1 numbytes))))
  :hints (("Goal" :expand  (addr-range ad numbytes)
           :in-theory (enable addr-range))))


;might be expensive, so we disable it..
(defthmd memberp-when-x-is-an-integer-listp
  (implies (and (integer-listp x)
                (not (integerp a)))
           (not (bag::memberp a x))))

(defthm integer-listp-of-addr-range
  (integer-listp (addr-range base k))
  :hints (("Goal" :in-theory (enable addr-range))))

;expensive?
(defthm memberp-of-addr-range
  (equal (bag::memberp k (addr-range i j))
         (and (<= (ifix i) k)
              (< k (+ (ifix i) j))
              (integerp j)
              (<= 0 j)
              (integerp k)))
  :hints (("Goal" :in-theory (enable ifix addr-range))))

(defthm memberp-of-addr-range-base
  (equal (bag::memberp base (addr-range base k))
         (and (< 0 k)
              (integerp base)
              (integerp k))))

;bzo. just use memberp-of-cons?
(defthm memberp-cons-addr-range
  (equal (bag::memberp addr1 (cons addr2 (addr-range addr3 k)))
         (or (equal addr1 addr2)
             (bag::memberp addr1 (addr-range addr3 k)))))

(defthm addr-range-of-ifix
  (equal (addr-range (ifix base) size)
         (addr-range base size))
  :hints (("Goal" :in-theory (enable addr-range ifix))))

;bzo do we want this?
(defthm addr-range-plus
  (implies (and (< addr (+ base k))
                (<= base addr)
                (integerp k)
                (< 0 k)
                (integerp addr)
                (integerp base))
           (bag::memberp addr (addr-range base k))))

;bzo do we want this?
(defthm addr-range-plus-corollary
  (implies (and (equal addr (+ base j)) ;j is a free variable
                (< j k)
                (acl2::natp j)
                (integerp k)
;                (< 0 k)
                (integerp base))
           (bag::memberp addr (addr-range base k))))

(defthm addr-not-member-addr-range-greater
  (implies (and (< addr1 addr2)
                (integerp addr2))
           (not (bag::memberp addr1 (addr-range addr2 n)))))

;drop? see ADDR-NOT-MEMBER-ADDR-RANGE-GREATER
(defthm addr-range-monotonic
  (implies (and (bag::memberp addr (addr-range base k))
                (integerp base))
           (<= base addr))
  :rule-classes nil)


;; ;bzo. The enable proved it - consider a new rule that shows (subbagp
;; ;(cons a x) y) if a and x have no overlap and both are subbagps of y.
;;
;; (defthm SUBBAGP-of-2-addr-ranges
;;   (implies (and (integerp size1)
;;                 (integerp size2)
;;                 (integerp base2)
;;                 (integerp base1)
;;                 )
;;            (equal (BAG::SUBBAGP (ADDR-RANGE base1 size1)
;;                                 (ADDR-RANGE base2 size2))
;;                   (or (zp size1)
;;                       (and  (<= base2 base1)
;;                             (<= (+ base1 size1) (+ base2 size2))))))
;;   :hints (("Goal" :in-theory (enable BAG::SUBBAGP-OF-CONS))))

(defthm subbagp-of-2-addr-ranges-better
  (equal (bag::subbagp (addr-range base1 size1)
                       (addr-range base2 size2))
         (or (zp size1)
             (and (<= (ifix base2) (ifix base1))
                  (<= (+ (ifix base1) (ifix size1))
                      (+ (ifix base2) (ifix size2))))))
  :hints (("Goal" :cases ((and (integerp size2) (integerp size1))
                          (and (not (integerp size2)) (integerp size1))
                          (and (integerp size2) (not (integerp size1)))

                          )
           :in-theory (enable ifix zp bag::subbagp-of-cons addr-range))))

;special case of subbagp-of-2-addr-ranges in case we diable that one
(defthm subbagp-of-two-addr-ranges-with-same-base
 (implies (< (ifix size1) (ifix size2))
          (BAG::SUBBAGP (ADDR-RANGE base size1)
                        (ADDR-RANGE base size2))))

;maybe we want helper-1 and helper-2 (perhaps somewhat improved) to still be around?

;; (defthm helper-1
;;   (IMPLIES (AND (< (+ -1 BASE1 SIZE1) BASE2)
;;                 (integerp base1)
;;                 (integerp base2)
;;                 (NOT (ZP SIZE1))
;;                 (NOT (ZP SIZE2))
;;                 )
;;            (BAG::DISJOINT (ADDR-RANGE BASE1 SIZE1)
;;                           (ADDR-RANGE BASE2 SIZE2)))
;;   :hints (("Goal" :in-theory (enable addr-range BAG::DISJOINT-OF-CONS-ONE))))

;; (defthm helper-2
;;   (IMPLIES (AND (NOT (ZP SIZE1))
;;                 (NOT (ZP SIZE2))
;;                 (integerp base1)
;;                 (integerp base2)
;;                 (<= BASE2 (+ -1 BASE1 SIZE1))
;;                 (< (+ -1 BASE2 SIZE2) BASE1)
;;                 )
;;            (BAG::DISJOINT (ADDR-RANGE BASE1 SIZE1)
;;                           (ADDR-RANGE BASE2 SIZE2)))
;;   :hints (("Goal" :in-theory (enable addr-range BAG::DISJOINT-OF-CONS-ONE))))

;; ;drop?
;; (defthm helper-3
;;   (IMPLIES (AND (NOT (ZP SIZE1))
;;                 (NOT (ZP SIZE2))
;;                 (integerp base1)
;;                 (integerp base2)
;;                 (<= BASE2 (+ -1 BASE1 SIZE1))
;;                 (NOT (BAG::DISJOINT (ADDR-RANGE BASE1 SIZE1)
;;                                     (ADDR-RANGE BASE2 SIZE2))))
;;            (<= BASE1 (+ -1 BASE2 SIZE2)))
;;   :hints (("Goal" :in-theory (enable addr-range BAG::DISJOINT-OF-CONS-ONE))))

;; (defthm helper-4
;;   (IMPLIES (AND (NOT (ZP SIZE1))
;;                 (NOT (ZP SIZE2))
;;                 (INTEGERP BASE1)
;;                 (INTEGERP BASE2)
;;                 (<= BASE2 (+ -1 BASE1 SIZE1))
;;                 (BAG::DISJOINT (ADDR-RANGE BASE1 SIZE1)
;;                                (ADDR-RANGE BASE2 SIZE2)))
;;            (< (+ -1 BASE2 SIZE2) BASE1))
;;   :hints (("Goal" :in-theory (enable addr-range BAG::DISJOINT-OF-CONS-ONE))))

(defthm unique-of-addr-range
  (bag::unique (addr-range base size))
  :hints (("Goal" :in-theory (enable addr-range bag::unique-of-cons))))

(defthm not-memberp-of-addr-range-when-not-integerp
  (implies (not (integerp k))
           (not (bag::memberp k (addr-range i j))))
  :hints (("Goal" :in-theory (enable addr-range))))

;I doubt I want this enabled very often...
(defthmd addr-range-expand-when-k-is-a-constant
  (implies (syntaxp (quotep k))
           (equal (addr-range base k)
                  (if (zp k)
                      nil
                      (cons (ifix base)
                            (addr-range (+ 1 (ifix base)) (1- k))))))
  :hints (("Goal" :in-theory (enable addr-range))))

;addr-range when zp?

(defthm addr-ranges-equal-same-base
  (equal (EQUAL (ADDR-RANGE base size1)
                (ADDR-RANGE base size2))
         (equal (nfix size1)
                (nfix size2)))
  :hints (("Goal" :in-theory (enable addr-range))))

;(in-theory (disable ACL2::LOGHEAD*-BETTER))

;Attempt to include in this book redundant copies of just those events from
;super-ihs that we need for gacc (because having all the events can slow
;proofs down).  Alternatively, we could include everything and disable the
;rules we don't want to fire.  Or leave stuff enabled and see if we can make
;things fast enough.  It worries me a bit to deliberately exclude most
;super-ih rules from most of our books, since I'd like changes to super-ihs to
;be tested by the regression suite...

;; (DEFUN ACL2::IMOD (ACL2::I ACL2::J)
;;   (DECLARE (XARGS :GUARD (AND (INTEGERP ACL2::I)
;;                               (INTEGERP ACL2::J)
;;                               (NOT (= 0 ACL2::J)))))
;;   (MOD (IFIX ACL2::I) (IFIX ACL2::J)))

;; (DEFUN ACL2::EXPT2 (ACL2::N)
;;   (DECLARE (XARGS :GUARD (AND (INTEGERP ACL2::N)
;;                               (<= 0 ACL2::N))))
;;   (EXPT 2 (NFIX ACL2::N)))

;; (DEFUN ACL2::LOGHEAD (ACL2::SIZE ACL2::I)
;;   (DECLARE (XARGS :GUARD (AND (INTEGERP ACL2::SIZE)
;;                               (>= ACL2::SIZE 0)
;;                               (INTEGERP ACL2::I))))
;;   (ACL2::IMOD ACL2::I (ACL2::EXPT2 ACL2::SIZE)))

;; (DEFUN ACL2::LOGAPP (ACL2::SIZE ACL2::I ACL2::J)
;;   (DECLARE (XARGS :GUARD (AND (INTEGERP ACL2::SIZE)
;;                               (>= ACL2::SIZE 0)
;;                               (INTEGERP ACL2::I)
;;                               (INTEGERP ACL2::J))))
;;   (LET ((ACL2::J (IFIX ACL2::J)))
;;        (+ (ACL2::LOGHEAD ACL2::SIZE ACL2::I)
;;           (* ACL2::J (ACL2::EXPT2 ACL2::SIZE)))))

;; (in-theory (disable ACL2::UNSIGNED-BYTE-P))

;; (in-theory (disable ACL2::LOGHEAD))

;; ;; ;;
;; ;; ;; WCONS
;; ;; ;;

;; ;append Y onto the low B bits of X
;; ;trying enabled..
;; ;would like to remove this function in favor of logapp
;; (defun wcons (b x y)
;;   (declare (xargs :guard t))
;;   (acl2::logapp (nfix b) (ifix x) (ifix y)))

;; (defthm wcons-non-negative
;;   (implies (<= 0 (ifix z))
;;            (<= 0 (wcons b y z)))
;;   :hints (("goal" :in-theory (enable wcons))))

;; (defthm integerp-of-wcons
;;   (integerp (wcons b x y))
;;   :rule-classes (:rewrite :type-prescription))

;; (defthm wcons-unsigned-byte-p
;;   (implies (and (acl2::unsigned-byte-p n x)
;;                 (acl2::unsigned-byte-p b y)
;;                 (integerp b)
;;                 (< 0 b)
;;                 (integerp n)
;;                 (< 0 n)
;;                 )
;;            (acl2::unsigned-byte-p (+ n b) (wcons n x y)))
;;   :hints (("Goal" :in-theory (enable wcons))))

;; ;;
;; ;; WCAR
;; ;;

;; ;return the low B bits of X
;; ;trying enabled..
;; ;would like to remove this function in favor of loghead
;; (defun wcar (b x)
;;   (declare (xargs :guard t))
;;   (acl2::loghead (nfix b) (ifix x)))

;; (defthm integerp-of-wcar
;;   (integerp (wcar b x))
;;   :rule-classes (:rewrite :type-prescription))

;; (defthm wcar-unsigned-byte-p
;;   (implies (and (integerp b)
;;                 (< 0 b))
;;            (acl2::unsigned-byte-p b (wcar b v)))
;;   :hints (("Goal" :in-theory (enable wcar))))

;; (defthm wcar-with-non-integerp-b
;;   (implies (not (integerp b))
;;            (equal (wcar b x)
;;                   0))
;;   :hints (("Goal" :in-theory (enable wcar))))

;; (defthm wcar-with-non-positive-b
;;   (implies (<= b 0)
;;            (equal (wcar b x)
;;                   0))
;;   :hints (("Goal" :in-theory (enable wcar))))

;; (defthm wcar-with-non-integerp-x
;;   (implies (not (integerp x))
;;            (equal (wcar b x)
;;                   0))
;;   :hints (("Goal" :in-theory (enable wcar))))

;; (defthm wcar-when-x-is-0
;;   (equal (wcar b 0)
;;          0)
;;   :hints (("Goal" :in-theory (enable wcar))))

;; (defthm wcar-of-wcar
;;   (equal (wcar b (wcar b x))
;;          (wcar b x))
;;   :hints (("Goal" :in-theory (enable wcar))))

;; (defthm wcar-does-nothing
;;   (implies (acl2::unsigned-byte-p b x)
;;            (equal (wcar b x)
;;                   x))
;;   :hints (("Goal" :in-theory (enable wcar))))

;; ;;
;; ;; WCDR
;; ;;

;; ;return everything except the low B bits of X.
;; ;That is, shift X to the right B places and truncate to an integer.
;; ;trying enabled..
;; ;would like to remove this function in favor of logtail
;; (defun wcdr (b x)
;;   (declare (xargs :guard t))
;;   (acl2::logtail (nfix b) (ifix x)))

;; (defthm integerp-of-wcdr
;;   (integerp (wcdr b x))
;;   :rule-classes (:rewrite :type-prescription))

;; (defthm wcdr-wcar-reduction
;;   (implies (equal (wcdr b x) 0)
;;            (equal (wcar b x)
;;                   (ifix x)))
;;   :hints (("Goal" :in-theory (enable wcar wcdr))))

;; (defthm wcdr-when-x-is-0
;;   (equal (wcdr b 0)
;;          0)
;;   :hints (("Goal" :in-theory (enable wcdr))))

;; (defthm wcdr-when-x-is-not-an-integerp
;;    (implies (not (integerp x))
;;             (equal (wcdr b x)
;;                    0))
;;    :hints (("Goal" :in-theory (enable wcdr))))

;; ;;
;; ;; Rules about (at least two of) WCONS, WCAR, and WCDR
;; ;;

;; (defthm wcons-when-y-is-0
;;   (equal (wcons b x 0)
;;          (wcar b x))
;;   :hints (("Goal" :in-theory (enable wcons wcar))))

;; (defthm wcons-when-y-is-not-an-integerp
;;   (implies (not (integerp y))
;;            (equal (wcons b x y)
;;                   (wcar b x)))
;;   :hints (("Goal" :in-theory (enable wcons wcar))))

;; (defthm wcons-when-x-is-not-an-integerp
;;   (implies (not (integerp x))
;;            (equal (wcons b x y)
;;                   (wcons b 0 y)))
;;   :hints (("Goal" :in-theory (enable wcons wcar))))

;; (defthm wcar-of-wcons
;;   (equal (wcar b (wcons b x y))
;;          (wcar b x))
;;   :hints (("Goal" :in-theory (enable wcar wcons))))

;; (defthm wcdr-of-wcons
;;   (equal (wcdr b (wcons b x y))
;;          (ifix y))
;;   :hints (("Goal" :in-theory (enable wcdr wcons))))

;; (defthm wcons-equal-0-rewrite
;;   (equal (equal 0 (wcons b x y))
;;          (and (equal (wcar b x) 0)
;;               (equal (ifix y) 0)))
;;   :hints (("Goal" :in-theory (enable wcar wcons))))

;; (defthm equal-of-wcons-and-wcons-rewrite
;;   (equal (equal (wcons b v1 v2)
;;                 (wcons b v3 v4))
;;          (and (equal (wcar b v1) (wcar b v3))
;;               (equal (ifix v2) (ifix v4))))
;;   :hints (("Goal" :in-theory (enable wcar wcons))))

;; (defthm wcons-of-wcar
;;   (equal (wcons b (wcar b x) y)
;;          (wcons b x y))
;;   :hints (("Goal" :in-theory (enable wcar wcons))))

;; (defthm wcdr-of-wcar
;;   (equal (wcdr b (wcar b x))
;;          0)
;;   :hints (("Goal" :in-theory (enable wcar wcdr))))

;; ;;
;; ;; WFIXW
;; ;;

;; ;Chop V down to fit in N B-bit chunks.
;; (defund wfixw (b n v)
;;   (declare (type (integer 0 *) n))
;;   (if (zp n) 0
;;     (acl2::logapp (nfix b) (acl2::loghead (nfix b) (ifix v)) (wfixw b (1- n) (acl2::logtail (nfix b) (ifix v))))))

;; ;; ;old
;; ;; (defund wfixw (b n v)
;; ;;   (declare (type (integer 0 *) n))
;; ;;   (if (zp n) 0
;; ;;     (wcons b (wcar b v) (wfixw b (1- n) (wcdr b v)))))

;; ;linear? ;-tp?
;; (defthm wfixw+
;;   (<= 0 (wfixw b s v))
;;   :hints (("goal" :in-theory (enable wfixw))))

;; (defthm wfixw-0
;;   (equal (wfixw b n 0)
;;          0)
;;   :hints (("Goal" :in-theory (enable wfixw))))

;; (defthm wfixw-with-n-0
;;   (equal (wfixw b 0 v)
;;          0)
;;   :hints (("Goal" :in-theory (enable wfixw))))

;; (defthm integerp-wfixw
;;   (integerp (wfixw b n value)))

;; (defthm wfixw-with-zp-n
;;   (implies (zp n)
;;            (equal (wfixw b n v)
;;                   0))
;;   :hints (("Goal" :in-theory (enable wfixw))))

;; (defthm wfixw-with-b-not-an-integerp
;;   (implies (not (integerp b))
;;            (equal (wfixw b n v)
;;                   0))
;;   :hints (("Goal" :in-theory (enable wfixw))))

;; (defthm wfixw-with-b-not-positive
;;   (implies (<= b 0)
;;            (equal (wfixw b n v)
;;                   0))
;;   :hints (("Goal" :in-theory (enable wfixw))))

;; (defthm wfixw-when-v-is-not-an-integerp
;;   (implies (not (integerp v))
;;            (equal (wfixw b n v)
;;                   (wfixw b n 0)))
;;   :hints (("Goal" :expand ((wfixw b n v)))))

;; (defthmd wfixw-reduction
;;   (equal (wfixw b n v)
;;          (acl2::loghead (* (nfix b) (nfix n)) v))
;;   :hints (("goal" :induct (wfixw b n v)
;;            :in-theory (enable wfixw zp ;wcons wcar wcdr
;;                               ))))


;; (defthmd open-wfixw
;;   (implies (not (zp n))
;;            (equal (wfixw b n v)
;;                   (acl2::logapp (nfix b) (acl2::loghead (nfix b) (ifix v)) (wfixw b (1- n) (acl2::logtail (nfix b) (ifix v))))))
;;   :hints (("Goal" :in-theory (enable wfixw))))

;; ;; (defthmd open-wfixw
;; ;;   (implies (not (zp n))
;; ;;            (equal (wfixw b n v)
;; ;;                   (wcons b (wcar b v) (wfixw b (1- n) (wcdr b v)))))
;; ;;   :hints (("Goal" :in-theory (enable wfixw))))

;; (defthm wfixw-wfixw
;;   (equal (wfixw b n (wfixw b m v))
;;          (wfixw b (min (nfix n) (nfix m)) v))
;;   :hints (("Goal" :in-theory (enable wfixw-reduction))))

;; ;rename
;; (defthm wcar-wcdr-wfixw
;;   (and (equal (acl2::loghead ;wcar
;;                b (wfixw b n value))
;;               (if (zp n)
;;                   0
;;                 (acl2::loghead ;wcar
;;                  b value)))
;;        (equal (acl2::logtail ;wcdr
;;                b (wfixw b n value))
;;               (if (zp n)
;;                   0
;;                 (wfixw b (1- n) (acl2::logtail ;wcdr
;;                                  b value)))))
;;   :hints (("Goal" :in-theory (enable open-wfixw))))

;;
;; WINTW
;;

;; ;test whether V is an integer which fits in N B-bit chunks.
;; ;could reduce to wint?
;; ;Eric would like to get rid of this function...
;; (defund wintw (b n v)
;;   (declare (type (integer 0 *) n))
;;   (and ;(integerp v) ;removed by Eric
;;        (equal (wfixw b n v) v)))

;; (defthmd wintw-unsigned-byte-p ;trying disabled...
;;   (implies (and (wintw b n v)
;;                 (equal (* b n) size)
;;                 (integerp b)
;;                 (integerp n)
;;                 (< 0 b)
;;                 (< 0 n)
;;                 )
;;            (acl2::unsigned-byte-p size v))
;;   :hints (("goal" :in-theory (enable wintw))))

;; (defthm wintw-rewrite-to-unsigned-byte-p
;;   (implies (and (integerp b)
;;                 (integerp n)
;;                 (<= 0 b)
;;                 (<= 0 n)
;;                 )
;;            (equal (wintw b n v)
;;                   (acl2::unsigned-byte-p (* b n) v)))
;;   :hints (("goal" :in-theory (enable wintw wfixw ;wcdr wcons
;;                                      ))))

;; (defthm wintw-when-n-is-zp
;;   (implies (and (zp n))
;;            (equal (wintw s n x)
;;                   (equal 0 x)))
;;   :hints (("Goal" :in-theory (enable wintw))))

;; ;;
;; ;; misc. word function properties
;; ;;

;; (defthm wintw-wfixw
;;   (implies (wintw s n x)
;;            (equal (wfixw s n x)
;;                   x))
;;   :hints (("Goal" :in-theory (enable wfixw wintw))))


(in-theory (disable acl2::append-true-listp-type-prescription)) ;we have a better rule

;;
;; BLK-REC
;;

;returns a list of the integers from base+off to base+max-1
;Eric thinks the "max" parameter should be called "size".
;why does this take 3 parameters?
(defund blk-rec (base off max)
  (declare (type t base off max)
           (xargs :measure (nfix (- (ifix max) (ifix off)))))
  (if (not (< (ifix off) (ifix max)))
      nil
    (cons (+ (ifix off) (ifix base))
          (blk-rec base (1+ (ifix off)) (ifix max)))))

(defthm true-listp-blk-rec
  (true-listp (blk-rec base off size))
  :rule-classes (:rewrite :TYPE-PRESCRIPTION))

(defthm blk-rec-non-integer-ptr
  (implies (not (integerp x))
           (equal (blk-rec x y z)
                  (blk-rec 0 y z)))
  :hints (("goal" :in-theory (enable blk-rec))))

(defthm blk-rec-non-integer-off
  (implies (not (integerp off))
           (equal (blk-rec ptr off max)
                  (blk-rec ptr 0 max)))
  :hints (("goal" :in-theory (enable blk-rec))))

(defthm blk-rec-non-integer-size
  (implies (not (integerp size))
           (equal (blk-rec base off size)
                  (blk-rec base off 0)))
  :hints (("Goal" :in-theory (enable blk-rec))))

(defthm unfixed-base-blk-rec
  (equal (blk-rec (ifix base) off max)
         (blk-rec base off max))
  :hints (("goal" :in-theory (enable blk-rec))))

(defthm len-blk-rec
  (equal (len (blk-rec base off max))
         (nfix (- (ifix max) (ifix off))))
  :hints (("goal" :in-theory (enable ifix blk-rec))))

(defthm integer-listp-blk-rec
  (integer-listp (blk-rec ptr off max))
  :hints (("goal" :in-theory (enable blk-rec))))

(defthm consp-blk-rec
  (equal (consp (blk-rec base off max))
         (< (ifix off) (ifix max)))
  :hints (("goal" :in-theory (enable blk-rec))))

(defthm blk-rec-consp-type
  (implies (and (< off max)
                (integerp off)
                (integerp max)
                )
           (consp (blk-rec base off max)))
  :rule-classes (:type-prescription))

(defthmd open-blk-rec
  (implies (< (ifix off) (ifix size))
           (equal (blk-rec ptr off size)
                  (cons (+ (ifix off) (ifix ptr))
                        (blk-rec ptr (1+ (ifix off)) (ifix size)))))
  :hints (("Goal" :in-theory '(blk-rec))))


(defthm subbagp-blk-rec-memberp
  (implies (and (subbagp (blk-rec ptr off size) y)
                (integerp off)
                (integerp size)
                (< off size)
                (integerp ptr)
                )
           (memberp (+ off ptr) y))
  :hints (("Goal" :in-theory (enable blk-rec))))

;added by eric (make blk analogues of these?)
(defthm car-of-blk-rec
  (equal (car (blk-rec base off max))
         (if (< (ifix off) (ifix max))
             (+ (ifix off) (ifix base))
           nil))
  :hints (("Goal" :in-theory (enable blk-rec))))

;Treat as zeros non-integers in the comparison
(defthm disjoint-blk-rec-subbagp
  (implies (and (disjoint list (blk-rec ptr off size1))
                (<= (ifix size0) (ifix size1)))
           (disjoint list (blk-rec ptr off size0)))
  :hints (("Goal" :in-theory (enable blk-rec)
           :do-not '(generalize eliminate-destructors))))

(defthm disjoint-blk-rec-subbagp-right
  (implies (and (not (disjoint list (blk-rec ptr off size0)))
                (<= (ifix size0) (ifix size1)))
           (equal (disjoint list (blk-rec ptr off size1))
                  nil)))

(defthm disjoint-blk-rec-subbagp-left
  (implies (and (not (disjoint (blk-rec ptr off size0) list))
                (<= (ifix size0) (ifix size1)))
           (equal (disjoint (blk-rec ptr off size1) list)
                  nil)))

;make a blk analogue of this?
(defthm blk-rec-non-membership-less
  (implies (< n (+ (ifix ptr) (ifix off)))
           (equal (memberp n (blk-rec ptr off m))
                  nil))
  :hints (("Goal" :in-theory (enable blk-rec))))

(defthm blk-rec-non-membership-more
  (implies (<= (+ (ifix ptr) (ifix m)) n)
           (equal (memberp n (blk-rec ptr off m)) nil))
  :hints (("Goal" :in-theory (enable blk-rec))))

(defthm blk-rec-membership-subbagp
  (implies (and (not (memberp addr (blk-rec ptr off size2)))
                (<= (ifix size1) (ifix size2))
                )
           (equal (memberp addr (blk-rec ptr off size1))
                  nil))
  :hints (("Goal" :in-theory (enable blk-rec))))

(defthm blk-rec-membership
  (implies (and (integerp ptr)
                (< (ifix off) (ifix size))
                (<= (+ (ifix base) (ifix off)) (ifix ptr))
                (< (ifix ptr) (+ (ifix base) (ifix size))))
           (memberp ptr (blk-rec base off size)))
  :hints (("Goal" :in-theory (e/d (blk-rec)
                                  ( BLK-REC-NON-INTEGER-PTR ;why??
                                    blk-rec-non-integer-size
                                    )))))

(defthm null-blk-rec
  (implies (<= (ifix max) (ifix off))
           (equal (blk-rec ptr off max)
                  nil))
  :hints (("Goal" :in-theory (enable blk-rec))))


;In order to keep usable need the integer hyps
;The problem taking them out comes cause x and rptr could be rationals
;For example, if x=5/2 and rptr=3/2, lhs of equal starts at 4+(ifix off)
; and rhs starts at 0+(ifix off).
(defthm blk-rec-normalization
  (implies (and (integerp rptr)
                (integerp x)
                (<= 0 x))
           (equal (blk-rec (+ x rptr) roff rmax)
                  (blk-rec rptr
                           (+ x (ifix roff))
                           (+ x (ifix rmax)))))
  :hints (("goal" :in-theory (enable blk-rec)
           :induct (blk-rec (+ x rptr) roff rmax))))

(defthm blk-rec-lower-subbagp
  (implies (and (<= (ifix m) (ifix n))
                (<= (ifix max1) (ifix max2))
                )
           (subbagp (blk-rec ptr n max1)
                    (blk-rec ptr m max2)))
  :hints (("Goal" :in-theory (enable blk-rec)
           :induct (blk-rec ptr m max2))))

(defthm disjoint-of-blk-recs-1
   (implies (and (<= (+ (ifix rptr) (ifix rsize)) (ifix wptr))
                 (<= 0 (ifix roff))
                 (<= 0 (ifix woff))
                 )
            (disjoint (blk-rec rptr roff rsize)
                      (blk-rec wptr woff wsize)))
   :hints (("Goal" :in-theory (e/d ( LIST::memberp-of-cons
                                     blk-rec
                                     bag::disjoint-of-cons-one)
                                   ( bag::disjoint-commutative ;why??
                                     ))
            :induct (blk-rec rptr roff rsize)
            )))

(defthm disjoint-of-blk-recs-2
  (implies (and (<= (+ (ifix wptr) (ifix wsize)) (ifix rptr))
                (<= 0 (ifix roff))
                (<= 0 (ifix woff))
                )
           (disjoint (blk-rec rptr roff rsize)
                     (blk-rec wptr woff wsize)))
  :hints (("Goal" :in-theory (disable blk-rec
;DISJOINT-BLK-REC-SUBBAGP-LEFT
                                      disjoint-of-blk-recs-1)
           :use (:instance disjoint-of-blk-recs-1
                           (rptr wptr)
                           (wptr rptr)
                           (roff woff)
                           (woff roff)
                           (wsize rsize)
                           (rsize wsize)
                           ))))

(defthm memberp-of-blk-rec-when-not-integerp
  (implies (not (integerp x))
           (not (bag::memberp x (gacc::blk-rec base offset max))))
  :hints (("Goal" :in-theory (enable gacc::blk-rec))))

(defthm unique-blk-rec
  (unique (blk-rec base off size))
  :hints (("goal" :in-theory (enable unique blk-rec))))




;;
;; BLK
;;


;return a list of the addresses from base to base+size-1
(defund blk (base size)
  (declare (type t base size))
  (blk-rec base 0 size))

;We disable the executable-counterpart of blk, so that ACL2 doesn't actually compute big lists of addresses
;For instance, (blk 5 10) does not get expanded to (5 6 7 8 9 10 11 12 13 14) if the executablec-counterpart is disabled.
(in-theory (disable (:executable-counterpart blk)))

(defthm true-listp-blk
  (true-listp (blk base size)))

(defthm true-listp-blk-type-prescription
  (true-listp (blk base size))
  :rule-classes :TYPE-PRESCRIPTION)

(in-theory (disable (:TYPE-PRESCRIPTION BLK))) ;we'll use true-listp-blk-type-prescription instead

(defthm unique-blk
  (unique (blk base size))
  :hints (("goal" :in-theory (enable unique blk))))

(defthm integer-listp-blk
  (integer-listp (blk base size))
  :hints (("Goal" :in-theory (enable blk))))

(defthm null-blk
  (implies (zp max)
           (equal (blk ptr max) nil))
  :hints (("goal" :in-theory (enable blk))))

(defthm consp-blk
  (equal (consp (blk base size))
         (< 0 (ifix size)))
  :hints (("Goal" :in-theory (enable blk))))

(defthm blk-consp-type
  (implies (and (integerp size)
                (< 0 size))
            (consp (blk base size)))
  :rule-classes (:type-prescription))

;make this an equal rule?
(defthm blk-upper-subbagp
  (implies (<= (ifix max1) (ifix max2))
           (subbagp (blk ptr max1)
                    (blk ptr max2)))
  :hints (("Goal" :in-theory (enable blk))))

 ;; These should be among the last rules attempted ..

(defthm blk-disjoint-from-blk-1
  (implies (and (<= (+ (ifix rptr) (ifix rsize)) (ifix wptr))
                (<= 0 (ifix rsize))
                (<= 0 (ifix wsize))
                )
           (disjoint (blk rptr rsize)
                     (blk wptr wsize)))
  :hints (("Goal" :in-theory (enable blk))))

(defthm blk-disjoint-from-blk-2
  (implies (and (<= (+ (ifix wptr) (ifix wsize)) (ifix rptr))
                (<= 0 (ifix rsize))
                (<= 0 (ifix wsize))
                )
           (disjoint (blk rptr rsize)
                     (blk wptr wsize)))
  :hints (("Goal" :in-theory (enable blk))))

(defthm blk-membership-subbagp
  (implies (and (not (memberp addr (blk ptr size2))) ;size2 is a free variable
                (<= (ifix size1) (ifix size2))
                )
           (equal (memberp addr (blk ptr size1))
                  nil))
  :hints (("Goal" :in-theory (enable blk))))

(defthm blk-non-membership-less
  (implies (< n (ifix ptr))
           (equal (memberp n (blk ptr size))
                  nil))
  :hints (("Goal" :in-theory (enable blk))))

(defthm blk-non-membership-more
  (implies (< (+ (ifix ptr) (ifix size)) n)
           (equal (memberp n (blk ptr size))
                  nil))
  :hints (("Goal" :in-theory (enable blk))))

;we need the integerp for the same reason as in blk-rec-membership
(defthm blk-membership
  (implies (and (integerp ptr)
                (<= (ifix base) ptr)
                (< ptr (+ (ifix base) (ifix size))))
           (memberp ptr (blk base size)))
  :hints (("Goal" :in-theory (enable blk))))

(defthm disjoint-blk-subbagp-right
  (implies (and (not (disjoint list (blk ptr size0))) ;size0 is a free variable
                (<= (ifix size0) (ifix size1)))
           (equal (disjoint list (blk ptr size1))
                  nil))
  :hints (("Goal" :in-theory (enable blk))))

(defthm disjoint-blk-subbagp-left
  (implies (and (not (disjoint (blk ptr size0) list)) ;size0 is a free variable
                (<= (ifix size0) (ifix size1)))
           (equal (disjoint (blk ptr size1) list)
                  nil))
  :hints (("Goal" :in-theory (enable blk))))

;;
;; XBLOCK
;;

;; ;bzo do we ever use xblock?

;; (defun xblock (base size)
;;   (declare (type integer size base))
;;   (if (zerop base)
;;       nil
;;     (blk base size)))

;; (defthm zp-xblock
;;   (implies (zerop base)
;;            (equal (xblock base size)
;;                   nil)))


;;
;; relocate-blk
;;

(defun relocate-blk (off list)
  (declare (type (satisfies integer-listp) list))
  (if (consp list)
      (cons (+ (ifix off) (car list)) (relocate-blk off (cdr list)))
    nil))

(defthm len-of-relocate-blk
  (equal (len (gacc::relocate-blk off list))
         (len list)))

;really do need to know that x and the list are integer based,
; but no longer need y to be an integer
; for these the problem is that +/- treats non-numbers as 0, so
; if x is a non-number, or anything in the list isn't, doesn't hold
(defthm memberp-relocate-blk
  (implies
   (and
    (integer-listp list)
    (integerp x)
    )
   (equal (memberp x (relocate-blk y list))
          (memberp (- x (ifix y)) list)))
  :hints (("Goal" :in-theory (enable LIST::memberp-of-cons))))

;can remove hyp that x is integerp, but still need nice lists
; see comments above for memberp-relocate-blk
(defthm disjoint-relocation
  (implies
   (and
    (integer-listp list1)
    (integer-listp list2)
    )
   (equal (disjoint (relocate-blk x list1)
                    (relocate-blk x list2))
          (disjoint list1 list2)))
  :hints (("Goal" :in-theory (enable LIST::memberp-of-cons
                                     BAG::DISJOINT-OF-CONS-TWO))))

;need the integerp or its just not true always
; see comment for blk-rec-normalization and memberp-relocate-blk
(defthm relocate-blk-rec-offset
  (implies
   (and
    (integerp ptr)
    (integerp x))
   (equal (blk-rec (+ ptr x) off max)
          (relocate-blk x (blk-rec ptr off max))))
  :hints (("Goal" :in-theory (enable blk-rec))))


(defthmd relocate-blk-offset
  (implies
   (and
    (integerp ptr)
    (integerp x))
   (equal (blk (+ x ptr) size)
          (relocate-blk x (blk ptr size))))
  :hints (("goal" :in-theory (enable blk))))

;Checks whether LIST is a true-listp of consecutive integers.
;despite the name of this, we define sblkp well before we define sblk.
;perhaps the name should be blkp?
(defund sblkp (list)
  (declare (type t list))
  (if (consp list)
      (let ((x (car list)))
        (and (integerp x)
             (implies* (consp (cdr list))
                       (equal (1+ x) (cadr list)))
             (sblkp (cdr list))))
    (null list)))

(defthm sblkp-blk-rec
  (sblkp (blk-rec base off max))
  :hints (("goal" :in-theory (enable blk-rec sblkp))))

(defun equal-x-blk-rec-induction (x base off max)
  (if (and (consp x)
           (< (ifix off) (ifix max)))
      (equal-x-blk-rec-induction (cdr x) base (1+ (ifix off)) (ifix max))
    (list x base off max)))

(defthm equal-blk-rec-extensionality
  (implies (and (integerp base)
                (integerp max)
                (integerp off)
                (< off max))
           (equal (equal x (blk-rec base off max))
                  (and (sblkp x)
                       (equal (car x) (+ base off))
                       (equal (len x) (- max off)))))
  :hints (("goal" :induct (equal-x-blk-rec-induction x base off max)
           :in-theory (enable sblkp len blk-rec open-blk-rec ;fix-size
                              ))))



;add to gacc, or is something like this already there?
(defthm sblkp-of-relocate-blk
  (implies (gacc::sblkp list)
           (gacc::sblkp (gacc::relocate-blk off list)))
  :hints (("Goal" :in-theory (enable  gacc::relocate-blk gacc::sblkp))))


;add to gacc, or is something like this already there?
(defthm car-of-relocate-blk
  (equal (car (gacc::relocate-blk off list))
         (if (consp list)
             (+ (ifix off) (car list))
           nil))
  :hints (("Goal" :in-theory (enable  gacc::relocate-blk gacc::sblkp))))

(defthmd blk-rec-normalize
  (IMPLIES (AND (case-split (INTEGERP SIZE))
;                (case-split (< 0 SIZE))
                (case-split (integerp base))
                (case-split (integerp e))
                (case-split (integerp off))
                )
           (EQUAL (GACC::BLK-REC base (+ e off) (+ e SIZE))
                  (GACC::BLK-REC (+ e base) off SIZE)))
  :hints (("Goal" ;:induct (ADDR-RANGE BASE SIZE)
           :in-theory (enable gacc::blk-rec))))

;looped
(defthmd blk-rec-normalize-to-0-offset
  (IMPLIES (AND (syntaxp (not (and (quotep off) (equal off ''0)))) ;prevents loops
                (case-split (INTEGERP SIZE))
;                (case-split (< 0 SIZE))
                (case-split (integerp base))
                (case-split (integerp off))
                )
           (EQUAL (GACC::BLK-REC base off size)
                  (GACC::BLK-REC (+ base off) 0 (- SIZE off))))
  :hints (("Goal" :use (:instance blk-rec-normalize (base base) (off 0) (size (- SIZE off)) (e off)))))


;bzo make nicer?
(defthm cdr-of-blk-rec
  (equal (cdr (gacc::blk-rec base off max))
         (if (<= (ifix max) (ifix off))
             nil
           (gacc::blk-rec base (+ 1 (ifix off)) max)))
  :hints (("Goal" :expand ( (gacc::blk-rec base off max)
                            (gacc::blk-rec (+ 1 base) off max))
           :in-theory (enable ;acl2::cons-equal-rewrite ;bzo
                              ifix
                              gacc::blk-rec))))

(defthm blk-when-size-is-1
  (equal (GACC::BLK PTR 1)
         (list (ifix ptr)))
  :hints (("Goal" :in-theory (enable gacc::blk)))
  )

(in-theory (disable list::len-of-cdr)) ;might be nice to remove this eventually
(local (in-theory (disable ifix)))

(in-theory (disable (:executable-counterpart skel)))

;Added by Eric
(local (in-theory (disable memberp
;                           acl2::MEMBERP-Subbagp-NOT-CONSP-VERSION
                           REMOVE-BAG
                           REMOVE-1)))


(local (in-theory (disable fix-slot)))

;(skipper
; (encapsulate ()

(defthm slot-p-implies-skel-p-slot-skel
  (implies
   (slot-p slot)
   (skel-p (slot-skel slot)))
  :hints (("goal" :in-theory (enable slot-p))))

#|
(defthm mv-nth-cons
  (equal (mv-nth i (cons a b))
         (if (zp i) a (mv-nth (1- i) b)))
  :hints (("goal" :in-theory (enable mv-nth))))
|#

;move these?
(defthm non-integerp-ifix
  (implies (not (integerp x))
           (equal (ifix x)
                  0))
  :hints (("goal" :in-theory (enable ifix))))

(defthm integerp-ifix
  (implies (integerp x)
           (equal (ifix x)
                  x))
  :hints (("goal" :in-theory (enable ifix))))

(in-theory
 (enable
  slot-p
  slot-extensionality!!
  ))

;fix-size was defined here

(defun offset-size (n)
  (declare (type (integer 0 *) n))
  (if (zp n)
      (word-size)
    (+ (word-size) (offset-size (1- n)))))

(defthm fix-size-offset-size
  (equal (fix-size (offset-size n))
         (offset-size n))
  :hints (("goal" :in-theory (enable fix-size offset-size))))

(defthm offset-size-max-offset
  (equal (offset-size (max-offset size))
         (fix-size size))
  :hints (("Goal" :in-theory (enable max-offset fix-size))))

(defthm offset-size-max-offset-free
  (implies
   (equal len (1+ (max-offset size)))
   (equal (offset-size (+ -1 len))
          (fix-size size))))

(defthm offset-size-len-sblk
  (equal (offset-size (1- (len (sblk size ptr))))
         (fix-size size)))




(defthm unfixed-size-sblk
  (implies (syntaxp (syntax-unfixed-size size))
           (equal (sblk size ptr)
                  (sblk (fix-size size) ptr)))
  :hints (("goal" :in-theory (enable sblk))))

(defthm unfixed-size-max-offset
  (implies (syntaxp (syntax-unfixed-size size))
           (equal (max-offset size)
                  (max-offset (fix-size size)))))

(in-theory (disable max-offset-fix-size))

(defun sblk-parms (base sblk)
  (declare (type t base sblk))
  (let ((size (offset-size (nfix (1- (len sblk))))))
    (let ((ptr (if (consp sblk) (car sblk) base)))
      (mv size (- (ifix ptr) (ifix base))))))

(defthm non-integerp-sblk-base
  (implies
   (not (integerp base))
   (equal (sblk-parms base sblk)
          (sblk-parms (ifix base) sblk)))
  :hints (("goal" :in-theory (enable ifix))))

;added by Eric.
(defthm integerp-of-v1-of-sblk-parms
  (integerp (v1 (sblk-parms base sblk)))
  :hints (("Goal" :in-theory (enable sblk-parms))))

;added by Eric.
(defthm integerp-of-v0-of-sblk-parms
  (integerp (v0 (sblk-parms base sblk)))
  :hints (("Goal" :in-theory (enable sblk-parms))))


(defun appears (base term)
  (declare (type t base term))
  (or (equal base term)
      (memberp base term)))

#|
(defun appears-ignore-package (base term)
  (declare (type t base term))
  (or (equal (symbol-name base) (symbol-name term))
      (memberp base term)))
|#


(defun syntax-ptr (base ptr woff wbase)
  (declare (type t base ptr))
  (if (and (consp ptr)
           (equal (car ptr) 'binary-+)
           (consp (cdr ptr))
           (consp (cddr ptr)))
      (if (appears base (cadr ptr))
          `((,woff  . ,(caddr ptr))
            (,wbase . ,(cadr ptr)))
        (if (appears base (caddr ptr))
            `((,woff  . ,(cadr  ptr))
              (,wbase . ,(caddr ptr)))
          nil))
    (if (appears base ptr)
        `((,woff  . (quote 0))
          (,wbase . ,ptr))
      `((,woff  . ,ptr)
        (,wbase . (quote 0))))))



(defthm sblk-parms-sblk
  (implies
   (and
    (bind-free (syntax-ptr base ptr 'woff 'wbase) (woff wbase))
    (equal wbase (ifix base))
    (equal ptr (+ wbase woff))
    (integerp wbase)
    (integerp woff)
    )
   (equal (sblk-parms base (sblk size ptr))
          (mv (fix-size size) woff)))
  :hints (("Goal" :in-theory (disable MAX-OFFSET-WHEN-MULTIPLE-OF-8 ;bzo
                                      ))))

(defthm sblk-parms-sblk-free
  (implies
   (and
    (equal (sblk size ptr) sblk)
    (bind-free (syntax-ptr base ptr 'woff 'wbase) (woff wbase))
    (equal wbase (ifix base))
    (equal ptr (+ wbase woff))
    (integerp wbase)
    (integerp woff)
    )
   (equal (sblk-parms base sblk)
          (mv (fix-size size) woff))))

(in-theory (disable sblk-parms))

(local (in-theory (disable MAX-OFFSET-WHEN-MULTIPLE-OF-8))) ;bzo

;bzo
(defthm open-len
  (implies (and (syntaxp (syntax-consp-or-symbol list))
                (consp list))
           (equal (len list)
                  (1+ (len (cdr list)))))
  :hints (("goal" :in-theory (enable len))))

(defun rs (size off base spec)
  (declare (type t size off spec))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (and (slot-p slot)
                 (equal :ptr (slot-type slot))
                 (compare base size off (slot-size slot) (slot-off slot)))
            (slot-skel slot)
          (rs size off base (cdr spec))))
    (skel 0 nil)))


(defthm rs-when-base-is-not-an-integerp
  (implies (not (integerp base))
           (equal (RS SIZE OFF BASE SPEC)
                  (RS SIZE OFF 0 SPEC)))
  :hints (("Goal" :in-theory (disable ;ZS-INTRODUCTION-LEFT ;bzo looped
                                      ))))

(defun rv (size off base spec)
  (declare (type t size off spec))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (and (slot-p slot)
                 (compare base size off (slot-size slot) (slot-off slot)))
            (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                   (ifix (slot-val slot)))
          (rv size off base (cdr spec))))
    0))

;was called positive-rv
(defthm rv-non-negative
  (<= 0 (rv size off base spec)))

(defun ws (size off base skel spec)
  (declare (type t size off skel spec))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (and (slot-p slot)
                 (equal :ptr (slot-type slot))
                 (compare base size off (slot-size slot) (slot-off slot)))
            (cons (update-slot slot :skel (fix-skel skel))
                  (cdr spec))
          (cons slot
                (ws size off base skel (cdr spec)))))
    spec))

(defthm ws-when-base-is-not-an-integerp
  (implies (not (integerp gacc::base))
           (equal (ws size gacc::off gacc::base skel gacc::spec)
                  (ws size gacc::off 0 skel gacc::spec)))
  :hints (("Goal" :in-theory (enable ws))))


(defthm open-ws
  (and
   (implies
    (consp spec)
    (equal (ws size off base skel spec)
           (let ((slot (car spec)))
             (if (and (slot-p slot)
                      (equal :ptr (slot-type slot))
                      (compare base size off (slot-size slot) (slot-off slot)))
                 (cons (update-slot slot :skel (fix-skel skel))
                       (cdr spec))
               (cons slot
                     (ws size off base skel (cdr spec)))))))
   (implies
    (not (consp spec))
    (equal (ws size off base skel spec) spec))))

(in-theory
 (disable
  (:definition ws)
  ))

(defun wv (size off base val spec)
  (declare (type t size off val spec))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (and (slot-p slot)
                 (compare base size off (slot-size slot) (slot-off slot)))
            (cons (update-slot slot :val (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                (ifix val)))
                  (cdr spec))
          (cons slot
                (wv size off base val (cdr spec)))))
    spec))

(defthm open-wv
  (and
   (implies
    (consp spec)
    (equal (wv size off base val spec)
           (let ((slot (car spec)))
             (if (and (slot-p slot)
                      (compare base size off (slot-size slot) (slot-off slot)))
                 (cons (update-slot slot :val (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                     val))
                       (cdr spec))
               (cons slot
                     (wv size off base val (cdr spec)))))))
   (implies
    (not (consp spec))
    (equal (wv size off base skel spec) spec))))

(in-theory (disable (:definition wv)))

(defthm rs-over-wv
  (equal (rs rsize roff base (wv wsize woff base value spec))
         (rs rsize roff base spec)))

(defthm rv-over-ws
  (equal (rv rsize roff base (ws wsize woff base value spec))
         (rv rsize roff base spec)))

(defthm rs-over-ws
  (implies
   (not (compare base rsize roff wsize woff))
   (equal (rs rsize roff base (ws wsize woff base value spec))
          (rs rsize roff base spec))))

(defthm rv-over-wv
  (implies
   (not (compare base rsize roff wsize woff))
   (equal (rv rsize roff base (wv wsize woff base value spec))
          (rv rsize roff base spec))))

(defthm rs-of-ws
  (implies
   (memberp (sblk size (+<> off base)) (keys-spec :ptr base spec))
   (equal (rs size off base (ws size off base value spec))
          (fix-skel value))))

(defthm rv-of-wv
  (implies
   (memberp (sblk size (+<> off base)) (keys-spec w base spec))
   (equal (rv size off base (wv size off base value spec))
          (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                 value))))

(defthm vanishing-ws
  (implies
   (not (memberp (sblk size (+<> off base)) (keys-spec :ptr base spec)))
   (equal (ws size off base value spec)
          spec))
  :hints (("goal" :induct (ws size off base value spec))))

(defthm vanishing-wv
  (implies
   (not (memberp (sblk size (+<> off base)) (keys-spec :all base spec)))
   (equal (wv size off base value spec)
          spec))
  :hints (("goal" :in-theory (enable fix-slot)
           :induct (wv size off base value spec))))

(defthm default-rs
  (implies
   (not (memberp (sblk size (+<> off base)) (keys-spec :ptr base spec)))
   (equal (rs size off base spec)
          (skel 0 nil))))

(defthm WEAK-SLOT-P-of-FIX-SLOT
  (WEAK-SLOT-P (FIX-SLOT slot))
  :hints (("Goal" :in-theory (enable fix-slot))))

(defthm default-rv
  (implies
   (not (memberp (sblk size (+<> off base)) (keys-spec :all base spec)))
                 (equal (rv size off base spec)
                        0))
  :hints (("Goal" :in-theory (enable fix-slot))))

(defthm ws-of-ws
  (implies
   (compare base s1 o1 s2 o2)
   (equal (ws s1 o1 base v1 (ws s2 o2 base v2 spec))
          (ws s1 o1 base v1 spec))))

(defthm wv-of-wv
  (implies
   (compare base s1 o1 s2 o2)
   (equal (wv s1 o1 base v1 (wv s2 o2 base v2 spec))
          (wv s1 o1 base v1 spec))))

(local
 (defthm ws-over-ws
   (implies
    (syntaxp (not (acl2::term-order p1 p2)))
    (equal (ws s1 p1 base v1 (ws s2 p2 base v2 spec))
           (if (compare base s1 p1 s2 p2)
               (ws s1 p1 base v1 spec)
             (ws s2 p2 base v2 (ws s1 p1 base v1 spec)))))))

(defthm wv-over-wv
  (implies
   (syntaxp (not (acl2::term-order p1 p2)))
   (equal (wv s1 p1 base v1 (wv s2 p2 base v2 spec))
          (if (compare base s1 p1 s2 p2)
              (wv s1 p1 base v1 spec)
            (wv s2 p2 base v2 (wv s1 p1 base v1 spec))))))

(defthm h*-spec-nil-wv
  (implies
   (equal hop (op :nil :z))
   (equal (h*-spec hop (wv size off base val spec))
          (h*-spec hop spec)))
  :hints (("goal" :induct (wv size off base val spec))))

(defthm h*-spec-of-ws
  (implies
   (not (g-op hop))
   (equal (h*-spec hop (ws size off base skel spec))
          (let ((skel (fix-skel skel)))
            (let ((wbase (skel-base skel)))
              (ws size off base (skel (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                             (op-base (op-how hop) :ptr wbase 0))
                                      (h*-spec hop (skel-spec (fix-skel skel))))
                  (h*-spec hop spec))))))
  :hints (("goal" :in-theory (enable ;unfixed-size-wfixn
                                     g? fix-skel)
           :induct (ws size off base skel spec))))


(defun spec-spec-induction (spec1 spec2)
  (declare (type t spec1 spec2))
  (if (and (consp spec1)
           (consp spec2))
      (spec-spec-induction (cdr spec1) (cdr spec2))
    (cons spec1 spec2)))

(defthm consp-ws
  (equal (consp (ws size off base value spec))
         (consp spec)))

(defthm consp-wv
  (equal (consp (wv size off base value spec))
         (consp spec)))

(defthm non-integerp-wv
  (implies
   (not (integerp off))
   (equal (wv size off base value spec)
          (wv size 0 base value spec))))

(defthm non-integerp-ws
  (implies
   (not (integerp off))
   (equal (ws size off base value spec)
          (ws size 0 base value spec))))

(defthm unfixed-size-wv
  (implies
   (syntaxp (syntax-unfixed-size size))
   (equal (wv size off base value spec)
          (wv (fix-size size) off base value spec)))
  :hints (("Goal" :in-theory (enable ;UNFIXED-SIZE-WFIXN
                                     ))))

(defthm unfixed-size-rv
  (implies
   (syntaxp (syntax-unfixed-size wsize))
   (equal (rv wsize woff base spec)
          (rv (fix-size wsize) woff base spec)))
  :hints (("Goal" :in-theory (enable ;UNFIXED-SIZE-WFIXN
                                     ))))

(defthm unfixed-size-ws
  (implies
   (syntaxp (syntax-unfixed-size size))
   (equal (ws size off base value spec)
          (ws (fix-size size) off base value spec))))

(defthm unfixed-size-rs
  (implies
   (syntaxp (syntax-unfixed-size wsize))
   (equal (rs wsize woff base spec)
          (rs (fix-size wsize) woff base spec))))

;; ==============================================
;;
;; zv
;;
;; ==============================================

(defun zv (list base spec)
  (declare (type t list spec))
  (if (consp list)
      (let ((sblk (car list)))
        (if (and (sblkp sblk) (consp sblk))
            (met ((size off) (sblk-parms base sblk))
                 (let ((spec (wv size off base 0 spec)))
                   (zv (cdr list) base spec)))
          (zv (cdr list) base spec)))
    spec))

(defthm open-zv
  (and
   (implies
    (consp list)
    (equal (zv list base spec)
           (let ((sblk (car list)))
             (if (and (sblkp sblk) (consp sblk))
                 (met ((size off) (sblk-parms base sblk))
                      (let ((spec (wv size off base 0 spec)))
                        (zv (cdr list) base spec)))
               (zv (cdr list) base spec)))))
   (implies
    (not (consp list))
    (equal (zv list base spec) spec))))

(in-theory
 (disable
  (:definition zv)
  ))

(defthm zv-of-wv
  (implies
   (memberp (sblk wsize (+<> woff base)) list)
   (equal (zv list base (wv wsize woff base value spec1))
          (zv list base spec1)))
  :hints (("goal" :induct (zv list base spec1))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
                         :do-not-induct t
                         :in-theory (enable ifix
                                            fix-skel)))))




(defthm skel-p-of-slot-skel-of-fix-slot
  (implies (SKEL-P (SLOT-SKEL slot))
           (SKEL-P (SLOT-SKEL (FIX-SLOT slot))))
  :hints (("Goal" :in-theory (enable fix-slot slot-skel SKEL-P slot))))

(defthm slot-p-of-fix-slot
  (implies (SLOT-p slot)
           (SLOT-p (FIX-SLOT slot)))
  :hints (("Goal" :in-theory (enable fix-slot slot-skel SKEL-P slot weak-slot-p))))

(defthm split-blk-when-spec-is-not-a-consp
  (implies (not (consp spec))
           (equal (split-blk spec)
                  (MV SPEC NIL))))

;bzo
(defthm rv-of-cons-one
  (implies (AND (GACC::SLOT-P GACC::SLOT)
                (GACC::COMPARE GACC::BASE GACC::SIZE
                               GACC::OFF (GACC::SLOT-SIZE GACC::SLOT)
                               (GACC::SLOT-OFF GACC::SLOT)))
           (equal (GACC::RV GACC::SIZE GACC::OFF GACC::BASE (cons gacc::slot GACC::SPEC))
                  (acl2::LOGHEAD (GACC::FIX-SIZE GACC::SIZE)
                                 (IFIX (GACC::SLOT-VAL GACC::SLOT)))))
  :hints (("Goal" :in-theory (enable gacc::rv))))

(defthm rv-of-cons-irrel-one
  (implies (not (GACC::SLOT-P GACC::SLOT))
           (equal (GACC::RV GACC::SIZE GACC::OFF GACC::BASE (cons gacc::slot GACC::SPEC))
                  (GACC::RV GACC::SIZE GACC::OFF GACC::BASE GACC::SPEC)))
  :hints (("Goal" :in-theory (enable gacc::rv))))

(defthm rv-of-cons-irrel-two
  (implies (not (GACC::COMPARE GACC::BASE GACC::SIZE
                               GACC::OFF (GACC::SLOT-SIZE GACC::SLOT)
                               (GACC::SLOT-OFF GACC::SLOT)))
           (equal (GACC::RV GACC::SIZE GACC::OFF GACC::BASE (cons gacc::slot GACC::SPEC))
                  (GACC::RV GACC::SIZE GACC::OFF GACC::BASE GACC::SPEC)))
  :hints (("Goal" :in-theory (enable gacc::rv))))

(defthm rv-of-cons-both
  (equal (GACC::RV GACC::SIZE GACC::OFF GACC::BASE (cons gacc::slot GACC::SPEC))
         (if  (AND (GACC::SLOT-P GACC::SLOT)
                   (GACC::COMPARE GACC::BASE GACC::SIZE
                                  GACC::OFF (GACC::SLOT-SIZE GACC::SLOT)
                                  (GACC::SLOT-OFF GACC::SLOT)))
             (acl2::LOGHEAD (GACC::FIX-SIZE GACC::SIZE)
                      (IFIX (GACC::SLOT-VAL GACC::SLOT)))
           (GACC::RV GACC::SIZE GACC::OFF GACC::BASE GACC::SPEC)))
  :hints (("Goal" :in-theory (enable gacc::rv))))

(defthm FIXED-SPEC-P-of-non-cons
  (implies (not (consp spec))
           (equal (FIXED-SPEC-P SPEC)
                  t)))

(defthm f*-spec-of-non-cons
  (implies (not (consp spec))
           (equal (F*-SPEC OP PTR SPEC)
                  nil)))

(defun start-of-f*-spec (op ptr slot)
  (IF
   (SLOT-P SLOT)
   (LET
    ((W (OP-WHICH OP)) (H (OP-HOW OP)))
    (LET
     ((OFF (SLOT-OFF SLOT))
      (SIZE (SLOT-SIZE SLOT))
      (TYPE (SLOT-TYPE SLOT))
      (SKEL (SLOT-SKEL SLOT))
      (VALUE (SLOT-VAL SLOT)))
     (LET
      ((READ VALUE))
      (LET
       ((BASE (SKEL-BASE SKEL)))
       (LET
        ((BASE
          (ACL2::LOGHEAD (FIX-SIZE SIZE)
                         (IFIX (OP-BASE H TYPE BASE READ)))))
        (LET
         ((BLK (IF (WHICHTYPE W TYPE)
                   (LIST (SBLK SIZE (|+<>| OFF PTR)))
                   NIL)))
         (LET ((REC (IF (PTR? TYPE)
                        (F*-SPEC OP BASE (SKEL-SPEC SKEL))
                        NIL)))
              (APPEND BLK
                      REC))))))))
   nil))

(defthm f*-spec-of-cons
  (equal (F*-SPEC OP PTR (cons slot SPEC))
         (append (start-of-f*-spec op ptr slot) (F*-SPEC OP PTR SPEC))))




(defthm zv-introduction-left
  (implies (fixed-spec-p spec2)
           (equal (equal (wv wsize woff base value spec1) spec2)
                  (let ((sblk (sblk wsize (+<> woff base))))
                    (and (equal (zv (list sblk) base spec1)
                                (zv (list sblk) base spec2))
                         (implies (memberp sblk (keys-spec :all base spec1))
                                  (equal (acl2::loghead (gacc::fix-size wsize) ;wfixn 8 wsize
                                                        value)
                                         (rv wsize woff base spec2)))))))
;  :otf-flg t
  :hints (("goal" ; :in-theory (enable acl2::memberp-of-cons)
           :expand ((RV (FIX-SIZE WSIZE) WOFF BASE SPEC2)
                    (H*-SPEC (OP :NIL :Z) SPEC1)
                    )
           :in-theory (e/d () (;split-blk ;bzo handle this
                              OPEN-H*-SPEC
                              OPEN-F*-SPEC
                               rv
                               slot-p
                               fix
                               SKEL-EXTENSIONALITY!
                               DEFS-SKEL-P-INCLUDES-WEAK-SKEL-P
                               OP-BASE
                               FIXED-SPEC-P
                               EQUAL-SBLK-EXTENSIONALITY
                               VANISHING-WV
                               ACL2::LOGHEAD-UPPER-BOUND
                               ACL2::LOGHEAD-NONNEGATIVE-LINEAR
;             SLOT-EXTENSIONALITY!!
;                       numtype
                               ))
           :induct (spec-spec-induction spec1 spec2)
           :do-not '(generalize eliminate-destructors ;fertilize
                                eliminate-irrelevance)
           :do-not-induct t)))

;(in-theory (disable unfixed-size-wintn))




;bzo trying disabled. try removing altogether...
(defthmd zv-introduction-right
  (implies
   (fixed-spec-p spec2)
   (equal (equal spec2 (wv wsize woff base value spec1))
          (let ((sblk (sblk wsize (+<> woff base))))
            (and (equal (zv (list sblk) base spec2)
                        (zv (list sblk) base spec1))
                 (implies (memberp sblk (keys-spec :all base spec1))
                          (equal (acl2::loghead (gacc::fix-size wsize) ;wfixn 8 wsize
                                        value) (rv wsize woff base spec2)))))))
  :hints (("goal" :in-theory (disable zv-introduction-left)

           :use ((:instance zv-introduction-left)))))

(defthm h*-spec-nil-zv
  (implies
   (equal hop (op :nil :z))
   (equal (h*-spec hop (zv list base spec))
          (h*-spec hop spec)))
  :hints (("goal" :induct (zv list base spec))))

(defthm keys-spec-zv
  (equal (keys-spec w base (zv list base spec))
         (keys-spec w base spec)))

(defthm fixed-spec-p-wv
  (implies
   (fixed-spec-p spec)
   (fixed-spec-p (wv size off base value spec)))
  :hints (("goal" :in-theory (enable ;unfixed-size-wintn
                                     ))))

(defthm fixed-spec-p-zv
  (implies
   (fixed-spec-p spec)
   (fixed-spec-p (zv list base spec))))

(defthm fixed-spec-p-ws
  (implies
   (and
    (fixed-spec-p spec)
    (acl2::unsigned-byte-p (gacc::fix-size size) ;wintn 8 size
           (skel-base skel))
    (fixed-spec-p (skel-spec skel)))
   (fixed-spec-p (ws size off base skel spec)))
  :hints (("goal"
           :in-theory (enable ;unfixed-size-wintn
                              fix-skel)
           :induct (ws size off base skel spec))))

(defthmd zv-over-wv
  (equal (zv list1 base (wv size off base 0 spec))
         (wv size off base 0 (zv list1 base spec)))
  :hints (("goal" :induct (zv list1 base spec)
           :in-theory (e/d (ifix)
                           (zv-introduction-right
                            zv-introduction-left)))))

;bzo move
;similar rule for wintn?
;; (defthm wfixn-of-fix-size
;;   (equal (acl2::loghead (gacc::fix-size (fix-size wsize)) ;wfixn 8 (fix-size wsize)
;;                 value)
;;          (wfixn 8 wsize
;;                 value))
;;   :hints (("Goal" :in-theory (enable unfixed-size-wfixn))))

(in-theory
 (disable
  zv-introduction-left
  zv-introduction-right
  zv-induction
  ))

;; ==============================================
;;
;; zs
;;
;; ==============================================

(defun zs (list base spec)
  (declare (type t list spec))
  (if (consp list)
      (let ((sblk (car list)))
        (if (and (sblkp sblk) (consp sblk))
            (met ((size off) (sblk-parms base sblk))
                 (let ((spec (ws size off base (skel 0 nil) spec)))
                   (zs (cdr list) base spec)))
          (zs (cdr list) base spec)))
    spec))

(defthm zs-when-base-is-not-an-integerp
  (implies (not (integerp base))
           (equal (ZS LIST BASE SPEC)
                  (ZS LIST 0 SPEC)))
  :hints (("Goal" :in-theory (disable ;ZS-INTRODUCTION-LEFT ;bzo looped (this lemma was lower down in the file)
                                      ))))
(defthm open-zs
  (and
   (implies
    (consp list)
    (equal (zs list base spec)
           (let ((sblk (car list)))
             (if (and (sblkp sblk) (consp sblk))
                 (met ((size off) (sblk-parms base sblk))
                      (let ((spec (ws size off base (skel 0 nil) spec)))
                        (zs (cdr list) base spec)))
               (zs (cdr list) base spec)))))
   (implies
    (not (consp list))
    (equal (zs list base spec) spec))))

(in-theory
 (disable
  (:definition zs)
  ))

(defthm zs-of-ws
  (implies
   (memberp (sblk wsize (+<> woff base)) list)
   (equal (zs list base (ws wsize woff base value spec1))
          (zs list base spec1)))
  :hints (("goal" :induct (zs list base spec1))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
                         :do-not-induct t
                         :in-theory (enable ifix fix-skel memberp)))))

(local
 (defthm not-skel-p-ws
   (implies
    (not (skel-p value))
    (equal (ws size off base value spec)
           (ws size off base (skel 0 nil) spec)))
   :hints (("goal" :in-theory (enable fix-skel))))
 )


#|
;old, slow-proving version
(defthm zs-introduction-left
  (iff (equal (ws wsize woff base value spec1)
              spec2)
       (let ((sblk (sblk wsize (+<> woff base))))
         (and (equal (zs (list sblk) base spec1)
                     (zs (list sblk) base spec2))
              (implies (memberp sblk (keys-spec :ptr base spec1))
                       (equal (fix-skel value) (rs wsize woff base spec2))))))
  :hints (("goal" :induct (spec-spec-induction spec1 spec2))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
                         :do-not-induct t
                         :in-theory (enable ;acl2::memberp-of-cons
                                     slot-extensionality!
                                     ifix
                                     fix-skel)))))

|#

(defthm split-blk-when-spec-is-not-a-consp
  (implies (not (consp spec))
           (equal (SPLIT-BLK spec)
                  (mv spec nil))))

(defthm zs-introduction-left
  (equal (equal (ws wsize woff base value spec1) spec2)
         (let ((sblk (sblk wsize (+<> woff base))))
           (and (equal (zs (list sblk) base spec1)
                       (zs (list sblk) base spec2))
                (implies (memberp sblk (keys-spec :ptr base spec1))
                         (equal (fix-skel value) (rs wsize woff base spec2))))))
  :otf-flg t
  :hints (("goal" :induct (spec-spec-induction spec1 spec2))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
                         :do-not-induct t
                         :expand (;(H*-SPEC (OP :NIL :Z) SPEC1)
                                  )
                         :in-theory (e/d ()
                                         (FIX
                                          ;PTR?
                                          ;split-blk
                                          slot-p
                                          ;efficiency:
                                          ;RS
                                          ;whichtype
                                          ;OPEN-H*-SPEC
                                          VANISHING-WS
                                          op-base
                                          fix-slot
                                          SKEL-EXTENSIONALITY!
                                          DEFS-SKEL-P-INCLUDES-WEAK-SKEL-P
                                          ))))))

;bzo consider dropping (and renaming the -left rule since there'd be no -right rule)
(defthmd zs-introduction-right
  (equal (equal spec2 (ws wsize woff base value spec1))
         (let ((sblk (sblk wsize (+<> woff base))))
           (and (equal (zs (list sblk) base spec2)
                       (zs (list sblk) base spec1))
                (implies (memberp sblk (keys-spec :ptr base spec1))
                         (equal (fix-skel value) (rs wsize woff base spec2))))))
  :hints (("goal" :in-theory (disable zs-introduction-left)
           :use ((:instance zs-introduction-left)))))


(defthm open-split-blk
  (and
   (implies
    (consp spec)
    (equal (split-blk spec)
           (let ((slot (car spec)))
             (if (slot-p slot)
                 (let ((slot (fix-slot slot)))
                   (let ((type (slot-type slot))
                         (skel (slot-skel slot)))
                     (if (ptr? type)
                         (let ((base (skel-base skel)))
                           (let ((line (line base skel)))
                             (let ((slot (update-slot slot :skel (skel base nil))))
                               (met ((spec list) (split-blk (cdr spec)))
                                    (mv (cons slot spec)
                                        (cons line list))))))
                       (met ((spec list) (split-blk (cdr spec)))
                            (mv (cons slot spec) list)))))
               (met ((spec list) (split-blk (cdr spec)))
                    (mv (cons slot spec) list))))))
   (implies
    (not (consp spec))
    (equal (split-blk spec) (mv spec nil)))))

(in-theory
 (disable
  (:definition split-blk)
  ))

(defthm split-sblk-ws
  (equal (f*-spec op ptr (v0 (split-blk (ws size off base value spec))))
         (f*-spec op ptr (v0 (split-blk spec))))
  :hints (("goal" :induct (ws size off base value spec))))

(defthm keys-spec-zs
  (equal (keys-spec w base (zs list base spec))
         (keys-spec w base spec))
  :hints (("goal" :in-theory (enable ifix)
           :induct (zs list base spec))))

(defthm fixed-spec-p-zs
  (implies
   (fixed-spec-p spec)
   (fixed-spec-p (zs list base spec))))


(defthmd zs-over-ws
  (implies
   (equal value (skel 0 nil))
   (equal (zs list1 base (ws size off base value spec))
          (ws size off base value (zs list1 base spec))))
  :hints (("goal" :induct (zs list1 base spec)
           :in-theory (e/d (ifix)
                           (zs-introduction-right
                            zs-introduction-left)))))

(in-theory
 (disable
  zs-introduction-left
  zs-introduction-right
  zs-induction
  ))

;; ==============================================
;;
;; zz
;;
;; ==============================================

(defun zz (vlist slist base spec)
  (declare (type t vlist slist spec))
  (let ((spec (zv vlist base spec)))
    (zs slist base spec)))


;I think the failed-location / tag-location stuff gives us debugging information in failed proofs.

(defund failed-location (key)
  (declare (ignore key))
  nil)

(in-theory (disable (:executable-counterpart failed-location)))
(in-theory (disable (:type-prescription failed-location)))

(defun tag-location (key bool)
  (implies (not bool) (failed-location key)))

(defthm zz-wv-introduction
  (implies
   (fixed-spec-p spec2)
   (and (equal (equal (wv wsize woff base value spec1)
                      spec2)
               (let ((sblk (sblk wsize (+<> woff base))))
                 (and (equal (zz (list sblk) nil base spec1)
                             (zz (list sblk) nil base spec2))
                      (implies (memberp sblk (keys-spec :all base spec1))
                               (tag-location woff (equal (acl2::loghead (gacc::fix-size wsize) ;wfixn 8 wsize
                                                                value)
                                                         (rv wsize woff base spec2)))))))
        ))
  :hints (("goal" :in-theory '(tag-location failed-location zz zs
                                            zv-introduction-left zv-introduction-right))))


(defthm zz-ws-introduction
  (and (equal (equal (ws wsize woff base value spec1)
                     spec2)
              (let ((sblk (sblk wsize (+<> woff base))))
                (and (equal (zz nil (list sblk) base spec1)
                            (zz nil (list sblk) base spec2))
                     (implies (memberp sblk (keys-spec :ptr base spec1))
                              (tag-location woff (equal (fix-skel value)
                                                        (rs wsize woff base spec2)))))))
;;        (equal (equal spec2
;;                      (ws wsize woff base value spec1))
;;               (let ((sblk (sblk wsize (+<> woff base))))
;;                 (and (equal (zz nil (list sblk) base spec2)
;;                             (zz nil (list sblk) base spec1))
;;                      (implies (memberp sblk (keys-spec :ptr base spec1))
;;                               (tag-location woff (equal (rs wsize woff base spec2)
;;                                                         (fix-skel value)))))))
       )
  :hints (("goal" :in-theory '(tag-location failed-location zz zv
                                            zs-introduction-left zs-introduction-right))))

(in-theory
 (disable
  zz-wv-introduction
  zz-ws-introduction
  ))

(defthm ws-wv
  (equal (wv s1 o1 base v1 (ws s2 o2 base v2 spec))
         (ws s2 o2 base v2 (wv s1 o1 base v1 spec))))

(defthm zv-over-ws
  (equal (zv list base (ws wsize woff base value spec))
         (ws wsize woff base value (zv list base spec)))
  :hints (("goal" :induct (zv list base spec))))

(defthm zs-over-wv
  (equal (zs list base (wv wsize woff base value spec))
         (wv wsize woff base value (zs list base spec)))
  :hints (("goal" :induct (zs list base spec))))


(defthm rs-zv
  (equal (rs rsize roff base (zv list base spec))
         (rs rsize roff base spec))
  :hints (("goal" :induct (zv list base spec))))

(defthm rv-zs
  (equal (rv rsize roff base (zs list base spec))
         (rv rsize roff base spec))
  :hints (("goal" :induct (zs list base spec))))

(defthm zz-ws-induction
  (implies
   (and
    (equal sblk (sblk wsize (+<> woff base)))
    (not (memberp sblk slist)))
   (and (equal (equal (zz vlist slist base (ws wsize woff base value spec1))
                      (zz vlist slist base spec2))
               (and (equal (zz vlist (cons sblk slist) base spec1)
                           (zz vlist (cons sblk slist) base spec2))
                    (implies (memberp sblk (keys-spec :ptr base spec1))
                             (tag-location woff (equal (fix-skel value)
                                                       (rs wsize woff base spec2))))))
;;         (equal (equal (zz vlist slist base spec2)
;;                       (zz vlist slist base (ws wsize woff base value spec1)))
;;                (and (equal (zz vlist (cons sblk slist) base spec2)
;;                            (zz vlist (cons sblk slist) base spec1))
;;                     (implies (memberp sblk (keys-spec :ptr base spec1))
;;                              (tag-location woff (equal (fix-skel value)
;;                                                        (rs wsize woff base spec2))))))
        ))
  :hints (("goal" :in-theory '(tag-location failed-location zz
                                            zv-over-ws zs-induction rs-zv keys-spec-zv))))

(defthm zs-over-zv
  (equal (zs slist base (zv vlist base spec))
         (zv vlist base (zs slist base spec))))

(defthm zv-over-zs
  (equal (zv vlist base (zs slist base spec))
         (zs slist base (zv vlist base spec))))

(in-theory
 (disable
  zv-over-zs
  ))

(defthm zz-wv-induction
  (implies
   (and
    (equal sblk (sblk wsize (+<> woff base)))
    (fixed-spec-p spec2)
    (not (memberp sblk vlist)))
   (and (equal (equal (zz vlist slist base (wv wsize woff base value spec1))
                      (zz vlist slist base spec2))
               (and (equal (zz (cons sblk vlist) slist base spec1)
                           (zz (cons sblk vlist) slist base spec2))
                    (implies (memberp sblk (keys-spec :all base spec1))
                             (tag-location woff (equal (acl2::loghead (gacc::fix-size wsize) ;wfixn 8 wsize
                                                                      value
                                                                      )
                                                       (rv wsize woff base spec2))))))
        ))
  :hints (("goal" :in-theory '(tag-location failed-location zz
                                            fixed-spec-p-zs
                                            zs-over-zv
                                            zs-over-wv
                                            zv-induction
                                            rv-zs
                                            keys-spec-zs))))

;              ))

(in-theory
 (disable
  failed-location
  (:type-prescription failed-location)
  (failed-location)
  ))

(in-theory
 (disable
  unfixed-size-wv
  unfixed-size-rv
  unfixed-size-ws
  unfixed-size-rs
  ))

(in-theory
 (disable
  open-wv
  open-ws
  rv-zs
  rs-zv
  zs-over-ws
  zv-over-ws
  vanishing-ws
  default-rs
  default-rv
  zz
  ))

;; For efficiency ..

(in-theory
 (disable
  wv-of-wv
  ws-of-ws
  ws-wv
  ))

(in-theory
 (enable
  zz-wv-introduction
  zz-ws-introduction
  zz-wv-induction
  zz-ws-induction
  ))

;;
;; f*/ws-wv
;;

(defthm f*-spec-wv
  (implies
   (not (memberp (sblk wsize (+<> woff base)) (keys-spec :ptr base spec)))
   (equal (f*-spec fop ptr (wv wsize woff base value spec))
          (f*-spec fop ptr spec)))
  :hints (("goal" :induct (wv wsize woff base value spec)
           :in-theory (enable open-wv memberp))))

;(in-theory (enable unfixed-size-wfixn))
;(in-theory (enable unfixed-size-wintn))

(defthm f*-spec-x-ws
  (implies
   (and
    (x? fop)
    (equal v (rs wsize woff base spec))
    (equal (f*-spec fop (acl2::loghead (gacc::fix-size wsize) ;wfixn 8 wsize
                               (skel-base (fix-skel skel))) (skel-spec (fix-skel skel)))
           (f*-spec fop (acl2::loghead (gacc::fix-size wsize) ;wfixn 8 wsize
                               (skel-base v)) (skel-spec v)))
    )
   (equal (f*-spec fop ptr (ws wsize woff base skel spec))
          (f*-spec fop ptr spec)))
  :hints (("goal'" :induct (ws wsize woff base skel spec)
           :in-theory (e/d (;unfixed-size-wfixn unfixed-size-wintn
                                               ) (;WFIXN-OF-FIX-SIZE
                                                  ))
           )
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
                         :do-not-induct t
                         :in-theory (e/d (;unfixed-size-wfixn unfixed-size-wintn
                                                             open-ws) (;WFIXN-OF-FIX-SIZE
                                                                       ))
                         ))))

;;
;; h*/ws-wx
;;

(defthm h*-spec-of-wv
  (implies
   (and
    (equal (op-which hop) :nil)
    (not (g-op hop)))
   (equal (h*-spec hop (wv wsize woff base value spec))
          (h*-spec hop spec)))
  :hints (("goal" :induct (wv wsize woff base value spec)
           :in-theory (e/d (g? open-wv) (zz-wv-introduction)))))

(defthm h*-spec-over-wv
  (implies
   (and
    (equal (op-which hop) :all)
    (not (g-op hop)))
   (equal (h*-spec hop (wv wsize woff base value spec))
          (wv wsize woff base (acl2::loghead (gacc::fix-size wsize) ;wfixn 8 wsize
                                             value) (h*-spec hop spec))))
  :hints (("goal" :induct (wv wsize woff base value spec)
           :in-theory (e/d (g? open-wv ;unfixed-size-wfixn
                               )
                           (zz-wv-introduction
;                            WFIXN-OF-FIX-SIZE
                            )))))

;;  ; was called wintn-rs for some reason
;; (defthm wintn-rv
;;   (wintn 8 size (rv size off base spec))
;;   :hints (("Goal" :in-theory (enable UNFIXED-SIZE-WINTN))))

(defthm fixed-spec-p-rs
  (implies
   (fixed-spec-p spec)
   (and (fixed-spec-p (skel-spec (rs size off base spec)))
        (acl2::unsigned-byte-p (gacc::fix-size size) ;wintn 8 size
               (skel-base (rs size off base spec)))))
  :hints (("goal" :in-theory (enable ;UNFIXED-SIZE-WINTN
                                      )
           :induct (rs size off base spec))))

(in-theory (disable wv-over-wv))

;eric added the next 2. are they okay?
(defthm ws-of-rs-helper
  (equal (ws size off base (rs size off base spec) spec)
         spec))

(defthm wv-of-rv-helper
  (implies (fixed-spec-p spec);t; (WINTN 8 32 (SLOT-VAL (CAR SPEC)))
           (equal (wv size off base (rv size off base spec) spec)
                  spec)))

;bzo what do we do in the base case? need to know the size of the target record, right?
(defun mypush-aux (keys r size)
  (if (set::empty keys)
      (mem::new size) ;nil ;the empty typed record
    (gacc::wr (set::head keys)
              (g (set::head keys) r)
              (mypush-aux (set::tail keys) r size))))

(defund mypush (r size)
  (mypush-aux (set::rkeys r) r size))

;; ;bzo add (or maybe this doesn't type-check?)
;; (defthm load-of-nil
;;   (equal (mem::load a nil)
;;          nil)
;;   :hints (("Goal" :in-theory (enable MEM::LOAD
;;                                      MEM::|_LOAD|))))

(defthm rd-of-new
  (equal (gacc::rd a (mem::new size))
         0)
  :hints (("Goal" :in-theory (enable gacc::rd))))

(defthm rd-of-mypush-aux
  (equal (gacc::rd a (mypush-aux rkeys r size))
         (if (set::in a rkeys)
             (loghead 8 (g a r))
           0)))

;for dave
(defthm rd-of-mypush
  (equal (gacc::rd a (mypush r size))
         (if (set::in a (set::rkeys r))
             (loghead 8 (g a r))
           0))
  :hints (("Goal" :in-theory (enable mypush))))

(defthm memory-clr-of-new
  (equal (gacc::memory-clr a (mem::new size))
         (mem::new size))
  :hints (("Goal" :in-theory (enable gacc::memory-clr))))

(defthm memory-clr-of-mypush-aux
  (equal (gacc::memory-clr key (mypush-aux rkeys r size))
         (mypush-aux rkeys (clr key r) size)))

;; ;what we really need is the analogous theorem for insert?
;; (defthm mypush-aux-of-cons
;;   (equal (mypush-aux (cons a rkeys) r)
;;          (gacc::wr a (g a r) (mypush-aux rkeys r)))
;;   :hints (("Goal" :induct t
;;            :expand ((MYPUSH-AUX (CONS A (SET::TAIL RKEYS))
;;                                  R)
;;                     (MYPUSH-AUX (CONS A RKEYS) R)
;;                     (SET::HEAD (CONS A RKEYS))
;;                     (SET::SETP (CONS A RKEYS))
;;                     (SET::EMPTY (CONS A RKEYS))
;;                     (SET::TAIL (CONS A RKEYS)))
;;            :in-theory (disable GACC::WR==R!)
;;            :do-not '(generalize eliminate-destructors))))


(local
 (defun my-ind (a rkeys r)
   (if (set::empty rkeys)
       (list a rkeys r)
     (if (equal a (set::head (set::insert a rkeys)))
         (list a rkeys r)
       (my-ind a (set::tail rkeys) (s (set::head rkeys) (g (set::head rkeys) r) r))))))




;clean up conclusion?
(defthmd car-of-insert
  (equal (car (set::insert a x))
         (cond ((set::empty x) a)
               ((equal (set::head x) a) (set::head x))
               ((<< a (set::head x)) a)
               (t (set::head x))))
  :hints (("Goal" :expand (set::insert a x)
           :in-theory (enable set::insert set::head))))

(defthm set-hack
  (implies (not (equal a (set::head (set::insert a s))))
           (equal (set::tail (set::insert a s))
                  (set::insert a (set::tail s))))
  :otf-flg t
  :hints (
          ("Goal" :expand ((SET::INSERT A S) ;prove a setp of cons rule?
                           (SET::SETP S)
                           (SET::INSERT A NIL)
                           (SET::INSERT A (CDR S))
                           (SET::SETP (CDDR S))
                           (SET::SETP (CDR S))
                           (:free (x y) (set::setp (cons x y)))
                           )
           :in-theory (e/d (car-of-insert SET::EMPTY SET::HEAD SET::tail SET::SFIX) ( SET::PICK-A-POINT-SUBSET-STRATEGY))
           :do-not '(generalize eliminate-destructors))))

(defthm set-hack2
  (implies (not (equal a (set::head (set::insert a s))))
           (equal (SET::HEAD (SET::INSERT A s))
                  (SET::HEAD s)))
  :otf-flg t
  :hints (("Goal" :expand ((SET::INSERT A S) ;prove a setp of cons rule?
                           (SET::SETP S)
                           (SET::INSERT A NIL)
                           (SET::INSERT A (CDR S))
                           (SET::SETP (CDDR S))
                           (SET::SETP (CDR S))
                           (:free (x y) (set::setp (cons x y)))
                           )
           :in-theory (e/d (car-of-insert SET::EMPTY SET::HEAD SET::tail SET::SFIX) ( SET::PICK-A-POINT-SUBSET-STRATEGY))
           :do-not '(generalize eliminate-destructors))))


;expensive?
(defthm not-in-when-<<-car
  (implies (<< a (car s))
           (not (set::in a s)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((set::empty s)
                    (set::setp s))
           :in-theory (enable set::head set::tail))))



(defthm tail-of-insert-when-equal-head-of-insert
  (implies (and (syntaxp (not (equal a ''nil)))
                (equal a (set::head (set::insert a s))))
           (equal (set::tail (set::insert a s))
                  (set::delete a s)))
  :otf-flg t
  :hints (("Goal" :expand ((SET::INSERT A S) ;prove a setp of cons rule?
                           (SET::SETP S)
                           (SET::INSERT A NIL)
                           (SET::INSERT A (CDR S))
                           (SET::SETP (CDDR S))
                           (SET::SETP (CDR S))
                           (:free (x y) (set::setp (cons x y)))
                           )
           :in-theory (e/d (car-of-insert SET::EMPTY SET::HEAD SET::tail SET::SFIX) ( SET::PICK-A-POINT-SUBSET-STRATEGY))
           :do-not '(generalize eliminate-destructors))))




;combine these cases?
(defthm mypush-aux-of-insert
  (equal (mypush-aux (set::insert a rkeys) r size)
         (if (set::in a rkeys)
             (mypush-aux rkeys r size)
           (gacc::wr a (g a r) (mypush-aux rkeys r size))))
  :otf-flg t
  :hints (("Goal" :induct (my-ind a rkeys r)
           :expand ((MYPUSH-AUX (SET::INSERT A nil) R size)
                    (MYPUSH-AUX (SET::INSERT A RKEYS) R size))
           :in-theory (disable GACC::WR==R!
                               )
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))


(defthm memory-clr-of-mypush-aux2
  (equal (gacc::memory-clr key (mypush-aux rkeys r size))
         (mypush-aux (set::delete key rkeys) r size))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


;rename to say insert
(defthm mypush-aux-of-cons-irrel
  (implies (not (g key r))
           (equal (mypush-aux (set::insert key rkeys) r size)
                  (mypush-aux rkeys r size)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))




;drop?
(defthm mypush-aux-of-insert-irrel-of-clr
  (equal (mypush-aux (set::insert key rkeys) (clr key r) size)
         (mypush-aux rkeys (clr key r) size))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


(defthm mypush-irrel
  (implies (not (set::in key rkeys))
           (equal (mypush-aux rkeys (clr key r) size)
                  (mypush-aux rkeys r size)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


(defthm mypush-aux-of-clr
  (equal (mypush-aux rkeys (clr a r) size)
         (mypush-aux (set::delete a rkeys) r size))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


(defthm mypush-irrel2
  (implies (not (set::in key rkeys))
           (equal (mypush-aux rkeys (s key v r) size)
                  (mypush-aux rkeys r size)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

;for dave
(defthm mypush-of-s
  (equal (mypush (s a v r) size)
         (gacc::wr a v (mypush r size)))
  :hints (("Goal" :in-theory (enable mypush))))


;for dave
(defthm mypush-of-sp
  (equal (mypush (cpath::sp (list a) v r) size)
         (gacc::wr a v (mypush r size)))
  :hints (("Goal" :in-theory (enable cpath::sp))))

;need a way to get the keys of a typed record...  -can it be rkeys?
;then prove keys of wr = blah...

;;
;; my-lift (turn a typed-record into a regular record)
;;

;keys "bound" to 0 don't show up in the typed record (since 0 is the default
;value for typed records) and so become keys "bound" to nil in the record
;(such keys don't show up, since nil is the default value for records).
(defun mylift-aux (keys tr)
  (if (set::empty keys)
      nil ;the empty record
    (s (set::head keys)
       (gacc::rd (set::head keys) tr)
       (mylift-aux (set::tail keys) tr))))

;bzo
(defund mylift (m)
  (mylift-aux (mem::domain m) m))

(defthm domain-of-wr
  (implies (good-memoryp tr)
           (equal (mem::domain (gacc::wr a v tr))
                  (if (gacc::wf-usbp8 (mem::load a tr))
                      (if (gacc::usbp8-zp v)
                          (if (cdr (mem::load a tr))
                              (set::insert a (mem::domain tr))
                            (set::delete a (mem::domain tr)))
                        (set::insert a (mem::domain tr)))
                    (if (gacc::usbp8-zp v)
                        (mem::domain tr)
                      (set::insert a (mem::domain tr))))))
  :otf-flg t
  :hints (("Goal" :expand ((gacc::wr a v tr))
;          :induct nil
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))

(defthm domain-of-wr-forced
  (implies (force (good-memoryp tr))
           (equal (mem::domain (gacc::wr a v tr))
                  (if (gacc::wf-usbp8 (mem::load a tr))
                      (if (gacc::usbp8-zp v)
                          (if (cdr (mem::load a tr))
                              (set::insert a (mem::domain tr))
                            (set::delete a (mem::domain tr)))
                        (set::insert a (mem::domain tr)))
                    (if (gacc::usbp8-zp v)
                        (mem::domain tr)
                      (set::insert a (mem::domain tr)))))))

(defthm g-of-mylift-aux
  (equal (g a (mylift-aux rkeys tr))
         (if (set::in a rkeys)
             (loghead 8 (gacc::rd a tr))
           nil)))

;for dave
(defthm g-of-mylift
  (equal (g a (mylift tr))
         (if (set::in a (mem::domain; rkeys
                         tr))
             (loghead 8 (gacc::rd a tr))
           nil))
  :hints (("Goal" :in-theory (enable mylift))))

;;
;; VAL-FIX
;;

(defun val-fix (v)
  (if (equal 0 (loghead 8 v))
      nil
     (loghead 8 v)))

;does this cause case splits?
(defthm integerp-of-val-fix
  (equal (integerp (acl2::val-fix x))
         (not (equal 0 (acl2::loghead 8 x))))
  :hints (("Goal" :in-theory (enable acl2::val-fix))))

(defthm loghead-8-of-val-fix
  (equal (acl2::loghead 8 (acl2::val-fix x))
         (acl2::loghead 8 x))
  :hints (("Goal" :in-theory (enable acl2::val-fix))))

(defthm wr-of-0-is-clr
  (implies (EQUAL (LOGHEAD 8 V) 0)
           (equal (GACC::WR A V TR)
                  (gacc::memory-clr A TR))))


;bzo improve CLR-OVER-CLR?

(defthm clr-of-clr-match-hack
  (implies (equal (clr b r1)
                  (clr b r2))
           (equal (equal (clr b (clr a r1))
                         (clr b (clr a r2)))
                  t))
  :hints (("Goal" :cases ((equal a b)))))

(defthm mylist-aux-of-insert
  (equal (mylift-aux (set::insert a rkeys) tr)
         (if (set::in a rkeys)
             (mylift-aux rkeys tr)
           (s a (gacc::rd a tr) (mylift-aux rkeys tr))))
  :otf-flg t
  :hints (("Goal" :induct (my-ind a rkeys rt)
           :expand ((MYLIFT-AUX (SET::INSERT A RKEYS) tR))
           :in-theory (disable GACC::WR==R!
                               )
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))

(defthm empty-means-tail-nil
  (implies (set::empty s)
           (equal (set::tail s)
                  (set::emptyset)))
  :hints (("Goal" :in-theory (enable set::empty set::tail set::sfix))))

;bzo may loop with defn delete or something?
(defthmd delete-from-tail-when-not-head
  (implies (not (equal key (set::head s)))
           (equal (set::delete key (set::tail s))
                  (set::delete (set::head s) (set::delete key s))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((set::delete key s)))))

(defthm clr-of-mylift-aux
  (equal (clr key (mylift-aux rkeys tr))
         (mylift-aux (set::delete key rkeys) (gacc::memory-clr key tr)))
  :hints (("Goal" :in-theory (disable SET::DELETE)
           :expand ((SET::DELETE KEY RKEYS))
           :do-not '(generalize eliminate-destructors))))

;; ;drop?
;; (defun wfr-weak (r)
;;   (and (rcdp r)
;;        (not (ifrp r)) ;;should really just use a typed version of ifrp?
;;        ))


(defun non-nil (x)
  (declare (xargs :guard t))
  (not (null x)))

;; ;sheesh even the guard has a guard...
;; (set::quantify-predicate (mem::address-p key mem) :arg-guard ((MEM::MEMORY-P MEM)))


(defun check-tr-val (val)
  (and (unsigned-byte-p 8 val)
       (not (equal 0 val))))

(defun check-tr-entry (val)
  (and ;(GACC::WF-USBP8 (cdr val))
   (equal nil (cdr val))
   (check-tr-val (car val))))

;bzo rename?
(defun check-fr-key (key tr)
  ;;   (declare (xargs :guard (and (MEM::MEMORY-P TR)
  ;;                               (NATP KEY)
  ;;                               (< KEY (MEM::SIZE TR)))))
  (let* ((val (mem::load key tr)))
    (or (null val)
        (and ;(consp val)
;(equal nil (cdr val)) ;(equal 1 (len val))
;(unsigned-byte-p 8 (car val))
;(not (equal 0 (car val)))
         (check-tr-entry val)
         ))))



;bzo bad name? really this checks the values?
(defun check-fr-keys (keys tr)
  (if (set::empty keys)
      t
    (and (check-fr-key (set::head keys) tr)
         (check-fr-keys (set::tail keys) tr))))


;; Well-formed fast-record, - bzo, bad name?
(defun wf-fr (tr)
  (and ;;(wfr-weak tr) ;;
       (good-memoryp tr) ;(wfr tr)
       ;(set::all<non-nil> (mem::domain TR)) ;like wfkeyed
       (check-fr-keys (mem::domain tr) tr)))

(defthm mylift-of-wr-1
  (implies (and (good-memoryp tr)
                (not (EQUAL 0 (LOGHEAD 8 V))))
           (equal (mylift (gacc::wr a v tr))
                  (s a (val-fix v) (mylift tr))))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable ;gacc::wr
                       mylift
                       ))))

;; (defthm cdr-of-g-nil-when-in-keys
;;   (implies (and (check-fr-keys keys tr)
;;                 (set::in k keys)
;;                 (set::subset keys (mem::domain tr))
;;                 )
;;            (not (cdr (mem::load k tr))))
;;   :hints (("Goal" :cases ((mem::load k tr))
;;            :do-not '(generalize eliminate-destructors))))

;drop?
(defthm sfix-of-rkeys
  (equal (set::sfix (set::rkeys tr))
         (set::rkeys tr))
  :hints (("Goal" :in-theory (enable rkeys))))

(defthm wfr-implies-wfr-of-cdr
  (implies (wfr tr)
           (wfr (cdr tr)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand (ifrp (cdr tr))
           :in-theory (enable wfr ifrp rcdp wfkeyed))))

;; (defthm wfr-weak-implies-wfr-weak-of-cdr
;;   (implies (wfr-weak tr)
;;            (wfr-weak (cdr tr)))
;;   :otf-flg t
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :expand (ifrp (cdr tr))
;;            :in-theory (enable wfr ifrp rcdp wfkeyed))))


;; (defthm wfr-weak-cancellations
;;   (implies (wfr-weak r)
;;            (and (equal (rcd->acl2 r) r)
;;                 (equal (acl2->rcd r) r)))
;;   :hints (("Goal" :in-theory (enable rcd->acl2 acl2->rcd))))

;; (defthm wf-fr-cancellations
;;   (implies (wf-fr r)
;;            (and (equal (rcd->acl2 r) r)
;;                 (equal (acl2->rcd r) r)))
;;   :hints (("Goal" :in-theory (enable rcd->acl2 acl2->rcd))))


;; (defthm wf-fr-implies-wf-fr-of-cdr
;;   (implies (wf-fr tr)
;;            (wf-fr (cdr tr)))
;;   :otf-flg t
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :expand (ifrp (cdr tr))
;;            :in-theory (enable wfr ifrp rcdp wfkeyed))))

;skipping for now...
;; (defthm not-consp-g-of-cdr-but-consp-g
;;   (IMPLIES (AND (NOT (CONSP (mem::load ;G
;;                              A (CDR TR))))
;;                 (CONSP (mem::load ;G
;;                         A TR))
;;                 (WFR TR) ;was wfr-weak
;;                 )
;;            (EQUAL (CAAR TR) A))
;;   :hints (("Goal" :in-theory (enable g
;;                                      ))))

;cool!  didn't have to open up the "record operations"
;go the other way too?
(defthm not-in-domain-means-load-is-nil
  (implies (and (not (set::in key (mem::domain fm)))
                (good-memoryp fm)
                )
           (equal (mem::load key fm)
                  nil))
  :hints (("Goal" :use (:instance domain-of-store
                                  (a key)
                                  (v (mem::load key fm))
                                  (mem fm))
           :in-theory (disable ;MEM::STORE-OF-SAME-LOAD
                       domain-of-store))))

(defthm not-in-domain-means-load-is-nil2
  (implies (good-memoryp fm)
           (equal (set::in key (mem::domain fm))
                  (not (equal nil (mem::load key fm)))))
  :hints (("Goal" :use (:instance domain-of-store
                                  (a key)
                                  (v (mem::load key fm))
                                  (mem fm))
           :in-theory (disable ;MEM::STORE-OF-SAME-LOAD
                       domain-of-store))))

;; ;see ACL2::NOT-IN-DOMAIN-MEANS-LOAD-IS-NIL2 and ACL2::G-MEANS-IN-KEYS
;; (defthm consp-g-means-in-keys
;;   (implies (and (good-memoryp tr) ;more generally, could say non-nil?
;;                 (consp (mem::load a tr)))
;;            (set::in a (mem::domain tr)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable rkeys key-set))))
;replace the consp-g-version?
(defthm g-means-in-keys
  (implies (and (mem::load a tr)
                (GOOD-MEMORYP tr) ;(wfr tr)
                )
           (set::in a (mem::domain tr)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           ;:in-theory (enable rkeys key-set g))))
           )))

;; (defthm g-of-caar
;;   (implies (wfr tr)
;;            (equal (g (caar tr) tr)
;;                   (CDAR TR)
;;                   ))
;;   :hints (("Goal" :in-theory (enable g)
;;            :do-not '(generalize eliminate-destructors))))

;; (defthm cons-g-cdr-means-consp-g
;;   (implies (and (consp (g a (cdr tr)))
;;                 (wfr tr))
;;            (consp (g a tr)))
;;   :hints (("Goal" :in-theory (enable g wfr))))

;bzo disable?
;; (defthm cdar-of-wfr-non-nil
;;   (implies (and (consp tr)
;;                 (wfr tr))
;;            (cdar tr))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :expand (rcdp tr)
;;            :in-theory (enable wfr rcdp wfkeyed wfkey))))

;bzo combine?
;; (defthm not-g-means-not-in-rkeys
;;   (implies (and (not (g a tr))
;;                 (wfr tr))
;;            (not (set::in a (set::rkeys tr))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;; ;           :expand ((G A TR))
;;            :in-theory (enable rkeys key-set))))

(defthm mylift-irrel
  (implies (not (set::in key keys))
           (equal (mylift-aux keys (gacc::memory-clr key tr))
                  (mylift-aux keys tr)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


;; (defthm mylift-aux-of-clr
;;   (equal (mylift-aux rkeys (gacc::memory-clr a t))
;;          (mylift-aux (set::delete a rkeys) t))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors))))


(defthm rd-of-s-irrel
  (implies (not (equal key1 key2))
           (equal (GACC::RD key1 (mem::store ;S
                                  KEY2 V TR))
                  (GACC::RD key1 TR)))
  :hints (("Goal" :in-theory (enable GACC::RD))))

(defthm mylift-irrel2
  (implies (not (set::in key rkeys))
           (equal (mylift-aux rkeys (mem::store ;s
                                     key v tr))
                  (mylift-aux rkeys tr)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


;; (defthmd check-fr-keys-lemma
;;   (IMPLIES (and (CHECK-FR-KEYS keys TR)
;;                 (set::in a keys)
;;                 (consp tr))
;;            (NOT (EQUAL (LOGHEAD 8 (CAR (mem::load ;G
;;                                         A TR))) 0))))

;ttt
;; (defthmd check-fr-keys-lemma2
;;   (IMPLIES (and (CHECK-FR-KEYS keys TR)
;;                 (set::in a keys)
;;                 (consp tr))
;;            (UNSIGNED-BYTE-P 8 (CAR (mem::load ;G
;;                                     A TR)))))

;maybe this is really load of new?
(defthm load-of-non-consp
  (implies (and (not (consp tr))
                (good-memoryp tr))
           (equal (MEM::LOAD A TR)
                  nil
                  ))
  :hints (("Goal" :in-theory (enable GOOD-MEMORYP
                                     MEM::LOAD
                                     MEM::MEMORY-P
                                     MEM::|_BAD-MEMORY-P|
                                     MEM::SIZE
                                     MEM::|_MEMORY-SIZE|
                                     MEM::|_MEMORY-P|
                                     MEM::|_MEMTREE-P|
                                     MEM::|_MEMTREE-FIX|
                                     MEM::|_MEMORY-MTREE|
                                     MEM::|_MEMORY-DEPTH|
                                     MEM::|_MEMTREE-LOAD|
                                     MEM::|_MEMORY-FIX|
                                     MEM::|_MEMORY-RECORD|
                                     mem::|_TO-MEM|
                                     MEM::|_LOAD|))))

;do we need this?
(defthm domain-of-non-consp
  (implies (not (consp m))
           (equal (mem::domain m)
                  nil))
  :hints (("Goal" :in-theory (enable MEM::DOMAIN
                                     GOOD-MEMORYP
                                     MEM::LOAD
                                     MEM::MEMORY-P
                                     MEM::|_BAD-MEMORY-P|
                                     MEM::SIZE
                                     MEM::|_MEMORY-SIZE|
                                     MEM::|_MEMORY-P|
                                     MEM::|_MEMTREE-P|
                                     MEM::|_MEMTREE-FIX|
                                     MEM::|_MEMORY-MTREE|
                                     MEM::|_MEMORY-DEPTH|
                                     MEM::|_MEMTREE-LOAD|
                                     MEM::|_MEMORY-FIX|
                                     MEM::|_MEMORY-RECORD|
                                     mem::|_TO-MEM|
                                     MEM::|_LOAD|))))

(defthm use-check-fr-keys
  (implies (and (check-fr-keys keys r)
                (set::in a keys))
           (check-fr-key a r)))

(in-theory (disable check-fr-key check-fr-keys))

(defthm use-check-fr-keys-2
  (implies (and (check-fr-keys keys r)
                (set::subset (mem::domain r) keys)
                (set::in a (mem::domain r)))
           (check-fr-key a r)))


(defthm mylift-of-wr-0-case
  (implies (and (wf-fr tr) ;(wfr tr)
                (good-memoryp tr)
                (equal 0 (loghead 8 v)))
           (equal (mylift (gacc::wr a v tr))
;if what was there was well-formed, we get 0.  otherwise (including if it was 0 before!), we get what was there!
                  (s a nil (mylift tr))))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;  :cases ((SET::in A (SET::RKEYS TR)))
           :use (;(:instance check-fr-keys-lemma (keys (mem::domain tr)))
                 ;(:instance check-fr-keys-lemma2 (keys (mem::domain tr)))
                 (:instance use-check-fr-keys (r tr) (keys (MEM::DOMAIN TR)))
                 )
           :in-theory (e/d ( ;gacc::wr
                            mylift
                            check-fr-keys
                            check-fr-key
                            GACC::MEMORY-CLR
                            )
                           (WR-OF-0-IS-CLR
                            LOGHEAD*-BETTER ;bzo why isn't this disabled?
                            LOGCAR-LOGCDR-ELIM
                            )))))

(in-theory (disable LOGHEAD*-BETTER))

;bzo can we improve this?
;for dave
(defthm mylift-of-wr
  (implies (and; (good-memoryp tr)
                (wf-fr tr)
                ;v
                )
           (equal (mylift (gacc::wr a v tr))
                  (s a (val-fix v) (mylift tr))))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :use ((:instance mylift-of-wr-0-case)
                 (:instance mylift-of-wr-1))
           :in-theory (disable MYLIFT
                               g-of-mylift
                               ))))

;see S-PRESERVES-WFR (should WFKEY be enabled?)

;bzo maybe wf-fr should allow nil keys?

;bzo move
(defthm load-of-store-redux
  (equal (mem::load a (mem::store b v r))
         (if (equal a b)
             v
           (mem::load a r))))

;bzo really what's checked by CHECK-FR-KEYS is the value -rename

(defthm check-fr-keys-of-store
  (implies (and (check-fr-keys keys tr)
                (or (null v)
                    (check-tr-entry v)) ;the whole entry, not the val
                )
           (check-fr-keys keys (mem::store a v tr)))
  :hints (("Goal" :in-theory (enable check-fr-keys check-fr-key)
           :do-not '(generalize eliminate-destructors))))

(defthm check-fr-keys-of-s-irrel
  (implies (not (set::in a keys))
           (equal (check-fr-keys keys (mem::store a nil tr))
                  (check-fr-keys keys tr)))
  :hints (("Goal" :in-theory (enable check-fr-keys check-fr-key))))

(defthm delete-when-would-be-head
  (implies (equal a (set::head (set::insert a keys)))
           (equal (set::delete a keys)
                  (if (set::in a keys)
                      (set::tail keys)
                    (set::sfix keys))))
  :hints (("Goal" :in-theory (enable set::sfix ;bzo
                                     ))))

(defthm car-of-insert-of-nil
  (equal (car (set::insert k nil))
         k)
  :hints (("Goal" :in-theory (enable set::insert))))

(defthm check-fr-keys-of-insert
  (equal (check-fr-keys (set::insert a keys) tr)
         (let* ((val (mem::load a tr)))
           (and (check-fr-keys keys tr)
                (or (null val)
                    (and (consp val)
                         (equal nil (cdr val))
                         (unsigned-byte-p 8 (car val))
                         (not (equal 0 (car val)))
                         )))))
  :otf-flg t
  :hints (("Goal" :induct (my-ind a keys r)
           :expand ((CHECK-FR-KEYS (SET::INSERT A KEYS) tR)
                    )
           :in-theory (e/d (CHECK-FR-KEYS CHECK-FR-KEY) ( gacc::wr==r! ))
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))

(defthm check-fr-keys-of-delete
  (implies (check-fr-keys keys tr)
           (check-fr-keys (set::delete a keys) tr))
  :hints (("Goal"
           :in-theory (e/d (CHECK-FR-KEYS CHECK-FR-KEY) (  ))
           :expand (CHECK-FR-KEYS (SET::INSERT (SET::HEAD KEYS)
                                               (SET::DELETE A (SET::TAIL KEYS)))
                                  TR)
           :do-not '(generalize eliminate-destructors))))
;ttt
;; (defthm consp-g-when-in-keys-and-check-fr-keys
;;   (implies (and (check-fr-keys keys tr)
;;                 (set::in a keys)
;;                 )
;;            (consp (mem::load ;g
;;                    a tr)))
;;   :hints (("Goal" :in-theory (enable check-fr-keys))))

;ttt
;; (defthm consp-g-when-g-and-check-fr-keys
;;   (implies (and (check-fr-keys (mem::domain ;rkeys
;;                                 tr) tr)
;;                 (mem::load ;g
;;                  a tr) ;is not nil
;;                 (good-memoryp ;;wfr
;;                  tr)
;;                 )
;;            (consp (mem::load ;g
;;                    a tr)))
;;   :hints (("Goal" :use (:instance consp-g-when-in-keys-and-check-fr-keys (keys (mem::domain ;rkeys
;;                                                                                 tr)))
;;            :in-theory (e/d (check-fr-keys) (consp-g-when-in-keys-and-check-fr-keys)))))

;; (defthm s-preserves-wfr-2
;;   (implies (wfr r)
;;            (equal (wfr (s a v r))
;;                   (or (wfkey a)
;;                       (not v))))
;;   :hints (("goal" :in-theory (enable ;s acl2->rcd rcd->acl2
;;                               WFR
;;                               WFKEY
;;                               ))))


(defthm use-check-fr-key-1
  (implies (check-fr-key a tr)
           (not (CDR (MEM::LOAD A TR))))
  :hints (("Goal" :in-theory (enable check-fr-key))))

(defthm use-check-fr-key-2
  (implies (check-fr-key a tr)
           (iff (consp (mem::load a tr))
                (mem::load a tr))
           )
  :hints (("Goal" :in-theory (enable check-fr-key))))

(defthm use-check-fr-key-3
  (implies (check-fr-key a tr)
           (or (null (mem::load a tr))
               (gacc::wf-usbp8 (mem::load a tr))
               ))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable check-fr-key))))


;for dave
(defthm wf-fr-of-wr
  (implies (and (wf-fr tr)
                ;;a ;that is, a is not nil
                )
           (wf-fr (gacc::wr a v tr)))
  :otf-flg t
  :hints (("Goal" :expand (CHECK-FR-KEYS (SET::INSERT A NIL) (mem::store A (LIST (LOGHEAD 8 V)) NIL))
           :use ( ;(:instance check-fr-keys-lemma2 (keys (mem::domain tr)))
;(:instance check-fr-keys-lemma (keys (mem::domain tr)))
                 (:instance use-check-fr-keys-2 (keys (MEM::DOMAIN TR)) (r tr))
                 use-check-fr-key-3
                 )
           :cases ((set::in a (MEM::DOMAIN TR)))
           :in-theory (e/d (GACC::WR wfkey ;GACC::WF-USBP8
                                     CHECK-TR-ENTRY
                                     ) ( ;check-fr-keys-lemma2 check-fr-keys-lemma
                                        ;;check-tr-entry
                                     USE-CHECK-FR-KEYS-2
                                     GACC::WF-USBP8
                                     )))))


;for dave
(defthm mylift-of-wr-sp-version
  (implies (wf-fr tr)
           (equal (mylift (gacc::wr a v tr))
                  (cpath::sp (list a) (val-fix v) (mylift tr))))
  :hints (("Goal" :in-theory (e/d ( CPATH::SP) (MYLIFT WF-FR val-fix)))))




;; ;bzo dup?
;; (defun all-non-nil (lst)
;; ;  (declare (xargs :guard t))
;;   (if (set::empty lst)
;;       t
;;     (and (not (null (set::head lst)))
;;          (all-non-nil (set::tail lst)))))

(defthm head-non-nil-when-all-non-nil
  (implies (and (set::all<non-nil> s)
                (not (set::empty s)))
           (set::head s))
  :hints (("Goal" :in-theory (enable))))

(defthm wfr-of-mylift-aux
  (implies (set::all<non-nil> keys)
           (wfr (mylift-aux keys tr)))
  :hints (("Goal" :in-theory (enable wfkey)
           :do-not '(generalize eliminate-destructors))))

(defthm rkeys-of-mylift-aux
  (implies (and (wf-fr tr)
;                (set::all<non-nil> keys)
                (set::setp keys))
           (equal (set::rkeys (mylift-aux keys tr))
                  keys))
  :hints (("Goal" :in-theory (enable SET::EMPTY))))

;;bzo wfkeyed should be rewritten to be more abstract.  just call rkeys and check for nils in the result.

;; (defthm all-non-nil-of-rkeys
;;   (implies (and (wfkeyed tr)
;;                 ;(wfr tr)
;;                 (good-memoryp tr)
;;                 )
;;            (set::all<non-nil> (mem::domain ;rkeys
;;                                tr)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable ;wfr
;;                        wfkeyed wfkey rkeys))))

;trying without...
;; (defthm all-non-nil-of-rkeys2
;;   (implies (wf-fr tr)
;;            (set::all<non-nil> (mem::domain ;RKEYS
;;                                TR)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable wfr WFKEYED))))

(defthm empty-rkeys-when-wfr
  (equal (set::empty (set::rkeys tr))
         (not tr))
  :hints (("Goal" :in-theory (e/d (set::rkeys)
                                  (SET::EMPTY-WHEN-SETP-MEANS-NIL)))))

(local
 (defun ind (keys tr)
   (declare (xargs :verify-guards nil))
   (if (or (not (set::setp keys))
           (set::empty keys))
       (list keys tr)
     (ind (set::tail keys)
          (GACC::MEMORY-CLR (SET::HEAD (mem::domain ;;RKEYS
                                        TR)) tr) ;
    ;(gacc::wr (set::head keys) (gacc::rd (set::head keys) tr) tr)
          ))))

(defthm rkeys-of-memory-clr
  (implies (and ;(rcdp tr) ;; (wfr tr)
                ;(not (ifrp tr))
            (wf-fr tr) ;hope this is okay...
                )
           (equal (mem::domain ;;rkeys
                   (gacc::memory-clr a tr))
                  (if (gacc::wf-usbp8 (mem::load ;g
                                       a tr))
                      (if (cdr (mem::load ;g
                                a tr))
                          (set::insert a (mem::domain ;;rkeys
                                          tr))
                        (set::delete a (mem::domain ;;rkeys
                                        tr)))
                    (mem::domain ;;rkeys
                     tr))))
  :hints (("Goal" :in-theory (e/d (gacc::memory-clr) (WR-OF-0-IS-CLR)))))

;bzo move?
;; (defthm wfr-of-wr
;;   (implies (and (wfr tr)
;;                 (wfkey a))
;;            (wfr (GACC::WR A v TR)))
;;   :hints (("Goal" :in-theory (e/d (GACC::WR) ()))))

;; (defthm wfr-of-memory-clr
;;   (implies (and (wfr tr)
;;                 (wfkey a))
;;            (wfr (gacc::memory-clr a tr)))
;;   :hints (("Goal" :in-theory (e/d (gacc::memory-clr) (wr-of-0-is-clr)))))


(defthm CHECK-FR-KEYS-when-empty
  (implies (SET::EMPTY RKEYS)
           (CHECK-FR-KEYS RKEYS TR))
  :hints (("Goal" :in-theory (enable CHECK-FR-KEYS))))

(defthm not-check-fr-keys-1
  (implies (and (MEM::LOAD (SET::HEAD RKEYS) TR)
                (equal 0 (loghead 8 (car (mem::load (set::head rkeys) tr)))))
           (equal (check-fr-keys rkeys tr)
                  (set::empty rkeys)))
  :otf-flg t
  :hints (("Goal" :use (:instance use-check-fr-keys (keys rkeys) (a (set::head rkeys)) (r tr))
           :in-theory (e/d (;CHECK-FR-KEYS
                            CHECK-FR-KEY
                            ) (use-check-fr-keys)))))

(defthm check-fr-keys-of-memory-clr-irrel
  (implies (and (not (set::in key keys))
                ;(wfr tr)
                (wf-fr tr)
                )
           (equal (check-fr-keys keys (gacc::memory-clr key tr))
                  (check-fr-keys keys tr)))
  :hints (("Goal" :in-theory (e/d (GACC::MEMORY-CLR GACC::WR) (WR-OF-0-IS-CLR))
           :do-not '(generalize eliminate-destructors))))

;; (defthm nil-not-in-key-set-when-wfkeyed
;;   (implies (WFKEYED R)
;;            (not (set::in nil (key-set r))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable key-set wfr wfkeyed wfkey))))

;; (defthm nil-not-in-key-set-when-wfr
;;  (implies (wfr r)
;;           (not (set::in nil (key-set r))))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;           :in-theory (enable key-set wfr wfkeyed wfkey))))

;trying without
;; (defthm wfkey-when-in-rkeys
;;   (implies (and ;(wfr tr)
;;             (wf-fr tr)
;; ;               tr ;
;;                 (set::in key (mem::domain ;rkeys
;;                               tr))
;;                 )
;;            (wfkey key))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (e/d (wfr rkeys wfkey wfkeyed) (NOT-IN-DOMAIN-MEANS-LOAD-IS-NIL2)))))

;skipping for now
;; (defthm wkeys-of-head-of-rkeys
;;   (implies (and ;(wfr tr)
;;             (wf-fr tr)
;;                 ;tr ;need to say something stronger now to imply the domain isn't empty...
;;                 )
;;            (wfkey (set::head (mem::domain ;rkeys
;;                               tr))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (e/d (;wfr rkeys wfkey wfkeyed
;;                        ) (wf-fr)))))

(defthm good-memoryp-of-wr
 (implies (and (good-memoryp tr)
               ;a
               )
          (good-memoryp (gacc::wr a v tr)))
 :hints (("Goal" :in-theory (e/d (gacc::wr) ()))))

(defthm good-memoryp-of-memory-clr
  (implies (and (good-memoryp tr)
                ;a ;drop?
                )
           (good-memoryp (gacc::memory-clr a tr)))
  :hints (("Goal" :in-theory (e/d (gacc::memory-clr) (wr-of-0-is-clr)))))



;; ;Bbzo now gotta show this is preserved...
;; ;show that new satisfies this?
;; (defund good-memoryp2 (mem)
;;   (and (good-memoryp mem)
;;        (equal (signed-byte-p 29 (caddr mem))
;;               (cdar mem))
;;        (equal (MEM::|_LOG2| (+ -1 (CADR mem)))
;;               (CADDR mem))
;;        ))

;moved to records
#+joe
(defthm rkeys-iff-when-wfr
  (iff (set::rkeys r)
       (not (equal r nil)))
  :hints (("Goal" :in-theory (enable rkeys ACL2->RCD))))

;move to fast memory book
;crud.  only true if keys didn't sneak into the wrong part (keys for the memory sneaking into the record or vice versa...)
;crud.  good-memoryp may also have to say that the fast flag is right?
(defthm empty-domain-means
  (implies (and (not (mem::domain fr))
                (good-memoryp fr))
           (equal fr (mem::new (mem::size fr))))
  :otf-flg t
  :hints (("subgoal 2" :in-theory (enable MEM::|_MEMORY-P|
                                          MEM::|_MEMORY-FIX|
                                          MEM::|_MEMORY-SIZE|
                                          MEM::MEMORY-P
                                          MEM::SIZE
                                          GOOD-MEMORYP
                                          MEM::MEM-TREE-DOMAIN
                                          MEM::|_MEMORY-DEPTH|
                                          ))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable ;MEM::|_MEMORY-P|

                       MEM::MEM-TREE-DOMAIN
                       mem::domain
                       mem::new
                       good-memoryp
                       MEM::MEMORY-P
;MEM::SIZE

                       MEM::|_MEMORY-P|
                       MEM::|_MEMORY-FIX|
                       MEM::|_MEMORY-SIZE|
                       MEM::|_MEMORY-DEPTH|
                       MEM::MEMORY-P
                       MEM::SIZE
;                       GOOD-MEMORYP2
                       GOOD-MEMORYP
                       MEM::MEM-TREE-DOMAIN
                       )))
  :rule-classes nil)

;bzo rename?
(defthm size-of-store
  (implies (good-memoryp fr)
           (equal (mem::size (gacc::memory-clr a fr))
                  (mem::size fr)))
  :hints (("Goal" :in-theory (e/d (GACC::MEMORY-CLR
                                   GACC::WR
                                   GOOD-MEMORYP)
                                  (WR-OF-0-IS-CLR)))))

(defthm wf-fr-of-memory-clr
  (implies (and (wf-fr tr)
                ;;a ;that is, a is not nil
                )
           (wf-fr (gacc::memory-clr a tr)))
  :hints (("Goal" :in-theory (e/d (gacc::memory-clr) (;wf-fr-of-wr
                                                      GACC::WF-USBP8
                                                      wr-of-0-is-clr)))))


;; (defthm check-fr-keys-of-memory-clr
;;   (implies (and (wf-fr fr)
;;                 ;(set::in key (mem::domain fr))
;;                 )
;;            (check-fr-keys (mem::domain fr) (gacc::memory-clr key fr)))
;;   :hints (("Goal" :cases ((set::in key (mem::domain fr)))
;;            :use (:instance wf-fr-of-wr
;;                                   (a key)
;;                                   (v 0)
;;                                   (tr fr)
;;                                   )
;;            :in-theory (e/d (gacc::memory-clr) (wf-fr-of-wr
;;                                                GACC::WF-USBP8
;;                                                wr-of-0-is-clr)))))

(defthm domain-not-nil-when-load-not-nil
  (implies (and (mem::load a mem)
                (force (GOOD-MEMORYP MEM)) ;drop?
                )
           (mem::domain mem))
  :hints (("Goal" :in-theory (disable mem::store-of-same-load
                                      MEM::STORE-EQUAL-REWRITE)
           :use (:instance mem::store-of-same-load (mem::mem mem)))))


(defthmd load-iff
  (implies (force (GOOD-MEMORYP MEM)) ;drop?
           (iff (MEM::LOAD a mem)
                (set::in a (mem::domain mem)))))

(defthm load-of-head-of-domain-iff
  (implies (force (GOOD-MEMORYP MEM)) ;drop?
           (iff (mem::load (set::head (mem::domain mem)) mem)
                (not (set::empty (mem::domain mem)))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (load-iff)
                                  ( mem::store-of-same-load
                                    NOT-IN-DOMAIN-MEANS-LOAD-IS-NIL
                                    NOT-IN-DOMAIN-MEANS-LOAD-IS-NIL2
                                    MEM::STORE-EQUAL-REWRITE))
                     ;          :use (:instance mem::store-of-same-load (a (SET::HEAD (MEM::DOMAIN mem))) (mem::mem mem))
           )))


(defthm mypush-aux-of-mylift-aux
  (implies (and (wf-fr fr)
                (equal rkeys (mem::domain ;;rkeys
                              fr)))
           (equal (mypush-aux rkeys
                              (mylift-aux rkeys fr)
                              (mem::size fr)
                              )
                  fr))
  :hints (("subgoal *1/1" :use (:instance empty-domain-means))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d ( ;wfr
                            CHECK-FR-KEY
                            CHECK-FR-KEYS
                            mypush-aux mylift-aux)
                           ( ;gacc::wr==r!
                            ))
           :induct (ind rkeys fr)
           )))

;for dave
(defthm mypush-of-mylift
  (implies (wf-fr tr)
           (equal (mypush (mylift tr) (mem::size tr))
                  tr))
  :hints (("Goal" :in-theory (enable MYPUSH mylift))))

(defthm mypush-of-mylift-matches-better
  (implies (and (acl2::wf-fr tr)
                (equal sz (mem::size tr)))
           (equal (acl2::mypush (acl2::mylift tr) sz)
                  tr))
  :hints (("Goal" :in-theory (enable acl2::mypush acl2::mylift))))

(defun typed-fix-aux (keys r)
  (declare (xargs :verify-guards nil))
  (if (set::empty keys)
      nil ;the empty record
    (s ;mem::store
     (set::head keys)
       (val-fix (g (set::head keys) r))
       (typed-fix-aux (set::tail keys) r))))

;takes a true record and fixes it by dropping all pairs whose value has a
;loghead8 of 0 and chopping the value on all pairs whose value is not a usb8.
(defund typed-fix (r)
  (declare (xargs :verify-guards nil))
  (typed-fix-aux (set::rkeys r) r))


(DEFTHM RKEYS-OF-WR-alt
  (IMPLIES (wf-fr tr)
           (EQUAL (mem::domain ;RKEYS
                   (GACC::WR A V TR))
                  (IF (GACC::WF-USBP8 (mem::load ;G
                                       A TR))
                      (IF (GACC::USBP8-ZP V)
                          (IF (CDR (mem::load ;G
                                    A TR))
                              (SET::INSERT A (mem::domain ;RKEYS
                                              TR))
                              (SET::DELETE A (mem::domain ;RKEYS
                                              TR)))
                          (SET::INSERT A (mem::domain ;RKEYS
                                          TR)))
                      (IF (GACC::USBP8-ZP V)
                          (mem::domain ; RKEYS
                           TR)
                          (SET::INSERT A (mem::domain ;RKEYS
                                          TR))))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (GACC::WR GACC::MEMORY-CLR) (WR-OF-0-IS-CLR)))))


;; (DEFTHM WFR-OF-WR-strong
;;   (IMPLIES (WFR TR)
;;            (equal (WFR (GACC::WR A V TR))
;;                   (WFKEY A)))
;;   :HINTS (("Goal" :IN-THEORY (E/D (wfkey) NIL))))



(local
 (defun ind3 (keys r)
   (declare (xargs :verify-guards nil))
   (if (or (not (set::setp keys))
           (set::empty keys))
       (list keys r)
     (ind3 (set::tail keys)
           (CLR (SET::HEAD (SET::RKEYS R)) r) ;
    ;(gacc::wr (set::head keys) (gacc::rd (set::head keys) tr) tr)
           ))))

(defthmd g-when-not-g-of-cdr
  (implies (and (not (g key (cdr r)))
                (wfr r)
                )
           (equal (g key r)
                  (if (equal key (caar r))
                      (cdar r)
                    nil)))
  :hints (("Goal" :in-theory (enable g)
           :do-not '(generalize eliminate-destructors))))

;could improve other lemmas (e.g., lemmas above this and the analogue of this in tr-path-connection) using a similar hint?
(defthm g-when-not-in-rkeys
  (implies (not (set::in key (set::rkeys r)))
           (equal (g key r)
                  nil))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :use (:instance S-SAME-G (a key))
           :in-theory (e/d ( ) (S-SAME-G S==R EQUAL-S-RECORD-EQUALITY)))))

(defthm clr-of-typed-fix-aux-irrel
  (implies (not (set::in key keys))
           (equal (clr
                   key (TYPED-FIX-AUX keys R))
                  (TYPED-FIX-AUX keys (clr key r))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm good-memoryp-of-mypush-aux
  (implies (posp size)
           (good-memoryp (mypush-aux keys r size))))

(defthm not-in-of-rkeys-of-mypush-aux
  (implies (and (NOT (SET::IN key keys))
;                (set::all<non-nil> keys) ;drop?
                (posp size)
                (wfr r))
           (NOT (SET::IN key (mem::domain ;RKEYS
                              (MYPUSH-AUX keys R size)))))
  :hints (("Goal" :in-theory (e/d (GACC::WR)
                                  (  ;disables for efficiency -why are things suddenyl so slow?
;                                           G-OF-MYPUSH-AUX-WHEN-NOT-IN-KEYS
                                           ))
           :do-not '(generalize eliminate-destructors))))


;bzo rename stuff like this...
(defthm g-of-mypush-aux-when-not-in-keys
  (implies (not (set::in key keys))
           (equal (mem::load ;g
                   key (mypush-aux keys r size))
                  nil))
  :hints (("Goal" :in-theory (e/d (GACC::WR)
                                  (NOT-IN-DOMAIN-MEANS-LOAD-IS-NIL
                                   NOT-CHECK-FR-KEYS-1))
           :do-not '(generalize eliminate-destructors))))

(local (in-theory (disable SET::SUBSET))) ;bzo make non-local?
(local (in-theory (disable SET::DELETE)))

;moved to records
#+joe
(defthm nil-not-in-keys
  (implies (wfkeyed tr)
           (not (bag::memberp nil (alist::keys tr))))
  :hints (("Goal" :in-theory (enable wfkeyed alist::keys))))

;moved to records?
#+joe
(defthm all-non-nil-of-rkeys
  (implies (wfr tr)
           (set::all<non-nil> (set::rkeys TR)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable set::rkeys rkeys wfr))))

(defthm domain-of-mypush-aux-subset
  (implies (posp size)
           (set::subset (mem::domain (mypush-aux keys r size))
                        (set::intersect keys (set::rkeys r))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable ;SET::SUBSET
                       SET::PICK-A-POINT-SUBSET-STRATEGY
                       ))))

(defthm mylift-of-mypush-helper
  (implies (and; (wfr r)
;                (set::all<non-nil> keys) ;drop?
                (posp size)
                (equal keys (set::rkeys r)))
           (equal (mylift-aux (mem::domain ;rkeys
                               (mypush-aux keys r size))
                              (mypush-aux keys r size))
                  (typed-fix-aux keys r)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (disable SET::IN
                               G-WHEN-NOT-IN-RKEYS
                               SET::ALL<NON-NIL>
                               SET::ALL<NOT-NON-NIL>
                               )
           :induct (ind3 keys r)
           )))

(defthm mylift-of-mypush
  (implies (posp size)
           (equal (mylift (mypush r size))
                  (typed-fix r)))
  :hints (("Goal" :in-theory (enable mypush mylift TYPED-FIX))))

;bzo rename?
(defun all-vals-okay-aux (keys r)
  (declare (xargs :verify-guards nil))
  (if (set::empty keys)
      t
    (and (unsigned-byte-p 8(g (set::head keys) r))
         (not (equal 0 (g (set::head keys) r)))
         (all-vals-okay-aux (set::tail keys) r))))

(defthm all-vals-okay-aux-of-clr-irrel
  (implies (not (set::in key keys))
           (equal (all-vals-okay-aux keys (clr key r))
                  (all-vals-okay-aux keys r)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;          :induct (ind3 keys r)
           )))

(defthm typed-fix-does-nothing-helper
  (implies (and (all-vals-okay-aux keys r)
                (equal keys (set::rkeys r))
                (wfr r)
                )
           (equal (typed-fix r)
                  r))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable TYPED-FIX)
           :induct (ind3 keys r))))

;;bzo Dave, what do we want to call this?
(defund well-typed-record (r)
  (declare (xargs :verify-guards nil))
  (and (wfr r)
       (all-vals-okay-aux (set::rkeys r) r)))

;for Dave
;bzo is this stuff common to both tr- and fr-?
(defthm typed-fix-does-nothing
  (implies (well-typed-record r)
           (equal (typed-fix r)
                  r))
  :hints (("Goal" :in-theory (enable typed-fix well-typed-record)
           :do-not '(generalize eliminate-destructors))))

(defthm good-memoryp-implies-non-nil-hack
  (implies (not x)
           (not (acl2::good-memoryp x))))

(defthm wr-non-nil-when-good-memoryp
  (implies (acl2::good-memoryp m)
           (GACC::WR a v m))
  :otf-flg t
  :hints (("Goal"
           :use ((:instance acl2::good-memoryp-of-store
                            (acl2::a a)
                            (acl2::v (CDR (MEM::LOAD A M)))
                            (acl2::mem m))
                 (:instance acl2::good-memoryp-of-store
                            (acl2::a a)
                            (acl2::v (CONS (ACL2::LOGHEAD 8 V)
                                           (MEM::LOAD A M)))
                            (acl2::mem m))
                 (:instance acl2::good-memoryp-of-store
                            (acl2::a a)
                            (acl2::v (CONS (ACL2::LOGHEAD 8 V)
                                           (CDR (MEM::LOAD A M))))
                            (acl2::mem m)))

           :in-theory (e/d (GACC::WR) (acl2::good-memoryp-of-store)))))
;; (thm
;;  (ACL2::MYPUSH-AUX keys (set::rkeys r) size))

;; (thm
;;  (iff (ACL2::MYPUSH r size)
;;       t)
;;  :hints (("Goal" :in-theory (enable ACL2::MYPUSH))))

(defthm acl2::good-memoryp-of-mypush
  (implies (posp acl2::size) ;drop?
           (acl2::good-memoryp (acl2::mypush acl2::r acl2::size)))
  :hints (("Goal" :in-theory (enable acl2::mypush))))

(defthm mypush-non-nil
  (implies (posp acl2::size)
           (acl2::mypush acl2::r acl2::size))
  :rule-classes (:rewrite :type-prescription) ;is t-p smart enough to know about posp?
  :hints (("Goal" :use (:instance acl2::good-memoryp-of-mypush)
           :in-theory (disable acl2::good-memoryp-of-mypush))))

(defthm domain-of-memory-clr
  (implies (good-memoryp m)
           (equal (mem::domain (gacc::memory-clr a m))
                  (IF (GACC::WF-USBP8 (MEM::LOAD A m))
                      (IF (CDR (MEM::LOAD A m))
                          (SET::INSERT A (MEM::DOMAIN m))
                          (SET::DELETE A (MEM::DOMAIN m)))
                      (MEM::DOMAIN m))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (mem::clear gacc::memory-clr) (wr-of-0-is-clr)))))

(defthm rd-of-clear
  (equal (gacc::rd key1 (mem::clear key2 m))
         (if (equal key1 key2)
             0
           (gacc::rd key1 m)))
  :hints (("Goal" :in-theory (enable gacc::rd))))

(defthm mylift-aux-of-clear-irrel
  (implies (not (set::in key keys))
           (equal (mylift-aux keys (mem::clear key m))
                  (mylift-aux keys m)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable ))))

(defthm clr-of-mylift
  (implies (good-memoryp m)
           (equal (clr key (acl2::mylift m))
                  (acl2::mylift ( ;gacc::memory-clr
                                 mem::clear
                                 key m))))
  :hints (("Goal" :in-theory (enable acl2::mylift))))

(defthm clear-of-wr
  (equal (mem::clear a (gacc::wr a v r))
         (mem::clear a r))
  :hints (("Goal" :in-theory (enable gacc::wr))))

(defthm clear-of-wr-diff
  (implies (not (equal a b))
           (equal (mem::clear a (gacc::wr b v r))
                  (gacc::wr b v (mem::clear a r))))
  :hints (("Goal" :in-theory (enable gacc::wr))))

(defthm clear-of-wr-both
  (equal (mem::clear a (gacc::wr b v r))
         (if (equal a b)
             (mem::clear a r)
           (gacc::wr b v (mem::clear a r))))
  :hints (("Goal" :in-theory (enable gacc::wr))))


;bzo move to memory
(defthm clear-of-new
  (equal (mem::clear key (mem::new size))
         (mem::new size))
  :hints (("Goal" :in-theory (enable mem::clear))))

(defthm clear-of-mypush-aux-irrel
  (implies (not (set::in key keys))
           (equal (MEM::CLEAR key (ACL2::MYPUSH-AUX keys R SIZE))
                  (ACL2::MYPUSH-AUX keys R SIZE))))

(defthm clear-of-mypush-aux
  (equal (MEM::CLEAR KEY (ACL2::MYPUSH-AUX keys R SIZE))
         (ACL2::MYPUSH-AUX keys (acl2::clr key R) SIZE))
  :hints (("Goal" :in-theory (enable set::delete))))

(defthm clear-of-mypush
  (implies (posp size)
           (equal (mem::clear key (acl2::mypush r size))
                  (acl2::mypush (acl2::clr key r) size)))
  :hints (("Goal" :in-theory (enable acl2::mypush))))

;; see proof in shell
(defthm all-vals-okay-aux-of-delete
  (implies (acl2::all-vals-okay-aux keys m)
           (acl2::all-vals-okay-aux (set::delete key keys) m))
  :hints (("Goal" :in-theory (enable set::delete))))

;bzo same for s?
(defthm well-typed-record-of-clr
  (implies (acl2::well-typed-record m)
           (acl2::well-typed-record (acl2::clr key m)))
  :hints (("Goal" :in-theory (e/d (acl2::well-typed-record) (;clrp-singleton-back
                                                             )))))
(in-theory (disable WF-FR))

(defthm wf-fr-of-new
  (implies (posp size)
           (wf-fr (mem::new size)))
  :hints (("Goal" :in-theory (enable wf-fr))))

(defthm wf-fr-of-mypush-aux
  (implies (posp size)
           (wf-fr (mypush-aux keys2 r size)))
  :hints (("Goal" :in-theory (enable check-fr-keys))))

(defthm wf-fr-of-mypush
  (implies (posp size)
           (wf-fr (mypush r size)))
  :hints (("Goal" :use (:instance wf-fr-of-MYPUSH-AUX (keys2 (set::rkeys R)))
           :in-theory (e/d (mypush wf-fr) (wf-fr-of-MYPUSH-AUX)))))

;bzo or put this elsewhere and don't include paths for this book (there's not much pathy stuff here?)
(defthm gp-of-mylift-singleton
  (equal (cpath::gp (list a) (acl2::mylift tr))
         (if (set::in a (mem::domain tr))
             (acl2::loghead 8 (gacc::rd a tr))
           nil))
  :hints (("Goal" :in-theory (enable cpath::gp))))

;bzo same for sp?
(defthm well-typed-record-of-clrp-singleton
  (implies (acl2::well-typed-record m)
           (acl2::well-typed-record (cpath::clrp (list key) m)))
  :hints (("Goal" :in-theory (e/d (cpath::clrp-singleton-becomes-clr)
                                  (cpath::clr-becomes-clrp-singleton
                                   )))))

(defthm clrp-of-mylift-singleton
  (implies (acl2::good-memoryp m)
           (equal (cpath::clrp (list key) (acl2::mylift m))
                  (acl2::mylift (mem::clear key m))))
  :hints (("Goal" :in-theory (e/d (cpath::clrp-singleton-becomes-clr)
                                  (cpath::SP==R ;bzo looped
                                   cpath::clr-becomes-clrp-singleton)))))

(defthm use-check-fr-keys-8
  (implies (and (acl2::check-fr-keys keys tr)
                (set::in a keys)
                (mem::load a tr)
                )
           (acl2::unsigned-byte-p 8 (car (mem::load a tr))))
  :hints (("Goal" :in-theory (enable acl2::check-fr-keys
                                     acl2::check-fr-key))))

(defthm use-check-fr-keys-9
  (implies (and (acl2::check-fr-keys keys tr)
                (set::in a keys)
                (mem::load a tr)
                )
           (NOT (GACC::USBP8-ZP (CAR (MEM::LOAD A TR)))))
  :hints (("Goal" :in-theory (enable acl2::check-fr-keys
                                     GACC::USBP8-ZP
                                     acl2::check-fr-key))))

(defthm use-check-fr-keys-10
  (implies (and (acl2::check-fr-keys keys tr)
                (set::in a keys)
                (mem::load a tr)
                )
           (NOT (equal 0 (CAR (MEM::LOAD A TR)))))
  :hints (("Goal" :in-theory (enable acl2::check-fr-keys
                                     GACC::USBP8-ZP
                                     acl2::check-fr-key))))

;disable? ;move?
(defthm rd-not-equal-0-helper
  (implies (and (acl2::wf-fr tr)
                (set::in a (mem::domain tr)))
           (not (equal 0 (gacc::rd a tr))))
  :hints (("Goal" :cases ((set::in a  (mem::domain tr)))
           :in-theory (enable gacc::rd acl2::wf-fr))))

;move?
(defthm rd-is-0
  (implies (and (not (set::in a (mem::domain tr)))
                (acl2::good-memoryp tr))
           (equal (gacc::rd a tr) 0))
  :hints (("Goal" :in-theory (enable gacc::rd acl2::not-in-domain-means-load-is-nil))))

(defthm wf-fr-implies-good-memoryp
  (implies (acl2::wf-fr tr)
           (acl2::good-memoryp tr))
  :hints (("Goal" :in-theory (enable acl2::wf-fr))))

;better version - kill the other?

(defthm g-of-mylift-2
  (implies (acl2::wf-fr tr)
           (equal (g a (acl2::mylift tr))
                  (acl2::val-fix (acl2::loghead 8 (gacc::rd a tr)))))
  :hints (("Goal" :in-theory (enable ACL2::NOT-IN-DOMAIN-MEANS-LOAD-IS-NIL))))

(in-theory (disable acl2::g-of-mylift))
(in-theory (disable acl2::val-fix))



;will this defeat the purpose of keeping val-fix closed?
(defthm val-fix-iff
  (iff (acl2::val-fix v)
       (not (equal 0 (acl2::loghead 8 v))))
  :hints (("Goal" :in-theory (enable acl2::val-fix))))


;bzo replace the other!
(defthm acl2::rd-of-mypush-better
  (equal (gacc::rd acl2::a (acl2::mypush acl2::r acl2::size))
         (acl2::loghead 8 (g acl2::a acl2::r)))
  :hints (("Goal" :in-theory (enable acl2::mypush))))

(in-theory (disable acl2::rd-of-mypush))

;bzo replace the other!
(defthm acl2::rkeys-of-wr-alt-2
  (implies (acl2::wf-fr acl2::tr)
           (equal (mem::domain (gacc::wr acl2::a acl2::v acl2::tr))
                  (if (gacc::usbp8-zp acl2::v)
                      (set::delete acl2::a (mem::domain acl2::tr))
                    (set::insert acl2::a (mem::domain acl2::tr)))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (gacc::wr gacc::memory-clr
                                            ACL2::WF-FR
                                            )
                                  (acl2::wr-of-0-is-clr)))))

(in-theory (disable acl2::rkeys-of-wr-alt))

(defthm wf-usbp8-of-load
  (implies (acl2::wf-fr acl2::m)
           (iff (gacc::wf-usbp8 (mem::load acl2::key acl2::m))
                (mem::load acl2::key acl2::m)))
  :hints (("Goal" :in-theory (enable acl2::wf-fr))))

(defthm use-check-fr-keys-another
  (implies (and (set::in acl2::key keys)
                (acl2::check-fr-keys keys acl2::m))
           (not (cdr (mem::load acl2::key acl2::m))))
  :hints (("Goal" :in-theory (enable acl2::check-fr-keys))))

(defthm not-cdr-load
 (implies (ACL2::WF-FR ACL2::M)
          (not (CDR (MEM::LOAD ACL2::KEY ACL2::M))))
 :hints (("Goal" :cases ((set::in ACL2::KEY (MEM::DOMAIN ACL2::M)))
          :use (:instance use-check-fr-keys-another
                          (keys (MEM::DOMAIN ACL2::M))
                          )
          :in-theory (e/d (ACL2::WF-FR ACL2::CHECK-FR-KEYS) (use-check-fr-keys-another)))))

;bzo replace the other?
(defthm acl2::clr-of-mylift-better
  (implies ;(acl2::good-memoryp acl2::m)
   (acl2::wf-fr acl2::m)
           (equal (acl2::clr acl2::key (acl2::mylift acl2::m))
                  (acl2::mylift (gacc::memory-clr acl2::key acl2::m))))
  :otf-flg t
  :hints (("Goal" :cases ((SET::in ACL2::KEY (MEM::DOMAIN ACL2::M)))
           :use (:instance acl2::mylift-irrel
                           (acl2::key ACL2::KEY)
                           (acl2::keys (MEM::DOMAIN ACL2::M))
                           (acl2::tr acl2::m))

           :in-theory (e/d (acl2::mylift) (acl2::mylift-irrel)))))

(in-theory (disable acl2::clr-of-mylift))

(defthm memory-clr-of-mypush
  (equal (gacc::memory-clr key (acl2::mypush r size))
         (acl2::mypush (acl2::clr key r) size))
  :hints (("Goal" :in-theory (enable acl2::mypush)
           :do-not '(generalize eliminate-destructors))))

(local (in-theory (disable MAX-OFFSET)))

;for efficiency:
;(local (in-theory (disable BAG::DISJOINT-APPEND-REDUCTION)))

(in-theory (disable
            (:REWRITE DEFAULT-<-2)
            (:REWRITE DEFAULT-<-1)
            (:REWRITE DEFAULT-+-2)
            (:REWRITE DEFAULT-+-1)
;            (:rewrite z*-wx-introduction)
            ))

; the next 4 events copied to gacc2, since this book is being deprecated (don't keep both copies forever).
(defun syntax-consp-or-quote (skel)
  (declare (type t skel))
  (or (quotep skel)
      (and (consp skel)
           (equal (car skel) 'cons))))

(defun syntax-consp-or-symbol (skel)
  (declare (type t skel))
  (or (symbolp skel)
      (and (consp skel)
           (or (equal (car skel) 'cons)
               (and (equal (car skel) 'quote)
                    (consp (cdr skel))
                    (not (null (cadr skel))))))))


(defun syntax-atom (m)
  (declare (type t m))
  (or (symbolp m)
      (quotep m)))




;;;
;;; Type reasoning
;;;

;bzo
(defthm integerp-+
  (implies
   (and
    (integerp x)
    (integerp y))
   (integerp (+ x y))))

;bzo
(defthm integerp-implies-common-types
  (implies (integerp x)
           (and (rationalp x)
                (acl2-numberp x))))

(defun anything (x)
  (declare (type t x)
           (ignore x))bzo)

;bzo
(defun non-negative-integerp (n)
  (declare (type t n))
  (and (integerp n)
       (<= 0 n)))

(defthm non-negative-integerp-implies
  (implies (non-negative-integerp n)
           (and (integerp n)
                (<= 0 n)))
  :rule-classes (:forward-chaining))

(defthm implies-non-negative-integerp
  (implies (and (integerp n)
                (<= 0 n))
           (non-negative-integerp n)))

(in-theory (disable non-negative-integerp))

(defun positive-integerp (n)
  (declare (type t n))
  (and (integerp n)
       (< 0 n)))

(defthm positive-integerp-implies
  (implies (positive-integerp n)
           (and (integerp n)
                (< 0 n)))
  :rule-classes (:forward-chaining))

(defthm implies-positive-integerp
  (implies (and (integerp n)
                (< 0 n))
           (positive-integerp n)))

;;
;; weak-skel
;;

(defun weak-skel (skel)
  (declare (type t skel))
  (if (consp skel)
      (let ((entry (car skel)))
        (and (skel-entry-body entry (acl2::unsigned-byte-p (fix-size size) ;wintn 8 size
                                                           ptr) (weak-skel type))
             (weak-skel (cdr skel))))
    (null skel)))

(defthm weak-skel-implies-true-listp
  (implies
   (weak-skel skel)
   (true-listp skel))
  :rule-classes (:forward-chaining))

(defthm open-weak-skel
  (implies (and (syntaxp (symbolp skel))
                (consp skel))
           (equal (weak-skel skel)
                  (let ((entry (car skel)))
                    (and (skel-entry-body entry (acl2::unsigned-byte-p (fix-size size) ;wintn 8 size
                                                                       ptr) (weak-skel type))
                         (weak-skel (cdr skel)))))))


;;
;; Here we begin to introduce a weak notion of collect .. one that
;; collects only the "active" regions of the block.
;;

(defund blks (skel)
  (declare (type (satisfies weak-skel) skel))
  (if (consp skel)
      (let ((entry (car skel)))
        (let ((ptr   (cadr entry))
              (index (caddr entry))
              (size  (cadddr entry)))
          (let ((blk (blk (+ (ifix ptr) index) (1+ (max-offset size)))))
            (append blk (blks (cdr skel))))))
    nil))

(defthm blks-of-cons
  (equal (blks (cons a skel))
         (append  (BLK (+ (IFIX (CADR a)) (CADDR a))
                       (1+ (MAX-OFFSET (CADDDR a))))
                  (blks skel)))
  :hints (("Goal" :in-theory (e/d (blks) (ifix)))))

(defthm blks-when-skel-is-not-a-consp
  (implies (not (consp skel))
           (not (blks skel)))
  :hints (("Goal" :in-theory (enable blks))))


(defthmd open-blks
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol skel))
     (consp skel))
    (equal (blks skel)
           (LET ((ENTRY (CAR SKEL)))
                (LET ((PTR (CADR ENTRY))
                      (INDEX (CADDR ENTRY))
                      (SIZE (CADDDR ENTRY)))
                     (LET ((BLK (BLK (+ (IFIX PTR) INDEX)
                                     (1+ (MAX-OFFSET SIZE)))))
                          (APPEND BLK (BLKS (CDR SKEL))))))))
   (implies
    (and
     (syntaxp (syntax-atom skel))
     (not (consp skel)))
    (equal (blks skel) nil)))
  :hints (("Goal" :in-theory (enable blks))))

(defthm true-listp-blks
  (true-listp (blks skel)))

(defthm blks-append
  (equal (blks (append x y))
         (append (blks x)
                 (blks y)))
  :hints (("Goal" :in-theory (enable blks append))))

;(local (in-theory (enable append))) ;yuck.

;; Does this really improve performance?
;;
(in-theory (disable (:TYPE-PRESCRIPTION BLKS)))

(defund mesh (skel)
  (declare (type (satisfies weak-skel) skel)
           ;(xargs :verify-guards nil)
           )
  (if (consp skel)
      (let ((entry (car skel)))
        (let ((type (cadddddr entry))) ; type
          (append (blks type)
                  (mesh type)
                  (mesh (cdr skel)))))
    nil))

(defthm mesh-of-cons
  (equal (mesh (cons entry skel))
         (APPEND (BLKS (CADDDDDR ENTRY))
                 (MESH (CADDDDDR ENTRY))
                 (MESH SKEL)))
  :hints (("Goal" :in-theory (enable mesh))))

(defthm mesh-when-skel-is-not-a-consp
  (implies (not (consp skel))
           (not (mesh skel)))
  :hints (("Goal" :in-theory (enable mesh))))

(defthmd open-mesh
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol skel))
     (consp skel))
    (equal (mesh skel)
           (LET ((ENTRY (CAR SKEL)))
                (LET ((TYPE (CADDDDDR ENTRY)))
                     (APPEND (BLKS TYPE)
                             (MESH TYPE)
                             (MESH (CDR SKEL)))))))
   (implies
    (and
     (syntaxp (syntax-atom skel))
     (not (consp skel)))
    (equal (mesh skel) nil)))
  :hints (("Goal" :in-theory (enable mesh))))

(defthm true-listp-mesh
  (true-listp (mesh skel)))

(defthm mesh-append
  (equal (mesh (append x y))
         (append (mesh x)
                 (mesh y)))
  :hints (("Goal" :in-theory (enable mesh))))

(in-theory (disable (:TYPE-PRESCRIPTION MESH)))

(defun flatten (skel)
  (declare (type (satisfies weak-skel) skel))
  (append (blks skel) (mesh skel)))

;;
;; wf-skel
;;

(defun uniform-base (skel)
  (declare (type (satisfies weak-skel) skel))
  (if (consp skel)
      (let ((entry1 (car skel)))
        (let ((base1 (cadr entry1)))
          (if (consp (cdr skel))
              (let ((entry2 (car (cdr skel))))
                (let ((base2 (cadr entry2)))
                  (and (equal base1 base2)
                       (uniform-base (cdr skel)))))
            t)))
    t))

(defun wf-skel (skel)
  (declare (type (satisfies weak-skel) skel))
  (if (consp skel)
      (let ((entry (car skel)))
        (and (skel-entry-body entry
                              (wf-skel type)
                              (acl2::unsigned-byte-p (fix-size size) ptr) ;(wintn 8 size ptr)
                              (unique (blks type))
                              (uniform-base type)
                              )
             (wf-skel (cdr skel))))
    (null skel)))

(defthm open-wf-skel
  (implies (and (syntaxp (syntax-consp-or-symbol skel))
                (consp skel))
           (equal (wf-skel skel)
                  (let ((entry (car skel)))
                    (and (skel-entry-body entry
                                          (wf-skel type)
                                          (acl2::unsigned-byte-p (fix-size size) ptr) ;(wintn 8 size ptr)
                                          (unique (blks type))
                                          (uniform-base type)
                                          )
                         (wf-skel (cdr skel)))))))

(defthm wf-skel-implies-weak-skel
  (implies (wf-skel skel)
           (weak-skel skel))
  :rule-classes (:forward-chaining))

;;
;; size-rec
;;

(defun size-rec (max skel)
  (declare (type integer max)
           (type (satisfies weak-skel) skel))
  (if (consp skel)
      (let ((entry (car skel)))
        (let ((indx (caddr entry))
              (size (cadddr  entry)))
          (let ((max (max (nfix max) (+ 1 (nfix indx) (max-offset size)))))
            (size-rec max (cdr skel)))))
    (nfix max)))

(defthm open-size-rec
  (and
   (implies
    (consp skel)
    (equal (size-rec max skel)
           (let ((entry (car skel)))
             (let ((indx (caddr entry))
                   (size (cadddr  entry)))
               (let ((max (max (nfix max) (+ 1 (nfix indx) (max-offset size)))))
                 (size-rec max (cdr skel)))))))
   (implies
    (null skel)
    (equal (size-rec max skel) (nfix max)))))

(defthm non-negative-integerp-size-rec
  (and
   (non-negative-integerp (size-rec max skel))
   (integerp (size-rec max skel))
   (<= 0 (size-rec max skel))))

(defthm rmax-bound-rewrite
  (implies
   (and
    (<= (size-rec max1 skel) rmax)
    (< (+ index (max-offset size)) (nfix max1)))
   (< (+ index (max-offset size)) rmax))
  :hints (("goal" :induct (size-rec max1 skel))))

(defthm size-rec-relation
  (implies
   (and
    (< rmax (size-rec max0 skel))
    (<= (size-rec max1 skel) rmax)
    (< (nfix max0) (nfix max1)))
   nil)
  :rule-classes (:forward-chaining))

(defthm size-rec-skel-prop
  (implies
   (wf-skel skel)
   (and
    (implies
     (< n (nfix max))
     (< n (size-rec max skel)))
    (implies
     (<= n (nfix max))
     (<= n (size-rec max skel)))))
  :hints (("goal" :induct (size-rec max skel))))


(defthm size-rec-relativity
  (implies
   (<= (nfix n1) (nfix n2))
   (<= (size-rec n1 skel) (size-rec n2 skel))))

;;
;; size
;;

(defun size (skel)
  (declare (type (satisfies weak-skel) skel))
  (size-rec 0 skel))

(defthm non-negative-integerp-size
  (non-negative-integerp (size skel)))

;;
;;
;; x* is a RAM _independent_ skeleton extraction function. I'm not
;; exactly sure how we would use this one .. perhaps if we had a
;; structure that was difficult to describe using g*, we would hand x*
;; a skeleton constructed in some other way.  Of course, this would
;; lead to problems when the constructor function was composed over
;; other functions that used g* .. hmm.
;;
;; Actually, I think we want to use x* in the following manner ..
;;
;; (x* ptr (g* ptr dtype ram) (fn ram))
;;
;; x* allows us to extract the functionality of fn as it applies to
;; the original structure (g* ..).
;;

(defun x* (skel ram)
  (declare (type (satisfies weak-skel) skel)
           (xargs :measure (acl2-count skel)
                  :guard-hints (("goal" :expand (wf-skel skel)))))
  (if (consp skel)
      (let ((entry (car skel)))
        (let ((akey (car entry))       ; abstract key
              (base (cadr entry))
              (indx (caddr entry))      ; index
              (size (cadddr entry))     ; size
              ;(ptr  (caddddr entry))   ; pointer
              (type (cadddddr entry)))  ; type
          (let ((valu (rx size (+ indx base) ram)))
            (let ((type (x* type ram)))
              (cons `(,akey ,base ,indx ,size ,valu ,type)
                    (x* (cdr skel) ram))))))
    nil))

(defthm open-x*
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol skel))
     (consp skel))
    (equal (x* skel ram)
           (let ((entry (car skel)))
             (let ((akey (car entry))       ; abstract key
                   (base (cadr entry))
                   (indx (caddr entry))      ; index
                   (size (cadddr entry))     ; size
                   (type (cadddddr entry)))  ; type
               (let ((valu (rx size (+ indx base) ram)))
                 (let ((type (x* type ram)))
                   (cons `(,akey ,base ,indx ,size ,valu ,type)
                         (x* (cdr skel) ram))))))))
   (implies
    (and
     (syntaxp (syntax-atom skel))
     (not (consp skel)))
    (equal (x* skel ram) nil))))

(defthm size-rec-x*
  (equal (size-rec min (x* skel ram))
         (size-rec min skel)))

(defthm size-x*
  (equal (size (x* skel ram))
         (size skel))
  :hints (("goal" :in-theory (enable size))))

(defthm blks-x*-reduction
  (equal (blks (x* rskel ram))
         (blks rskel)))

(defthm base-x*
  (implies
   (consp skel)
   (equal (cadar (x* skel ram))
          (cadar skel))))

(defthm uniform-base-x*
  (implies
   (uniform-base skel)
   (uniform-base (x* skel ram)))
  :hints (("goal" :induct (uniform-base skel))))

(defthm wf-skel-x*
  (implies
   (wf-skel skel)
   (wf-skel (x* skel ram))))

(defun relocate-block (rptr rskel)
  (declare (type (satisfies weak-skel) rskel))
  (if (consp rskel)
      (let ((entry (car rskel)))
        (let ((akey (car entry))        ; abstract key
              (indx (caddr entry))      ; index
              (size (cadddr entry))     ; size
              (valu (caddddr entry))    ; pointer/value
              (type (cadddddr entry)))  ; type
          (cons `(,akey ,rptr ,indx ,size ,valu ,type)
                (relocate-block rptr (cdr rskel)))))
    nil))

(defthm base-relocate-block
  (implies
   (consp rskel)
   (equal (cadar (relocate-block rptr rskel))
          rptr)))

(defthm consp-relocate-block
  (implies
   (consp (relocate-block rptr rskel))
   (consp rskel))
  :rule-classes (:forward-chaining))

(defthm uniform-base-relocate-block
  (uniform-base (relocate-block rptr rskel)))

;;
;;
;; g* is a RAM dependent skeleton extraction function
;;
;;

(defun g* (base skel ram)
  (declare (type (satisfies weak-skel) skel)
           (type (satisfies integerp) base)
           (xargs :measure (acl2-count skel)
                  :guard-hints (("goal" :expand (wf-skel skel)))))
  (let ((base (ifix base)))
    (if (and (consp skel) (not (zerop base)))
        (let ((entry (car skel)))
          (let ((akey (car entry))       ; abstract key
                (indx (caddr entry))      ; index
                (size (cadddr entry))     ; size
                ;(ptr  (caddddr entry))   ; pointer
                (type (cadddddr entry)))   ; type
            (let ((valu (rx size (+ indx base) ram)))
              (let ((type (g* valu type ram)))
                (cons `(,akey ,base ,indx ,size ,valu ,type)
                      (g* base (cdr skel) ram))))))
      nil)))

#|   now takes 3 args...
(defun g*-list (skel ram)
  (declare (type (satisfies weak-skel) skel))
  (if (consp skel)
      (let ((entry (car skel)))
        (let ((akey (car entry))       ; abstract key
              (base (cadr entry))
              (indx (caddr entry))      ; index
              (size (cadddr entry))     ; size
              ;(ptr  (caddddr entry))   ; pointer
              (type (cadddddr entry)))  ; type
          (let ((valu (rx size (+ indx base) ram)))
            (let ((type (g* valu type ram)))
              (cons `(,akey ,base ,indx ,size ,valu ,type)
                    (g*-list (cdr skel) ram))))))
    nil))
|#

(defthm open-g*
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol skel))
     (consp skel))
    (equal (g* base skel ram)
           (let ((base (ifix base)))
             (if (zerop base) nil
               (let ((entry (car skel)))
                 (let ((akey (car entry))       ; abstract key
                       (indx (caddr entry))      ; index
                       (size (cadddr entry))     ; size
                       (type (cadddddr entry)))   ; type
                   (let ((valu (rx size (+ indx base) ram)))
                     (let ((type (g* valu type ram)))
                       (cons `(,akey ,base ,indx ,size ,valu ,type)
                             (g* base (cdr skel) ram))))))))))
   (implies
    (and
     (syntaxp (syntax-atom skel))
     (not (consp skel)))
    (equal (g* base skel ram) nil))
   (implies
    (and
     (syntaxp (syntax-atom base))
     (zerop base))
    (equal (g* base skel ram) nil))))

(defthm size-rec-g*-casesplit
  (equal (size-rec min (g* base skel ram))
         (if (zerop (ifix base)) (nfix min)
           (size-rec min skel))))

(defthm size-g*-casesplit
  (equal (size (g* base skel ram))
         (if (zerop (ifix base)) 0 (size skel)))
  :hints (("goal" :in-theory (enable size))))


(defthm blks-g*-reduction-casesplit
  (equal (blks (g* rptr rskel ram))
         (if (zerop (ifix rptr)) nil (blks (relocate-block rptr rskel)))))

(defthm base-g*
  (implies
   (and
    (consp rskel)
    (not (zerop (ifix rptr))))
   (equal (cadar (g* rptr rskel ram))
          (ifix rptr))))

(defthm consp-g*-forward
  (implies
   (consp (g* ptr skel ram))
   (and
    (not (zerop (ifix ptr)))
    (consp skel)))
  :rule-classes (:forward-chaining))

(defthm uniform-base-g*
  (uniform-base (g* rptr rskel ram)))

;;
;;
;; A little ground work on blks ..
;;
;;

(defun blks-ptr (ptr skel)
  (declare (type (satisfies weak-skel) skel)
           (type integer ptr))
  (if (consp skel)
      (let ((entry (car skel)))
        (let (;(ptr   (cadr entry))
              (index (caddr entry))
              (size  (cadddr entry)))
          (let ((blk (blk (+ (ifix ptr) index) (1+ (max-offset size)))))
            (append blk (blks-ptr ptr (cdr skel))))))
    nil))

(defthm uniform-base-blks-transformation
  (implies
   (uniform-base skel)
   (equal (blks skel)
          (blks-ptr (cadar skel) skel))))

;These next three just not true unless we're dealing with integers
(defthm disjoint-blk-ptr-blks-ptr-independent-of-ptr
  (implies
   (and
    (disjoint (blks-ptr ptr1 skel)
              (blk (+ ptr1 x) size))
    (wf-skel skel)
    (integerp ptr1)
    (integerp ptr2)
    (integerp x)
    )
   (disjoint (blks-ptr ptr2 skel)
             (blk (+ ptr2 x) size)))
  :hints (("goal" :in-theory (enable RELOCATE-BLK-OFFSET
                                     BAG::DISJOINT-APPEND-REDUCTION
                                     ))))

(defthm disjoint-blk-ptr-blks-ptr-independent-of-ptr-0-conclusion
  (implies
   (and
    (disjoint (blks-ptr ptr1 skel)
              (blk (+ ptr1 x) size))
    (wf-skel skel)
    (integerp ptr1)
    (integerp x)
    )
   (disjoint (blks-ptr 0 skel)
             (blk x size)))
  :hints (("Goal" :use (:instance  disjoint-blk-ptr-blks-ptr-independent-of-ptr (ptr2 0))
           :in-theory (disable  disjoint-blk-ptr-blks-ptr-independent-of-ptr))))

(defthm disjoint-blk-ptr-blks-ptr-independent-of-ptr-0-hyp
  (implies
   (and
    (disjoint (blks-ptr 0 skel)
              (blk x size))
    (wf-skel skel)
    (integerp ptr2)
    (integerp x)
    )
   (disjoint (blks-ptr ptr2 skel)
             (blk (+ ptr2 x) size)))
  :hints (("Goal" :use (:instance  disjoint-blk-ptr-blks-ptr-independent-of-ptr (ptr1 0))
           :in-theory (disable  disjoint-blk-ptr-blks-ptr-independent-of-ptr))))

(defthm blks-ptr-reduction
  (implies
   (not (integerp ptr1))
   (equal (blks-ptr ptr1 skel)
          (blks-ptr 0 skel))))

;; Perhaps this should be changed so that we know more about
;; relocate-blk (rather than leaving relocate-blk-offset off)

(defthm unique-blks-ptr-independent-of-ptr
  (implies
   (and
    (unique (blks-ptr ptr1 skel))
    (wf-skel skel))
   (unique (blks-ptr ptr2 skel)))
  :hints (("goal" :in-theory (enable bag::unique-of-append)  ;bzo
           :induct (blks-ptr ptr2 skel))))

(defthm blks-ptr-g*-reduction-casesplit
  (equal (blks-ptr addr (g* rptr rskel ram))
         (if (zerop (ifix rptr)) nil (blks-ptr addr rskel))))

(defthm integerp-cadar-g*
  (implies
   (consp (g* rptr skel ram))
   (integerp (cadar (g* rptr skel ram)))))

(defthm wf-skel-g*
  (implies
   (wf-skel skel)
   (wf-skel (g* ptr skel ram))))

;;
;;
;; s* takes a fleshed out skeleton and applies it to a memory.
;;
;;

(defun s* (skel ram)
  (declare (type (satisfies weak-skel) skel))
  (if (consp skel)
      (let ((entry (car skel)))
        (let (;(akey (car entry))        ; abstract key
              (base (cadr entry))         ; base address
              (indx (caddr entry))       ; index
              (size (cadddr entry))      ; size
              (valu (caddddr entry))     ; value
              (type (cadddddr entry)))   ; type
          (let ((ram (s* type ram)))
            (let ((ram (s* (cdr skel) ram)))
              (wx size (+ indx base) valu ram)))))
    ram))

(defthm open-s*
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol skel))
     (consp skel))
    (equal (s* skel ram)
           (let ((entry (car skel)))
             (let (;(akey (car entry))        ; abstract key
                   (base (cadr entry))         ; base address
                   (indx (caddr entry))       ; index
                   (size (cadddr entry))      ; size
                   (valu (caddddr entry))     ; value
                   (type (cadddddr entry)))   ; type
               (let ((ram (s* type ram)))
                 (let ((ram (s* (cdr skel) ram)))
                   (wx size (+ indx base) valu ram)))))))
   (implies
    (and
     (syntaxp (syntax-atom skel))
     (not (consp skel)))
    (equal (s* skel ram) ram)))
  :hints (("goal" :in-theory '(s*))))

(defun g*-instance (rptr rskel wskel)
  (declare (type integer rptr)
           (type (satisfies weak-skel) rskel wskel)
           (xargs :measure (cons (1+ (acl2-count rskel)) (acl2-count wskel))))
  (if (and (consp rskel) (not (zerop (ifix rptr))))
      (if (consp wskel)
          (let ((rentry (car rskel))
                (wentry (car wskel)))
            (let ((wbase (cadr wentry))
                  (wvalu (caddddr wentry))
                  (wtype (cadddddr wentry))
                  (rtype (cadddddr rentry)))
              (if (spec-equal rentry wentry)
                  (if (equal (ifix rptr) wbase)
                      (and (g*-instance (ifix rptr) (cdr rskel) (cdr wskel))
                           (g*-instance wvalu rtype wtype))
                    nil)
                nil)))
        nil)
    t))

(defthm g*-instance-g*
  (implies
   (wf-skel rskel)
   (g*-instance rptr rskel (g* rptr rskel ram)))
  :hints (("goal" :induct (g* rptr rskel ram))))

(defun g*-fix (rptr rskel wskel)
  (declare (type integer rptr)
           (type (satisfies weak-skel) rskel wskel)
           (xargs :measure (cons (1+ (acl2-count rskel)) (acl2-count wskel))))
  (if (and (consp rskel) (not (zerop (ifix rptr))))
      (if (consp wskel)
          (let ((rentry (car rskel))
                (wentry (car wskel)))
            (if (spec-equal rentry wentry)
                (let ((akey (car wentry))       ; abstract key
                      (base (cadr wentry))      ; base
                      (indx (caddr wentry))     ; index
                      (size (cadddr wentry))    ; size
                      (ptr  (caddddr wentry))   ; pointer
                      (wtype (cadddddr wentry)) ; type
                      (rtype (cadddddr rentry)))
                  (let ((type (g*-fix ptr rtype wtype)))
                    (cons `(,akey ,base ,indx ,size ,ptr ,type)
                          (g*-fix (ifix rptr) (cdr rskel) (cdr wskel)))))
              (g*-fix (ifix rptr) rskel (cdr wskel))))
        nil)
    nil))

(defthm g*-fix-g*
  (implies
   (wf-skel rskel)
   (equal (g*-fix rptr rskel (g* rptr rskel ram))
          (g* rptr rskel ram))))


(defun x*-instance (rskel wskel)
  (declare (type (satisfies weak-skel) rskel wskel)
           (xargs :measure (cons (1+ (acl2-count rskel)) (acl2-count wskel))))
  (if (consp rskel)
      (if (consp wskel)
          (let ((rentry (car rskel))
                (wentry (car wskel)))
            (let ((wbase (cadr wentry))
                  (rbase (cadr rentry))
                  (wtype (cadddddr wentry))
                  (rtype (cadddddr rentry)))
              (if (spec-equal rentry wentry)
                  (if (equal rbase wbase)
                      (and (x*-instance (cdr rskel) (cdr wskel))
                           (x*-instance rtype wtype))
                    nil)
                nil)))
        nil)
    t))


(defthm x*-instance-x*
  (implies
   (wf-skel rskel)
   (x*-instance rskel (x* rskel ram))))

(defun x*-fix (rskel wskel)
  (declare (type (satisfies weak-skel) rskel wskel)
           (xargs :measure (cons (1+ (acl2-count rskel)) (acl2-count wskel))))
  (if (consp rskel)
      (if (consp wskel)
          (let ((rentry (car rskel))
                (wentry (car wskel)))
            (if (spec-equal rentry wentry)
                (let ((akey (car wentry))       ; abstract key
                      (base (cadr wentry))     ; base
                      (indx (caddr wentry))     ; index
                      (size (cadddr wentry))    ; size
                      (ptr  (caddddr wentry))   ; pointer
                      (wtype (cadddddr wentry)) ; type
                      (rtype (cadddddr rentry)))
                  (let ((type (x*-fix rtype wtype)))
                    (cons `(,akey ,base ,indx ,size ,ptr ,type)
                          (x*-fix (cdr rskel) (cdr wskel)))))
              (x*-fix rskel (cdr wskel))))
        nil)
    nil))


(defthm x*-fix-x*
  (implies
   (wf-skel rskel)
   (equal (x*-fix rskel (x* rskel ram))
          (x* rskel ram))))

;;
;; rx/wx - x*/g*/s* rules
;;

(in-theory (disable DEFAULT-*-2 DEFAULT-*-1
                    ACL2::INTEGERP-+-MINUS-*
                    ACL2::INTEGERP-*-CONSTANT-MEANS-1
;                    ACL2::TOP-BIT-MEANS-<
                    ACL2::INTEGERP-+-MINUS-*
                    ;DISJOINT-BLK-FREE-BACKCHAINING-1
                    ;DISJOINT-BLK-FREE-BACKCHAINING-2
                    ;DISJOINT-BLK-FREE-BACKCHAINING-2A
                    ;DISJOINT-BLK-FREE-BACKCHAINING-1A
                    ))

(in-theory (disable UNIFORM-BASE-BLKS-TRANSFORMATION))

(defthm s*-over-wx-mesh
  (implies
   (and
    (syntaxp (not (syntax-consp-or-quote rskel)))
    (disjoint (flatten rskel) (blk wptr (1+ (max-offset wsize))))
    (wf-skel rskel)
    )
  (equal (s* rskel (wx wsize wptr v ram))
         (wx wsize wptr v (s* rskel ram))))
  :hints (("goal" :in-theory (e/d (sblk) (fix ifix))
           :expand ((BLKS RSKEL)
                    (MESH RSKEL))
           :induct (s* rskel ram))))


(defthm x*-over-wx-mesh
  (implies
   (and
    (syntaxp (not (syntax-consp-or-quote rskel)))
    (disjoint (flatten rskel)
              (blk wptr (1+ (max-offset wsize))))
    (wf-skel rskel)
    )
   (equal (x* rskel (wx wsize wptr value ram))
          (x* rskel ram)))
  :hints (("goal" :in-theory (e/d (sblk) (WF-SKEL
                                          ;OPEN-WF-SKEL
                                          ;efficiency:
                                          BAG::DISJOINT-APPEND-REDUCTION
                                          ))

;efficiency:
           :expand  ((MESH RSKEL)
                     (BLKS RSKEL))
           :induct (x* rskel ram)))
  ) ; :rule-classes ((:rewrite :match-free :once)))

(defthm rx-over-s*-mesh
  (implies
   (and
    (disjoint (flatten wskel)
              (blk rptr (1+ (max-offset rsize))))
    (wf-skel wskel)
    )
   (equal (rx rsize rptr (s* wskel ram))
          (rx rsize rptr ram)))
  :hints (("goal" :in-theory (enable sblk)
           :induct (s* wskel ram)))
  ) ; :rule-classes ((:rewrite :match-free :once)))

;;
;; x*/g*/s* rules
;;

;; (defthm flatten-of-cons
;;   (equal (flatten (cons a skel))
;;          (APPEND (BLKS (cons a SKEL)) (MESH (cons a SKEL)))))

(in-theory (disable mesh blks)) ;trying, now that we have blks-of-cons and mesh-of-cons...


(local (in-theory (disable BINARY-APPEND))) ;bzo why is append on?

(defthm x*-over-s*-mesh
  (implies
   (and
    (syntaxp (not (syntax-consp-or-quote rskel)))
    (disjoint (flatten rskel)
              (flatten wskel))
    (wf-skel rskel)
    (wf-skel wskel)
    )
   (equal (x* rskel (s* wskel ram))
          (x* rskel ram)))
  :hints (("goal" :in-theory (enable mesh)
           :induct (s* wskel ram))))

(defthm s*-over-s*
  (implies
   (and
    (syntaxp (not (syntax-consp-or-quote skel1)))
    (disjoint (flatten skel1)
              (flatten skel2))
    (wf-skel skel1)
    (wf-skel skel2)
    )
   (equal (s* skel1 (s* skel2 ram))
          (s* skel2 (s* skel1 ram))))
  :hints (("goal" :in-theory (enable mesh)
           :induct (s* skel2 ram)))
  :rule-classes ((:rewrite :loop-stopper ((skel2 skel1 s*)))))

(defthm g*-over-s*-s*
  (implies
   (and
    (and
     (disjoint (flatten skel1)
               (flatten skel2))
     (equal v (g* rptr rskel (s* skel1 ram)))
     (disjoint (flatten skel2)
               (flatten v))
     (wf-skel rskel)
     (wf-skel skel1)
     (wf-skel skel2)
     )
    )
   (equal (g* rptr rskel (s* skel1 (s* skel2 ram))) v)))



;; (defthm x*-x*
;;   (implies
;;    (equal ram1 ram2)
;;    (equal (x* (x* skel ram1) ram2)
;;           (x* skel ram2))))

;; (defthm x*-g*
;;   (implies
;;    (equal ram1 ram2)
;;    (equal (x* (g* ptr skel ram1) ram2)
;;           (g* ptr skel ram2))))


(defthm x*-x*
  (equal (x* (x* skel ram) ram)
         (x* skel ram)))

(defthm x*-g*
  (equal (x* (g* ptr skel ram) ram)
         (g* ptr skel ram)))

(defun s*-instance (skel ram)
  (declare (type t skel ram))
  (if (and (consp ram)
           (equal (car ram) 's*) ; (s* skel ram)
           (consp (cdr ram))
           (consp (cddr ram)))
      (if (equal skel (cadr ram))
          t
        (s*-instance skel (caddr ram)))
    nil))

;; #+joe
;; (defthm ram==s*
;;   (implies
;;    (and
;;     (syntaxp (not (s*-instance skel ram2)))
;;     (equal skel (x* skel ram2))
;;     (equal ram1 ram2)
;;     )
;;    (and (equal (equal (s* skel ram1) ram2)
;;                t)
;; ;        (equal (equal ram2 (s* skel ram1))
;;  ;              t)
;;         )))

;bzo an odd lemma. try disabled?
(defthm s*==s*
  (implies
   (and
    (equal skel1 skel2)
    (equal ram1 ram2)
    )
   (equal (equal (s* skel1 ram1) (s* skel2 ram2))
          t)))

(defthm disjoint-blks-from-x*-instance
  (implies
   (and
    (x*-instance a b)
    (disjoint (blks b) c))
   (disjoint (blks a) c))
  :hints (("Goal" :in-theory (enable BAG::DISJOINT-APPEND-REDUCTION))))

;nested inductions
(defthm disjoint-mesh-from-x*-instance
  (implies (and (x*-instance a b)
                (disjoint (mesh b) c))
           (disjoint (mesh a) c))
  :hints (("Goal" ;:do-not '(generalize eliminate-destructors)
           :in-theory (e/d (bag::disjoint-of-append-one ;yuck
                              mesh
                              blks
                              bag::disjoint-of-append-two)
                           (ifix)))))

(defthm subbagp-blks-g*-fix-lemma
  (subbagp (BLKS (G*-FIX PTR C2 a))
           (BLKS a)))

(defthm disjoint-blks-g*-fix
  (implies (disjoint (blks a) b)
           (disjoint (blks (g*-fix ptr c a)) b))
  :hints (("Goal" :in-theory (e/d (BAG::SUBBAGP-DISJOINT) (g*-fix)))))

(defthm disjoint-g*-blks-g*-fix-2
  (implies (disjoint b (blks a))
           (disjoint b (blks (g*-fix ptr c a))))
  :hints (("Goal" :in-theory (e/d (BAG::SUBBAGP-DISJOINT) (g*-fix)))))

(defthm disjoint-mesh-g*-fix
  (implies
   (disjoint (mesh b) c)
   (disjoint (mesh (g*-fix ptr a b)) c))
;  :hints (("Goal" :in-theory (e/d (BAG::SUBBAGP-DISJOINT) (g*-fix))))
  :hints (("Goal" ;:do-not '(generalize eliminate-destructors)
           :in-theory (enable bag::disjoint-of-append-one ;yuck
                              bag::disjoint-of-append-two))))

(defthm mesh-x*-g*
  (implies
   (wf-skel skel)
   (equal (mesh (x* (g* ptr skel ram1) ram2))
          (mesh (g* ptr skel ram1)))))

;; #+joe
;; (defthm s*-of-g*
;;   (equal (s* (g* ptr skel ram) ram)
;;          ram))

(defthm x*-fix-g*
  (equal (x*-fix (g* ptr skel ram)
                 (g* ptr skel ram))
         (g* ptr skel ram)))

(defthm x*-instance-g*
  (x*-instance (g* ptr skel ram)
               (g* ptr skel ram)))


(in-theory (disable
            G*-OVER-S*-S*
            BLKS-G*-REDUCTION-CASESPLIT
            ))


;; ;bzo
;; #+joe
;; (defthm x*-of-s*
;;   (implies
;;    (and
;;     (syntaxp (not (syntax-consp-or-quote rskel)))
;;     (unique (flatten wskel))
;;     (x*-instance rskel wskel)
;;     (wf-skel rskel)
;;     (wf-skel wskel)
;;     )
;;    (equal (x* rskel (s* wskel ram))
;;           (x*-fix rskel wskel)))
;;   :hints (("goal" :in-theory '((:DEFINITION ANYTHING)
;;         (:DEFINITION BLKS)
;;         (:DEFINITION FIX)
;;         (:DEFINITION FLATTEN)
;;         (:DEFINITION IFIX)
;;         (:DEFINITION NOT)
;;         (:DEFINITION NULL)
;;         (:DEFINITION POSITIVE-INTEGERP)
;;         (:DEFINITION SYNP)
;;         (:DEFINITION WF-SKEL)
;;         (:DEFINITION WINTN)
;;         (:DEFINITION X*-FIX)
;;         (:DEFINITION X*-INSTANCE)
;;         (:ELIM CAR-CDR-ELIM)
;;         (:EXECUTABLE-COUNTERPART BLKS)
;;         (:EXECUTABLE-COUNTERPART CONSP)
;;         (:EXECUTABLE-COUNTERPART DISJOINT)
;;         (:EXECUTABLE-COUNTERPART EQUAL)
;;         (:EXECUTABLE-COUNTERPART MESH)
;;         (:EXECUTABLE-COUNTERPART SYNP)
;;         (:EXECUTABLE-COUNTERPART UNIQUE)
;;         (:EXECUTABLE-COUNTERPART X*-FIX)
;;         (:EXECUTABLE-COUNTERPART X*-INSTANCE)
;;         (:INDUCTION X*-FIX)
;;         (:FORWARD-CHAINING NON-NEGATIVE-INTEGERP-IMPLIES)
;;         (:FORWARD-CHAINING WEAK-SKEL-IMPLIES-TRUE-LISTP)
;;         (:FORWARD-CHAINING WF-SKEL-IMPLIES-WEAK-SKEL)
;;         (:REWRITE CAR-CONS)
;;         (:REWRITE CDR-CONS)
;;         (:REWRITE COMMUTATIVITY-OF-+)
;;         (:REWRITE DISJOINT-BLKS-FROM-X*-INSTANCE)
;;         (:REWRITE DISJOINT-COMMUTATIVE)
;;         (:REWRITE DISJOINT-of-APPEND-one)
;;         (:REWRITE DISJOINT-of-APPEND-two)
;;         (:REWRITE DISJOINT-MESH-FROM-X*-INSTANCE)
;;         (:REWRITE EQUAL-TRUE-LIST-CASES)
;;         (:REWRITE IMPLIES-NON-NEGATIVE-INTEGERP)
;;         (:REWRITE IMPLIES-POSITIVE-INTEGERP)
;;         (:REWRITE OPEN-BLKS)
;;         (:REWRITE OPEN-MESH)
;;         (:REWRITE OPEN-S*)
;;         (:REWRITE OPEN-WF-SKEL)
;;         (:REWRITE OPEN-X*)
;;         (:REWRITE REMOVE-LIST-UNIT)
;;         (:REWRITE RX-OF-WX)
;;         (:REWRITE S*-OVER-S*)
;;         (:REWRITE UNICITY-OF-0)
;;         (:REWRITE UNIQUE-of-APPEND)
;;         (:REWRITE UNIQUE-BLK)
;;         (:REWRITE X*-OVER-S*-MESH)
;;         (:REWRITE X*-OVER-WX-MESH)
;;         (:TYPE-PRESCRIPTION DISJOINT)
;;         (:TYPE-PRESCRIPTION NON-NEGATIVE-INTEGERP)
;;         (:TYPE-PRESCRIPTION UNIQUE)
;;         (:TYPE-PRESCRIPTION WEAK-SKEL)
;;         (:TYPE-PRESCRIPTION WF-SKEL)
;;         (:TYPE-PRESCRIPTION WFIXN)
;;         (:TYPE-PRESCRIPTION X*-FIX)
;;         (:TYPE-PRESCRIPTION X*-INSTANCE)))))

;; #+joe
;; (defthm g*-of-s*
;;   (implies
;;    (and
;;     (syntaxp (not (syntax-consp-or-quote rskel)))
;;     (unique (flatten wskel))
;;     (g*-instance ptr rskel wskel)
;;     (wf-skel wskel)
;;     (wf-skel rskel)
;;     )
;;    (equal (g* ptr rskel (s* wskel ram))
;;           (g*-fix ptr rskel wskel)))
;;   :hints (("goal" :in-theory '((:DEFINITION ANYTHING)
;;         (:DEFINITION BLKS)
;;         (:DEFINITION FIX)
;;         (:DEFINITION FLATTEN)
;;         (:DEFINITION G*)
;;         (:DEFINITION G*-FIX)
;;         (:DEFINITION G*-INSTANCE)
;;         (:DEFINITION IFIX)
;;         (:DEFINITION NOT)
;;         (:DEFINITION NULL)
;;         (:DEFINITION POSITIVE-INTEGERP)
;;         (:DEFINITION SYNP)
;;         (:DEFINITION WF-SKEL)
;;         (:DEFINITION WINTN)
;;         (:DEFINITION ZEROP)
;;         (:ELIM CAR-CDR-ELIM)
;;         (:EXECUTABLE-COUNTERPART BLKS)
;;         (:EXECUTABLE-COUNTERPART CONSP)
;;         (:EXECUTABLE-COUNTERPART DISJOINT)
;;         (:EXECUTABLE-COUNTERPART EQUAL)
;;         (:EXECUTABLE-COUNTERPART FLATTEN)
;;         (:EXECUTABLE-COUNTERPART IFIX)
;;         (:EXECUTABLE-COUNTERPART MESH)
;;         (:EXECUTABLE-COUNTERPART SYNP)
;;         (:EXECUTABLE-COUNTERPART UNIQUE)
;;         (:FORWARD-CHAINING NON-NEGATIVE-INTEGERP-IMPLIES)
;;         (:FORWARD-CHAINING WEAK-SKEL-IMPLIES-TRUE-LISTP)
;;         (:FORWARD-CHAINING WF-SKEL-IMPLIES-WEAK-SKEL)
;;         (:INDUCTION G*-FIX)
;;         (:REWRITE CAR-CONS)
;;         (:REWRITE CDR-CONS)
;;         (:REWRITE COMMUTATIVITY-OF-+)
;;         (:REWRITE DISJOINT-BLKS-G*-FIX)
;;         (:REWRITE DISJOINT-COMMUTATIVE)
;;         (:REWRITE DISJOINT-of-APPEND-one)
;;         (:REWRITE DISJOINT-of-APPEND-two)
;;         (:REWRITE DISJOINT-MESH-G*-FIX)
;;         (:REWRITE DISJOINT-NIL)
;;         (:REWRITE EQUAL-TRUE-LIST-CASES)
;;         (:REWRITE G*-OVER-S*-MESH)
;;         (:REWRITE G*-OVER-S*-S*)
;;         (:REWRITE G*-OVER-WX-MESH)
;;         (:REWRITE IMPLIES-NON-NEGATIVE-INTEGERP)
;;         (:REWRITE IMPLIES-POSITIVE-INTEGERP)
;;         (:REWRITE OPEN-BLKS)
;;         (:REWRITE OPEN-G*)
;;         (:REWRITE OPEN-MESH)
;;         (:REWRITE OPEN-S*)
;;         (:REWRITE OPEN-WF-SKEL)
;;         (:REWRITE REMOVE-LIST-UNIT)
;;         (:REWRITE RX-OF-WX)
;;         (:REWRITE S*-OVER-S*)
;;         (:REWRITE UNICITY-OF-0)
;;         (:REWRITE UNIQUE-of-APPEND)
;;         (:REWRITE UNIQUE-BLK)
;;         (:TYPE-PRESCRIPTION DISJOINT)
;;         (:TYPE-PRESCRIPTION G*-FIX)
;;         (:TYPE-PRESCRIPTION NON-NEGATIVE-INTEGERP)
;;         (:TYPE-PRESCRIPTION UNIQUE)
;;         (:TYPE-PRESCRIPTION WEAK-SKEL)
;;         (:TYPE-PRESCRIPTION WF-SKEL)
;;         (:TYPE-PRESCRIPTION WFIXN)))))

;These two rules get sucked in by defstructure.  We disable these for
;efficiency, since we don't expect to reason about all-conses or no-conses.
;(The free variables in these rules make them not too bad, but still they are
;hung on cons, so every time we're reasoning about a call to cons, these rules
;go looking for calls to all-conses and no-conses.) -ews

(in-theory (disable cpath::consp-when-member-of-all-conses))
(in-theory (disable cpath::not-consp-when-member-of-no-conses))

;(in-theory (disable WFIXN-REWRITE-TO-LOGHEAD))

;from gacc.lisp - bzo

(defun syntax-consp-or-quote (skel)
  (declare (type t skel))
  (or (quotep skel)
      (and (consp skel)
           (equal (car skel) 'cons))))

(defun syntax-consp-or-symbol (skel)
  (declare (type t skel))
  (or (symbolp skel)
      (and (consp skel)
           (or (equal (car skel) 'cons)
               (and (equal (car skel) 'quote)
                    (consp (cdr skel))
                    (not (null (cadr skel))))))))

;move?
(defthmd open-flat
  (implies (and (syntaxp (syntax-consp-or-symbol list))
                (consp list))
           (equal (flat list)
                  (append (car list)
                          (flat (cdr list)))))
  :hints (("goal" :in-theory (enable flat))))

(defun syntax-atom (m)
  (declare (type t m))
  (or (symbolp m)
      (quotep m)))

;apparently, these happen to be the same...
;consider enabling this?
(defthmd skel-p-reduction
  (equal (skel-p x)
         (weak-skel-p x))
  :hints (("goal" :in-theory (enable skel-p))))

;this is a weird lemma?:
(defthm not-line-p-not-equal
  (implies (not (line-p x))
           (equal (equal (line k (skel b s)) x)
                  nil))
  :hints (("goal" :in-theory (enable ;weak-skel-p skel-p
                                     ;line-p line-skel weak-line-p line skel
                                     ))))

(in-theory (disable slot-p))

(defun which-p (which)
  (declare (type t which))
  (memberp which '(:all :ptr :val :nil)))

(defun how-p (how)
  (declare (type t how))
  (memberp how '(:g :x :z)))

(defun ptr? (type)
  (declare (type t type))
  (equal type :ptr))

(defun x? (op)
  (declare (type (satisfies op-p) op))
  (let ((how (op-how op)))
    (equal how :x)))

(defun whichnum (n)
  (declare (type integer n))
  (case n
        (3 :all)
        (2 :ptr)
        (1 :val)
        (0 :nil)))

;; Disabling this (and other functions like it) in some proofs helped speed
;; them up a lot!
;;
(defun numwhich (which)
  (declare (type t which))
  (case which
        (:all 3)
        (:ptr 2)
        (:nil 0)
        (t    1)))

(defthm logbit-1-1-of-numwhich
  (equal (equal 1 (acl2::logbit 1 (numwhich which)))
         (or (equal :all which)
             (equal :ptr which)))
  :hints (("Goal" :in-theory (enable acl2::logbit))))


(defun numtype (type)
  (declare (type t type))
  (case type
        (:ptr 2)
        (t    1)))

(defun whichtype (which type)
  (declare (type t which type))
  (let ((which (numwhich which))
        (type  (numtype  type)))
    (equal type (logand which type))))

(defthm skel-measure
  (implies (consp list)
           (e0-ord-< (acl2-count (skel-spec (slot-skel (car list))))
                     (acl2-count list)))
  :hints (("goal" :in-theory (enable skel-spec slot-skel))))

(defun fix-skel (skel)
  (declare (type t skel))
  (if (skel-p skel) skel (skel 0 nil)))

(defthm fix-skel-skel-p
  (implies (skel-p skel)
           (equal (fix-skel skel)
                  skel))
  :hints (("goal" :in-theory (enable fix-skel))))

(defun wfixn-skel (size skel)
  (let ((skel (fix-skel skel)))
    (skel (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                 (skel-base skel))
          (skel-spec skel))))

(defthm skel-p-fix-skel
  (and (skel-p (fix-skel skel))
       (skel-p (wfixn-skel size skel))))

(in-theory (disable fix-skel))

(defun spectype (type)
  (declare (type t type))
  (if (equal type :ptr) :ptr :val))

(defun op-base (h type base valu)
  (declare (type t h type base valu))
  (if (equal type :ptr)
      (if (equal h :x) base
        (if (equal h :z) 0 valu))
    base))

(defun wf-spec (spec)
  (declare (type t spec))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((skel (slot-skel slot))
                  (type (slot-type slot)))
              (and (skel-p skel)
                   (implies (ptr? type) (wf-spec (skel-spec skel)))
                   (wf-spec (cdr spec))))
          (wf-spec (cdr spec))))
    t))

(defun wf-skels (skels)
  (declare (type t skels))
  (if (consp skels)
      (let ((line (car skels)))
        (if (line-p line)
            (let ((skel (line-skel line)))
              (and (skel-p skel)
                   (wf-spec (skel-spec skel))
                   (wf-skels (cdr skels))))
          (wf-skels (cdr skels))))
    t))

(defun g*-spec (op ptr spec ram)
  (declare (type (satisfies op-p) op)
           (type (satisfies wf-spec) spec)
           (xargs :verify-guards nil))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how   op)))
              (let ((off   (slot-off  slot))
                    (size  (slot-size slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot))
                    (value (slot-val  slot))
                    )
                (let ((read (rx size (+<> off ptr) ram)))
                  (let ((base (skel-base skel)))
                    (let ((base (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                       (ifix (op-base h type base read))
                                       )))
                      (let ((value (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                          (ifix (if (whichtype w type) read value))
                                          )))
                        (let ((skel (if (ptr? type) (skel base (g*-spec op base (skel-spec skel) ram)) skel)))
                          (cons (update-slot slot
                                             :val  value
                                             :skel skel
                                             )
                                (g*-spec op ptr (cdr spec) ram)))))))))
          (cons slot
                (g*-spec op ptr (cdr spec) ram))))
    spec))


(defun G*-SPEC-car (op ptr slot ram)
  (IF
   (SLOT-P SLOT)
   (LET
    ((W (OP-WHICH OP)) (H (OP-HOW OP)))
    (LET
     ((OFF (SLOT-OFF SLOT))
      (SIZE (SLOT-SIZE SLOT))
      (TYPE (SLOT-TYPE SLOT))
      (SKEL (SLOT-SKEL SLOT))
      (VALUE (SLOT-VAL SLOT)))
     (LET
      ((READ (RX SIZE (|+<>| OFF PTR) RAM)))
      (LET
       ((BASE (SKEL-BASE SKEL)))
       (LET
        ((BASE
          (ACL2::LOGHEAD (FIX-SIZE SIZE)
                         (IFIX (OP-BASE H TYPE BASE READ)))))
        (LET
         ((VALUE
           (ACL2::LOGHEAD
            (FIX-SIZE SIZE)
            (IFIX (IF (WHICHTYPE W TYPE) READ VALUE)))))
         (LET
          ((SKEL
            (IF (PTR? TYPE)
                (SKEL BASE
                      (G*-SPEC OP BASE (SKEL-SPEC SKEL) RAM))
                SKEL)))
          (UPDATE-SLOT SLOT :VAL VALUE :SKEL SKEL))))))))
   SLOT))

(DEFTHM G*-SPEC-of-non-cons
  (implies (not (consp spec))
           (EQUAL (G*-SPEC OP ptr spec RAM)
                  spec))
  :hints (("Goal" :in-theory (enable g*-spec))))

(defthm g*-spec-of-cons
  (equal (g*-spec op ptr (cons slot spec) ram)
         (cons (g*-spec-car op ptr slot ram)
               (g*-spec op ptr spec ram)))
  :hints (("Goal" :in-theory (e/d (g*-spec) (numwhich numtype op-base ptr? whichtype)))))


(defthm car-of-g*-spec
  (equal (car (G*-SPEC OP ptr spec RAM))
         (if (consp spec)
             (g*-spec-car op ptr (car spec) ram)
           (car spec)))
  :hints (("Goal" :in-theory (enable g*-spec))))

(defthm cdr-of-g*-spec
  (equal (cdr (G*-SPEC OP ptr spec RAM))
         (g*-spec op ptr (cdr spec) ram))
  :hints (("Goal" :in-theory (e/d (g*-spec) (numwhich numtype op-base ptr? whichtype)))))



(defthm wf-spec-g*-spec
  (wf-spec (g*-spec op ptr spec ram))
  :hints (("Goal" :in-theory (disable numwhich numtype op-base whichtype ptr? ifix))))

(defthm consp-g*-spec
  (equal (consp (g*-spec op ptr spec ram))
         (consp spec)))

;bzo
(defthm loghead-of-ifix
  (equal (acl2::loghead n (ifix base))
         (acl2::loghead n base)))

(defthm open-g*-spec
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol spec))
     (consp spec))
    (equal (g*-spec op ptr spec ram)
           (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how   op)))
              (let ((off   (slot-off  slot))
                    (size  (slot-size slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot))
                    (value (slot-val  slot))
                    )
                (let ((read (rx size (+<> off ptr) ram)))
                  (let ((base (skel-base skel)))
                    (let ((base (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                       (op-base h type base read))))
                      (let ((value (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                          (if (whichtype w type) read value))))
                        (let ((skel (if (ptr? type) (skel base (g*-spec op base (skel-spec skel) ram)) skel)))
                          (cons (update-slot slot
                                             :val  value
                                             :skel skel
                                             )
                                (g*-spec op ptr (cdr spec) ram)))))))))
          (cons slot
                (g*-spec op ptr (cdr spec) ram))))))
   (implies
    (and
     (syntaxp (syntax-atom spec))
     (not (consp spec)))
    (equal (g*-spec op ptr spec ram)
           spec)))
  :hints (("goal" :in-theory '(g*-spec loghead-of-ifix))))

(in-theory (disable (:definition g*-spec) (g*-spec)))

(defund g*-list (op skels ram)
  (declare (type (satisfies op-p) op)
           (type (satisfies wf-skels) skels))
  (if (consp skels)
      (let ((line (car skels)))
        (if (line-p line)
            (let ((key  (line-key line))
                  (skel (line-skel line)))
              (let ((base (op-base (op-how op) :ptr (skel-base skel) key)))
                (let ((line (line key (skel base (g*-spec op base (skel-spec skel) ram)))))
                  (cons line
                        (g*-list op (cdr skels) ram)))))
          (cons line
                (g*-list op (cdr skels) ram))))
    skels))

(in-theory (disable (:executable-counterpart g*-list)))

;bzo Eric added this to support G*-LIST-of-cons.  Could change g*-list to call this function?
(defun g*-list-car (op line ram)
  (IF (LINE-P LINE)
      (LET
       ((KEY (LINE-KEY LINE))
        (SKEL (LINE-SKEL LINE)))
       (LET
        ((BASE (OP-BASE (OP-HOW OP)
                              :PTR (SKEL-BASE SKEL)
                              KEY)))
        (LINE KEY
              (SKEL BASE
                    (G*-SPEC OP BASE (SKEL-SPEC SKEL)
                             RAM)))))
      LINE))

(defthm car-of-g*-list
  (equal (car (g*-list op skels ram))
         (if (consp skels)
             (g*-list-car op (car skels) ram)
           (car skels)))
  :hints (("Goal" :in-theory (enable g*-list))))

(defthm cdr-of-g*-list
  (equal (cdr (g*-list op skels ram))
         (g*-list op (cdr skels) ram))
  :hints (("Goal" :in-theory (enable g*-list))))

;big speed up in a later book from this instead of using open-g*-list!
(defthm g*-list-of-cons
  (equal (g*-list op (cons line skels) ram)
         (cons (g*-list-car op line ram) (g*-list op skels ram)))
  :hints (("Goal" :in-theory (enable g*-list))))

(DEFTHM G*-LIST-of-non-cons
  (implies (not (consp skels))
           (EQUAL (G*-LIST OP SKELS RAM)
                  SKELS))
  :hints (("Goal" :in-theory (enable g*-list))))

(defthmd open-g*-list
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol skels))
     (consp skels))
    (equal (g*-list op skels ram)
           (let ((line (car skels)))
        (if (line-p line)
            (let ((key  (line-key line))
                  (skel (line-skel line)))
              (let ((base (op-base (op-how op) :ptr (skel-base skel) key)))
                (let ((line (line key (skel base (g*-spec op base (skel-spec skel) ram)))))
                  (cons line
                        (g*-list op (cdr skels) ram)))))
          (cons line
                (g*-list op (cdr skels) ram))))))
   (implies
    (and
     (syntaxp (syntax-atom skels))
     (not (consp skels)))
    (equal (g*-list op skels ram)
           skels)))
  :hints (("goal" :in-theory '(g*-list))))

(defthm consp-g*-list
  (equal (consp (g*-list op list ram))
         (consp list))
  :hints (("Goal" :in-theory (enable g*-list))))

(defthm g*-list-append
  (equal (g*-list op (append x y) ram)
         (append (g*-list op x ram)
                 (g*-list op y ram)))
  :hints (("goal" :in-theory (enable binary-append g*-list)
           :induct (append x y))))

(defthm wf-skels-g*-list
  (wf-skels (g*-list op skels ram))
  :hints (("Goal" :in-theory (enable g*-list))))



(defun s*-spec (op ptr spec ram)
  (declare (type (satisfies op-p) op)
           (type (satisfies wf-spec) spec))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how op)))
              (let ((size  (slot-size slot))
                    (off   (slot-off  slot))
                    (value (slot-val  slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot)))
                (let ((read value))
                  (let ((base (skel-base skel)))
                    (let ((base (acl2::loghead (fix-size size) ;wfixn 8 size
                                       (ifix (op-base h type base read)))))
                      (let ((value (acl2::loghead (fix-size size) ;wfixn 8 size
                                          (ifix (if (whichtype w type) value (rx size (+<> off ptr) ram))))))
                        (let ((ram (wx size (+<> off ptr) value ram)))
                          (let ((ram (if (ptr? type)
                                         (s*-spec op base (skel-spec skel) ram)
                                       ram)))
                            (s*-spec op ptr (cdr spec) ram)))))))))
          (s*-spec op ptr (cdr spec) ram)))
    ram))


(defthm open-s*-spec
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol spec))
     (consp spec))
    (equal (s*-spec op ptr spec ram)
           (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how op)))
              (let ((size  (slot-size slot))
                    (off   (slot-off  slot))
                    (value (slot-val  slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot)))
                (let ((read value))
                  (let ((base (skel-base skel)))
                    (let ((base (acl2::loghead (fix-size size) ;wfixn 8 size
                                       (op-base h type base read))))
                      (let ((value (acl2::loghead (fix-size size) ;wfixn 8 size
                                          (if (whichtype w type) value (rx size (+<> off ptr) ram)))))
                        (let ((ram (wx size (+<> off ptr) value ram)))
                          (let ((ram (if (ptr? type)
                                         (s*-spec op base (skel-spec skel) ram)
                                       ram)))
                            (s*-spec op ptr (cdr spec) ram)))))))))
          (s*-spec op ptr (cdr spec) ram)))))
   (implies
    (and
     (syntaxp (syntax-atom spec))
     (not (consp spec)))
    (equal (s*-spec op ptr spec ram)
           ram)))
  :hints (("goal" :in-theory '(s*-spec loghead-of-ifix))))

(in-theory (disable (:definition s*-spec) (s*-spec)))

(defun s*-list (op skels ram)
  (declare (type (satisfies op-p) op)
           (type (satisfies wf-skels) skels))
  (if (consp skels)
      (let ((line (car skels)))
        (if (line-p line)
            (let ((skel (line-skel line))
                  (key  (line-key line)))
              (let ((base (op-base (op-how op) :ptr (skel-base skel) key)))
                (let ((ram (s*-list op (cdr skels) ram)))
                  (s*-spec op base (skel-spec skel) ram))))
          (s*-list op (cdr skels) ram)))
    ram))

(defthm open-s*-list
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol skels))
     (consp skels))
    (equal (s*-list op skels ram)
           (let ((line (car skels)))
        (if (line-p line)
            (let ((skel (line-skel line))
                  (key  (line-key line)))
              (let ((base (op-base (op-how op) :ptr (skel-base skel) key)))
                (let ((ram (s*-list op (cdr skels) ram)))
                  (s*-spec op base (skel-spec skel) ram))))
          (s*-list op (cdr skels) ram)))))
   (implies
    (and
     (syntaxp (syntax-atom skels))
     (not (consp skels)))
    (equal (s*-list op skels ram)
           ram)))
  :hints (("goal" :in-theory '(s*-list))))

(in-theory (disable (:definition s*-list) (s*-list)))

;;
;; f* (flatten) returns the addresses of selected locations, useful
;; for determining disjointness.
;;


(defun f*-spec (op ptr spec)
  (declare (type (satisfies op-p) op)
           (type (satisfies wf-spec) spec))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how op)))
              (let ((off  (slot-off  slot))
                    (size (slot-size slot))
                    (type (slot-type slot))
                    (skel (slot-skel slot))
                    (value (slot-val slot)))
                (let ((read value))
                  (let ((base (skel-base skel)))
                    (let ((base (acl2::loghead (fix-size size) ;wfixn 8 size
                                       (ifix (op-base h type base read)))))
                      (let ((blk (if (whichtype w type) (list (sblk size (+<> off ptr))) nil)))
                        (let ((rec (if (ptr? type) (f*-spec op base (skel-spec skel)) nil)))
                          (append blk
                                  rec
                                  (f*-spec op ptr (cdr spec))))))))))
          (f*-spec op ptr (cdr spec))))
    nil))

(defthm f*-spec-when-ptr-is-not-an-integerp
  (implies (not (integerp ptr))
           (equal (f*-spec op ptr spec)
                  (f*-spec op 0 spec))))

(defthm open-f*-spec
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol spec))
     (consp spec))
    (equal (f*-spec op ptr spec)
           (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how op)))
              (let ((off  (slot-off  slot))
                    (size (slot-size slot))
                    (type (slot-type slot))
                    (skel (slot-skel slot))
                    (value (slot-val slot)))
                (let ((read value))
                  (let ((base (skel-base skel)))
                    (let ((base (acl2::loghead (fix-size size) ;wfixn 8 size
                                       (op-base h type base read))))
                      (let ((blk (if (whichtype w type) (list (sblk size (+<> off ptr))) nil)))
                        (let ((rec (if (ptr? type) (f*-spec op base (skel-spec skel)) nil)))
                          (append blk
                                  rec
                                  (f*-spec op ptr (cdr spec))))))))))
          (f*-spec op ptr (cdr spec))))))
   (implies
    (and
     (syntaxp (syntax-atom spec))
     (not (consp spec)))
    (equal (f*-spec op ptr spec)
           nil)))
  :hints (("goal" :in-theory '(f*-spec loghead-of-ifix))))

(defthm true-listp-f*-spec
  (true-listp (f*-spec op ptr spec)))

(defthm f*-spec-nil
  (implies (equal (op-which fop) :nil)
           (equal (f*-spec fop fptr spec)
                  nil)))

(in-theory (disable (:definition f*-spec) (f*-spec)))

;; We will need to prove that (f*-x :all ..) is a permutation of
;; (append (f*-x :ptr ..) (f*-x :val ..))  and rewrite it as such
;; under uniqueness/disjointness, etc.

(defun f*-list (op skels)
  (declare (type (satisfies op-p) op)
           (type (satisfies wf-skels) skels))
  (if (consp skels)
      (let ((line (car skels)))
        (if (line-p line)
            (let ((key  (line-key line))
                  (skel (line-skel line)))
              (let ((base (op-base (op-how op) :ptr (skel-base skel) key)))
                (append (f*-spec op base (skel-spec skel))
                        (f*-list op (cdr skels)))))
          (f*-list op (cdr skels))))
    nil))

(defthm open-f*-list
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol skels))
     (consp skels))
    (equal (f*-list op skels)
           (let ((line (car skels)))
        (if (line-p line)
            (let ((key  (line-key line))
                  (skel (line-skel line)))
              (let ((base (op-base (op-how op) :ptr (skel-base skel) key)))
                (append (f*-spec op base (skel-spec skel))
                        (f*-list op (cdr skels)))))
          (f*-list op (cdr skels))))))
   (implies
    (and
     (syntaxp (syntax-atom skels))
     (not (consp skels)))
    (equal (f*-list op skels)
           nil)))
  :hints (("goal" :in-theory '(f*-list))))

(defthm true-listp-f*-list
  (true-listp (f*-list op spec)))

(defthm f*-list-append
  (equal (f*-list op (append x y))
         (append (f*-list op x)
                 (f*-list op y)))
  :hints (("goal" :in-theory (enable binary-append))))


(defthm f*-list-nil
  (implies (equal (op-which fop) :nil)
           (equal (f*-list fop list) nil))
  :hints (("Goal" :in-theory (enable  op-which)
           :expand ( (f*-list fop list))))
  )

(in-theory (disable (:definition f*-list) (f*-list)))

;;
;; h* (heirarchy) returns a pared-down structure, useful for determining
;; structural equivalence.
;;

(defun h*-spec (op spec)
  (declare (type (satisfies op-p) op)
           (type (satisfies wf-spec) spec))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how   op)))
              (let ((size  (slot-size slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot))
                    (value (slot-val  slot))
                    )
                (let ((read value))
                  (let ((base (skel-base skel)))
                    (let ((base (acl2::loghead (fix-size size) ;wfixn 8 size
                                               (ifix (op-base h type base read)))))
                      (let ((value (acl2::loghead (fix-size size) ;wfixn 8 size
                                                  (ifix (if (whichtype w type) read 0)))))
                        (let ((skel (if (ptr? type) (skel base (h*-spec op (skel-spec skel))) skel)))
                          (cons (update-slot slot
                                             :val  value
                                             :skel skel
                                             )
                                (h*-spec op (cdr spec))))))))))
          (cons slot (h*-spec op (cdr spec)))))
    spec))


(defthm H*-SPEC-of-non-cons
  (implies (not (consp spec))
           (equal (H*-SPEC OP SPEC)
                  spec)))

(defun car-h*-spec (op slot)
  (IF
   (SLOT-P SLOT)
   (LET
    ((W (OP-WHICH OP)) (H (OP-HOW OP)))
    (LET
     ((SIZE (SLOT-SIZE SLOT))
      (TYPE (SLOT-TYPE SLOT))
      (SKEL (SLOT-SKEL SLOT))
      (VALUE (SLOT-VAL SLOT)))
     (LET
      ((READ VALUE))
      (LET
       ((BASE (SKEL-BASE SKEL)))
       (LET
        ((BASE
          (ACL2::LOGHEAD (FIX-SIZE SIZE)
                         (IFIX (OP-BASE H TYPE BASE READ)))))
        (LET
         ((VALUE (ACL2::LOGHEAD
                  (FIX-SIZE SIZE)
                  (IFIX (IF (WHICHTYPE W TYPE) READ 0)))))
         (LET
          ((SKEL (IF (PTR? TYPE)
                     (SKEL BASE (H*-SPEC OP (SKEL-SPEC SKEL)))
                     SKEL)))
          (UPDATE-SLOT SLOT :VAL VALUE :SKEL SKEL))))))))
   SLOT))

(defthm H*-SPEC-of-cons
  (equal (H*-SPEC OP (cons slot SPEC))
         (cons (car-h*-spec op slot)  (H*-SPEC OP SPEC)))
  :hints (("Goal" :in-theory (disable numtype numwhich op-base ptr? whichtype))))

(defthm car-of-h*-spec
  (equal (car (h*-spec op spec))
         (if (consp spec)
             (car-h*-spec op (car spec))
           nil))
  :hints (("Goal" :in-theory (disable numtype numwhich op-base ptr?))))

(defthm cdr-h*-spec
  (implies
   (consp spec)
   (equal (cdr (h*-spec op spec))
          (h*-spec op (cdr spec))))
  :hints (("goal" :in-theory (enable default-cdr)
           :expand (h*-spec op spec))))

#|
(defthm consp-h*-spec
  (implies
   (consp (h*-spec hop hspec))
   (consp hspec))
  :rule-classes (:forward-chaining))

(defthm not-consp-h*-spec
  (implies (not (consp (h*-spec hop hspec)))
           (not (consp hspec)))
  :rule-classes (:forward-chaining))
|#

(defthm consp-h*-spec-whamo
  (equal (consp (h*-spec op spec))
         (consp spec)))


(defthm open-h*-spec
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol spec))
     (consp spec))
    (equal (h*-spec op spec)
           (let ((slot (car spec)))
             (if (slot-p slot)
                 (let ((w (op-which op))
                       (h (op-how   op)))
                   (let ((size  (slot-size slot))
                         (type  (slot-type slot))
                         (skel  (slot-skel slot))
                         (value (slot-val  slot))
                         )
                     (let ((read value))
                       (let ((base (skel-base skel)))
                         (let ((base (acl2::loghead (fix-size size) ;wfixn 8 size
                                                    (op-base h type base read))))
                           (let ((value (acl2::loghead (fix-size size) ;wfixn 8 size
                                                       (if (whichtype w type) read 0))))
                             (let ((skel (if (ptr? type) (skel base (h*-spec op (skel-spec skel))) skel)))
                               (cons (update-slot slot
                                                  :val  value
                                                  :skel skel
                                                  )
                                     (h*-spec op (cdr spec))))))))))
               (cons slot (h*-spec op (cdr spec)))))))
   (implies
    (and
     (syntaxp (syntax-atom spec))
     (not (consp spec)))
    (equal (h*-spec op spec)
           spec)))
  :hints (("goal" :in-theory '(h*-spec loghead-of-ifix))))


(defthm wf-spec-h*-spec
  (wf-spec (h*-spec op spec)))

(in-theory (disable (:definition h*-spec) (h*-spec) ))

(defun h*-list (op skels)
  (declare (type (satisfies op-p) op)
           (type (satisfies wf-skels) skels))
  (if (consp skels)
      (let ((line (car skels)))
        (if (line-p line)
            (let ((key  (line-key line))
                  (skel (line-skel line)))
              (let ((base (op-base (op-how op) :ptr (skel-base skel) key)))
                (let ((key key))
                  (cons (line key (skel base (h*-spec op (skel-spec skel))))
                        (h*-list op (cdr skels))))))
          (cons line (h*-list op (cdr skels)))))
    skels))

(defthm h*-list-append
  (equal (h*-list op (append x y))
         (append (h*-list op x) (h*-list op y)))
  :hints (("goal" :in-theory (enable binary-append))))

(defthm len-h*-list
  (equal (len (h*-list op list))
         (len list)))

(defthm true-listp-h*-list
  (equal (true-listp (h*-list op list))
         (true-listp list)))

(defthm consp-h*-list
  (equal (consp (h*-list op list))
         (consp list)))

;add type-prescriptions?

(defthm open-h*-list
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol skels))
     (consp skels))
    (equal (h*-list op skels)
           (let ((line (car skels)))
        (if (line-p line)
            (let ((key  (line-key line))
                  (skel (line-skel line)))
              (let ((base (op-base (op-how op) :ptr (skel-base skel) key)))
                (let ((key key))
                  (cons (line key (skel base (h*-spec op (skel-spec skel))))
                        (h*-list op (cdr skels))))))
          (cons line (h*-list op (cdr skels)))))))
   (implies
    (and
     (syntaxp (syntax-atom skels))
     (not (consp skels)))
    (equal (h*-list op skels)
           skels)))
  :hints (("goal" :in-theory '(h*-list))))

(defthm wf-skels-h*-list
  (wf-skels (h*-list op skels)))

(in-theory (disable (:definition h*-list) (h*-list)))

;;
;; v* (value) returns a list of selected values from the skel
;;

(defun v*-spec (op spec)
  (declare (type (satisfies op-p) op)
           (type (satisfies wf-spec) spec))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  )
              (let ((size  (slot-size slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot))
                    (value (slot-val  slot))
                    )
                (let ((read value))
                  (let ((value (if (whichtype w type) (list (acl2::loghead (fix-size size) ;wfixn 8 size
                                                                           (ifix read)
                                                                           )) nil)))
                    (let ((rec (if (ptr? type) (v*-spec op (skel-spec skel)) nil)))
                      (append value
                              rec
                              (v*-spec op (cdr spec))))))))
          (v*-spec op (cdr spec))))
    nil))

(defthm open-v*-spec
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol spec))
     (consp spec))
    (equal (v*-spec op spec)
           (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  )
              (let ((size  (slot-size slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot))
                    (value (slot-val  slot))
                    )
                (let ((read value))
                  (let ((value (if (whichtype w type) (list (acl2::loghead (fix-size size) ;wfixn 8 size
                                                                           read)) nil)))
                    (let ((rec (if (ptr? type) (v*-spec op (skel-spec skel)) nil)))
                      (append value
                              rec
                              (v*-spec op (cdr spec))))))))
          (v*-spec op (cdr spec))))))
   (implies
    (and
     (syntaxp (syntax-atom spec))
     (not (consp spec)))
    (equal (v*-spec op spec)
           nil)))
  :hints (("goal" :in-theory '(v*-spec loghead-of-ifix))))


(defthm true-listp-v*-spec
  (true-listp (v*-spec op spec)))

(in-theory
 (disable
  (:definition v*-spec)
  (v*-spec)
  ))

(defun v*-list (op skels)
  (declare (type (satisfies op-p) op)
           (type (satisfies wf-skels) skels))
  (if (consp skels)
      (let ((line (car skels)))
        (if (line-p line)
            (let ((skel (line-skel line)))
              (append (v*-spec op (skel-spec skel))
                      (v*-list op (cdr skels))))
          (v*-list op (cdr skels))))
    nil))

(defthm open-v*-list
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol skels))
     (consp skels))
    (equal (v*-list op skels)
           (let ((line (car skels)))
        (if (line-p line)
            (let ((skel (line-skel line)))
              (append (v*-spec op (skel-spec skel))
                      (v*-list op (cdr skels))))
          (v*-list op (cdr skels))))))
   (implies
    (and
     (syntaxp (syntax-atom skels))
     (not (consp skels)))
    (equal (v*-list op skels)
           nil)))
  :hints (("goal" :in-theory '(v*-list))))

(defthm true-listp-v*-list
  (true-listp (v*-list op spec)))

(in-theory (disable (:definition v*-list) (v*-list)))



(defun fixed-spec-p (spec)
  (declare (type t spec))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((size  (slot-size slot))
                  (type  (slot-type slot))
                  (skel  (slot-skel slot))
                  (value (slot-val  slot))
                  )
              (let ((base  (skel-base skel))
                    (sspec (skel-spec skel)))
                (and (acl2::unsigned-byte-p (fix-size size) value) ;(wintn 8 size value)
                     (implies* (ptr? type)
                               (and (acl2::unsigned-byte-p (fix-size size) ;wintn 8 size
                                           base)
                                    (fixed-spec-p sspec)))
                     (fixed-spec-p (cdr spec)))))
          (fixed-spec-p (cdr spec))))
    t))

(defthm open-fixed-spec-p
  (implies
   (consp spec)
   (equal (fixed-spec-p spec)
          (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((size  (slot-size slot))
                  (type  (slot-type slot))
                  (skel  (slot-skel slot))
                  (value (slot-val  slot))
                  )
              (let ((base  (skel-base skel))
                    (sspec (skel-spec skel)))
                (and (acl2::unsigned-byte-p (fix-size size) value); (wintn 8 size value)
                     (implies* (ptr? type)
                               (and (acl2::unsigned-byte-p (fix-size size) base) ;(wintn 8 size base)
                                    (fixed-spec-p sspec)))
                     (fixed-spec-p (cdr spec)))))
          (fixed-spec-p (cdr spec)))))))

(defun fixed-skel-list (list)
  (if (consp list)
      (let ((line (car list)))
        (if (line-p line)
            (let ((skel (line-skel line)))
              (and (fixed-spec-p (skel-spec skel))
                   (fixed-skel-list (cdr list))))
          (fixed-skel-list (cdr list))))
    t))

(defthm h*-spec-fixed-spec-p
  (implies
   (fixed-spec-p spec)
   (equal (h*-spec (op :all :x) spec) spec)))

(defthm h*-list-fixed-skel-list
  (implies
   (fixed-skel-list list)
   (equal (h*-list (op :all :x) list) list)))

(defthm fixed-spec-p-h*-spec
  (fixed-spec-p (h*-spec op spec)))

(defthm fixed-skel-list-h*-list
  (fixed-skel-list (h*-list op list)))

(defthm fixed-spec-p-g*-spec
  (fixed-spec-p (g*-spec op ptr spec ram)))

(defthm fixed-skel-list-g*-list
  (fixed-skel-list (g*-list op list ram))
  :hints (("Goal" :in-theory (enable g*-list))))

(defthm atomic-f*-op-replacement
  (implies
   (syntaxp (symbolp fop))
   (equal (f*-spec fop base spec)
          (f*-spec (xop fop) base spec))))

(defthm atomic-h*-op-replacement
  (implies
   (syntaxp (symbolp hop))
   (equal (h*-spec hop spec)
          (h*-spec (xop hop) spec))))

(defthm atomic-g*-op-replacement
  (implies
   (syntaxp (symbolp gop))
   (equal (g*-spec gop ptr spec ram)
          (g*-spec (xop gop) ptr spec ram))))

(defthm atomic-s*-op-replacement
  (implies
   (syntaxp (symbolp sop))
   (equal (s*-spec sop ptr spec ram)
          (s*-spec (xop sop) ptr spec ram)))
  :hints (("Goal" :in-theory (disable
                              ;for efficiency:
                              whichtype OP-BASE ptr? ifix
                                      ))))

(defthm atomic-f*-list-op-replacement
  (implies
   (syntaxp (symbolp fop))
   (equal (f*-list fop list)
          (f*-list (xop fop) list))))

(defthm atomic-h*-list-op-replacement
  (implies
   (syntaxp (symbolp fop))
   (equal (h*-list fop list)
          (h*-list (xop fop) list))))

;experiment:
(local (in-theory (disable numwhich numtype)))


;;bzo
;;
;;
;; z* stuff (moved to gacc3.lisp [was in ram.lisp]).
;;
;;

(defun z* (zlist ram)
  ;(declare (type t zlist ram))
  (if (consp zlist)
      (let ((ram (z*-rec (car zlist) ram)))
        (z* (cdr zlist) ram))
    ram))

;;
;; This may be helpful in extending the z*-rec lemmas to z*
;;
;bzo nested inductions

(defthmd z*-reduction
  (equal (z* zlist ram)
         (z*-rec (flat zlist) ram))
  :hints (("Goal" :in-theory (enable append  ;bzo why the enables?
                                     flat
                                     ))))

(defthmd z*-wx-introduction
  (equal (equal (wx size ptr value ram1)
                ram2)
         (and (equal (z* (list (sblk size ptr)) ram1)
                     (z* (list (sblk size ptr)) ram2))
              (tag-location ptr (equal (acl2::loghead (fix-size size) ;wfixn 8 size
                                              value)
                                       (rx size ptr ram2)))))
  :hints (("Goal" :in-theory (e/d (blk sblk wx rx failed-location ;wfixn
                                       wx==ram-rec)
                                  (
                                   open-rx-rec open-wx-rec z*-same-wx-rec-0)))))

;bzo WX==RAM-REC seemed to loop here when wx was disabled...
(defthm z*-of-wx
  (implies
   (any-subbagp (sblk size ptr) zlist)
   (equal (z* zlist (wx size ptr value ram1))
          (z* zlist ram1)))
  :hints (("Goal" :in-theory (e/d (blk sblk wx z*-reduction) (open-wx-rec)))))

(defun z*-induction-fn (ptr ram1 ram2 size value zlist)
  (if (consp zlist)
      (z*-induction-fn ptr (z*-rec (car zlist) ram1) (z*-rec (car zlist) ram2)
                    size value (cdr zlist))
    (list ptr ram1 ram2 size value)))

(defthm rx-rec-over-z*-disjoint
  (implies (disjoint-list (blk-rec ptr off size) zlist)
           (equal (rx-rec ptr off size (z* zlist ram))
                  (rx-rec ptr off size ram)))
  :hints (("Goal" :in-theory (enable z*-reduction))))

(in-theory (disable bag::disjoint-list-reduction ;bzo why?
                    ))
;;
;; getx/sets, gets/sets
;;

(defun missing-key (key)
  (update-slot nil :name key :type :int :skel (skel 0 nil)))

(defthm slot-p-missing-key
  (slot-p (missing-key key)))

(in-theory (disable missing-key (missing-key)))

(defun get-slot (key spec)
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (if (equal key (slot-name slot))
                slot
              (get-slot key (cdr spec)))
          (missing-key key)))
    (missing-key key)))

(defun update-slot-value (value slot)
  (let ((size (slot-size slot)))
    (update-slot slot :val (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                  value))))

(defun update-slot-skel (skel slot)
  (update-slot slot :skel skel))

(defun set-slot-skel (key value skel)
  (if (consp skel)
      (let ((slot (car skel)))
        (if (slot-p slot)
            (if (equal key (slot-name slot))
                (cons (update-slot-skel value slot)
                      (cdr skel))
              (cons slot
                    (set-slot-skel key value (cdr skel))))
          (cons (missing-key key) skel)))
    (cons (missing-key key) skel)))

(defun set-slot-value (key value skel)
  (if (consp skel)
      (let ((slot (car skel)))
        (if (slot-p slot)
            (if (equal key (slot-name slot))
                (cons (update-slot-value value slot)
                      (cdr skel))
              (cons slot
                    (set-slot-value key value (cdr skel))))
          (cons (missing-key key) skel)))
    (cons (missing-key key) skel)))

(defun syntax-offset (woff wbase wptr rptr)
  (declare (type t woff wbase wptr rptr))
  (if (and (consp wptr)
           (equal (car wptr) 'binary-+)
           (consp (cdr wptr))
           (consp (cddr wptr))
           (equal (caddr wptr) rptr))
      `((,woff  . ,(cadr wptr))
        (,wbase . ,rptr))
    (if (equal wptr rptr)
        `((,woff  . (quote 0))
          (,wbase . ,rptr))
      nil)))

(defthmd unfixed-size-rx
  (implies (syntaxp (syntax-unfixed-size rsize))
           (equal (rx rsize rptr ram)
                  (rx (fix-size rsize) rptr ram)))
  :hints (("goal" :in-theory (enable rx))))

;move
(defthm unfixed-size-rx-constant-version
  (implies (syntaxp (and (quotep rsize)
                         (syntax-unfixed-size rsize)))
           (equal (rx rsize rptr ram)
                  (rx (fix-size rsize) rptr ram)))
  :hints (("goal" :use (:instance unfixed-size-rx)
           :in-theory (disable  unfixed-size-rx))))

(defthmd unfixed-size-wx
  (implies (syntaxp (syntax-unfixed-size wsize))
           (equal (wx wsize wptr value ram)
                  (wx (fix-size wsize) wptr value ram)))
  :hints (("goal" :in-theory (enable wx))))

(defthm split-blk-h*-spec
  (equal (f*-spec fop ptr (v0 (split-blk (h*-spec hop spec))))
         (f*-spec fop ptr (v0 (split-blk spec))))
  :hints (("goal" ;:induct (len spec) :in-theory (enable len)
           )))

(defthm f*-spec-g*-spec-v0-split-blk
  (equal (f*-spec fop fptr (g*-spec gop gptr (v0 (split-blk spec)) ram))
         (f*-spec fop fptr (v0 (split-blk spec))))
  :hints (("goal" :induct (split-blk spec))))


;; ==========================================
;;
;; deeper perm/unique/remove-list meta-rules
;;
;; ==========================================


(defun bind-fn-template-args (temp args)
  (declare (type t temp args))
  (if (consp temp)
      (if (consp args)
          (if (consp (car temp))
              (if (and (consp (car args))
                       (equal (caar temp) (caar args)))
                  (met ((hit alist) (bind-fn-template-args (cdar temp) (cdar args)))
                       (if hit
                           (met ((hit rst) (bind-fn-template-args (cdr temp) (cdr args)))
                                (if hit
                                    (mv hit (append alist rst))
                                  (mv nil nil)))
                         (mv nil nil)))
                (mv nil nil))
            (met ((hit alist) (bind-fn-template-args (cdr temp) (cdr args)))
                 (if hit
                     (mv hit (cons (cons (car temp) (car args)) alist))
                   (mv nil nil))))
        (mv nil nil))
    (mv t nil)))

(defun find-fn-template-args-rec (fn args term)
  (declare (type t fn args term))
  (and (consp term)
       (or (and (consp (car term))
                (and (equal (caar term) fn)
                     (met ((hit alist) (bind-fn-template-args args (cdar term)))
                          (and hit alist)))
                (find-fn-template-args-rec fn args (cdar term)))
           (find-fn-template-args-rec fn args (cdr term)))))

(defun find-fn-template-args (fncall term)
  (declare (type t fncall term))
  (and (consp term)
       (consp fncall)
       (or (and (equal (car term) (car fncall))
                (met ((hit alist) (bind-fn-template-args (cdr fncall) (cdr term)))
                     (and hit alist)))
           (find-fn-template-args-rec (car fncall) (cdr fncall) (cdr term)))))

(defun template-keys (template)
  (declare (type t template))
  (if (consp template)
      (if (consp (car template))
          (append (template-keys (cdar template))
                  (template-keys (cdr template)))
        (cons (car template) (template-keys (cdr template))))
    nil))

(defun ptr! (op)
  (if (whichtype (op-which op) :ptr)
      (update-op op :which :ptr)
    (update-op op :which :nil)))

(defun val! (op)
  (if (whichtype (op-which op) :val)
      (update-op op :which :val)
    (update-op op :which :nil)))

(defun f*-vp (fop fptr spec)
  (append (f*-spec (val! fop) fptr spec)
          (f*-spec (ptr! fop) fptr spec)))


;;
;; We might want to define a meta-unique as well to feed this
;; function.
;;


(defun concrete-pv (which)
  (declare (type t which))
  (and (consp which)
       (consp (cdr which))
       (if (equal (car which) 'quote)
           (let ((which (cadr which)))
             (or (equal which ':nil)
                 (equal which ':ptr)
                 (equal which ':val)))
         (not (equal (car which) 'op-which)))))

(defthmd f*-spec-vp-perm
  (implies
   (and
    (equal which (op-which fop))
    (syntaxp (not (concrete-pv which))))
   (perm (f*-spec fop fptr spec)
         (f*-vp fop fptr spec)))
  :hints (("goal" :induct (f*-spec fop fptr spec)
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable ;acl2::perm-free-substitution
                       ))))



(defthm g*-spec-v0-split-blk-of-wx-helper
  (implies
   (and
    (equal (op-how gop) :x)
    (equal (op-which gop) :val)
    (equal wbase base)
    (equal wptr (+ (ifix woff) (ifix wbase)))

    (unique (flat (f*-spec (update-op gop :which :all) base (v0 (split-blk spec)))))

    (memberp (sblk wsize (+<> woff wbase))
             (f*-spec gop base (v0 (split-blk spec))))

    (subbagp (sblk wsize (+<> woff wbase))
             (flat (f*-spec gop base (v0 (split-blk spec)))))

    )
   (equal (g*-spec gop base (v0 (split-blk spec)) (wx wsize wptr value ram))
          (wv wsize woff wbase (acl2::loghead (gacc::fix-size wsize) ;wfixn 8 wsize
                                      value)
              (g*-spec gop base (v0 (split-blk spec)) ram))))
  :otf-flg t
  :rule-classes nil
  :hints (("goal" :induct (len spec)
           :do-not '(generalize ;preprocess
                                eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :in-theory (e/d (open-wv
                            ;len
                            bag::flat-of-cons
;                            (:REWRITE ACL2::DISJOINT-COMMUTATIVE)
;                           (:REWRITE ACL2::MEMBERP-COMPUTATION)
                            (:REWRITE BAG::UNIQUE-of-APPEND)
                            bag::disjoint-of-append-one
                            bag::disjoint-of-append-two
                            LIST::memberp-of-cons
                            bag::disjoint-of-flat-helper-2
                            bag::disjoint-of-flat-helper
                            BAG::SUBBAGP-MEANS-RARELY-DISJOINT
                            BAG::SUBBAGP-MEANS-RARELY-DISJOINT-two
                            g*-spec-over-wx
                            f*-spec-vp-perm
;                            unfixed-size-wfixn
                            unfixed-size-rx
                            unfixed-size-wx
                            )
                           (fix-slot
                            slot-p
                            ;;whichtype
                            ;;START-OF-F*-SPEC
                            ;;wfixn-of-fix-size
                            ;;subbagp-membership-fwd
                            ;;subbagp-membership-free
                            ;;bag::memberp-implies-subbagp-flat
                            zz-wv-introduction)))))

(defthm rv-over-g*-spec-helper
  (implies
   (and
    (memberp (sblk wsize (+<> woff base))
             (f*-spec gop base (v0 (split-blk spec))))
    (subbagp (sblk wsize (+<> woff base))
             (flat (f*-spec gop base (v0 (split-blk spec)))))
    (unique (flat (f*-spec (update-op gop :which :all) base (v0 (split-blk spec)))))
    )
   (equal (rv wsize woff base (g*-spec gop base spec ram))
          (rx wsize (+<> woff base) ram)))
  :rule-classes nil
  :hints (("goal" :induct (len spec)
           :do-not '(generalize preprocess
                                eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :in-theory (e/d (bag::flat-of-cons
                            bag::disjoint-of-append-one
                            bag::disjoint-of-append-two
                            LIST::memberp-of-cons
                            bag::disjoint-of-flat-helper-2
                            bag::unique-of-append
                            F*-SPEC-VP-PERM
                            UNFIXED-SIZE-RX
;                                          UNFIXED-SIZE-WFIXN
                            LIST::MEMBERP-of-APPEND
                            BAG::MEMBERP-SUBBAGP
;                                           BAG::NOT-MEMBERP-OF-CDR-CHEAP
                            BAG::SUBBAGP-IMPLIES-SUBBAGP-APPEND-CAR
                            )
                           ( ;wfixn-of-fix-size
                            ;;ptr!
                            ;;F*-SPEC-VP-PERM
                            numwhich
                            numtype
                            op-base
                            )))))

;(local (in-theory (disable wfixn-of-fix-size)));bzo

;; Of course, we could have faster (evaluating) versions of these
;; combinations of functions that would improve proof times ..

(defthm g*-spec-v0-split-blk-of-wx
  (implies
   (and
    (equal (op-how gop) :x)
    (equal (op-which gop) :val)
    (bind-free (syntax-offset 'woff 'wbase wptr base) (woff wbase))
    (equal wbase base)
    (equal wptr (+<> woff wbase))
    (memberp (sblk wsize (+<> woff wbase))
            (f*-spec (update-op gop :which :val) base (v0 (split-blk spec))))
    (unique (flat (f*-spec (update-op gop :which :all) base (v0 (split-blk spec)))))
    )
   (equal (g*-spec gop base (v0 (split-blk spec)) (wx wsize wptr value ram))
          (wv wsize woff wbase (acl2::loghead (gacc::fix-size wsize) ;wfixn 8 wsize
                                              value)
              (g*-spec gop base (v0 (split-blk spec)) ram))))
  :hints (("goal" :use (:instance g*-spec-v0-split-blk-of-wx-helper)
           :in-theory (e/d (;unfixed-size-wfixn
                            unfixed-size-rx
                            unfixed-size-wx
                            f*-spec-vp-perm)
                           (zz-wv-introduction)))))

(defthm rv-over-g*-spec
   (implies
    (and
     (memberp (sblk wsize (+<> woff base))
             (f*-spec gop base (v0 (split-blk spec))))
     (unique (flat (f*-spec (update-op gop :which :all) base (v0 (split-blk spec)))))
     )
    (equal (rv wsize woff base (g*-spec gop base spec ram))
           (rx wsize (+<> woff base) ram)))
   :hints (("goal" :use (:instance rv-over-g*-spec-helper)
            :in-theory `(bag::subbagp-membership-fwd f*-spec-vp-perm))))

;;
;; Next for GACC is the Z* stuff for s* .. should be fun.
;;

(defthm z*-of-s*
  (implies
   (any-subbagp (flat (f*-spec sop sptr spec)) list)
   (equal (z* list (s*-spec sop sptr spec ram))
          (z* list ram)))
  :hints (("Goal" :in-theory (enable flat))))

(defthm z*-nil-reduction
  (equal (z* '(nil) ram) ram))

(defthm z*-list-append-reduction
  (equal (z* (list (append x y)) ram)
         (z* (list x y) ram))
  :hints (("goal" :in-theory (enable z*-reduction flat))))


;;
;; This is an example of how to split/join
;;

(defun split-list (list)
  (if (consp list)
      (let ((entry (car list)))
        (if (consp entry)
            (cons (car entry)
                  (append (split-list (cdr entry))
                          (split-list (cdr list))))
          (cons entry
                (split-list (cdr list)))))
    list))

(defun join-list (list flat)
  (if (and (consp list) (consp flat))
      (let ((entry (car list))
            (line  (car flat))
            (flat  (cdr flat)))
        (if (consp entry)
            (met ((cdrline flat hit1) (join-list (cdr entry) flat))
                 (met ((list flat hit2) (join-list (cdr list) flat))
                      (mv (cons (cons line cdrline) list) flat (and hit1 hit2))))
          (met ((list flat hit) (join-list (cdr list) flat))
               (mv (cons line list) flat hit))))
    (mv list flat (not (consp list)))))

(defthm open-join-list
  (and
   (implies
    (consp list)
    (equal (join-list list flat)
           (if (and (consp list) (consp flat))
      (let ((entry (car list))
            (line  (car flat))
            (flat  (cdr flat)))
        (if (consp entry)
            (met ((cdrline flat hit1) (join-list (cdr entry) flat))
                 (met ((list flat hit2) (join-list (cdr list) flat))
                      (mv (cons (cons line cdrline) list) flat (and hit1 hit2))))
          (met ((list flat hit) (join-list (cdr list) flat))
               (mv (cons line list) flat hit))))
    (mv list flat (not (consp list))))))
   (implies
    (not (consp list))
    (equal (join-list list flat) (mv list flat (not (consp list)))))
   (implies
    (not (consp flat))
    (equal (join-list list flat) (mv list flat (not (consp list)))))))


(defthm join-list-append-reduction
  (implies
   (v2 (join-list list x))
   (and (v2 (join-list list (append x y)))
        (equal (v0 (join-list list (append x y)))
               (v0 (join-list list x)))
        (equal (v1 (join-list list (append x y)))
               (append (v1 (join-list list x)) y))))
  :hints (("goal" :in-theory (enable default-car default-cdr))))

(defthm join-list-split-list
  (and (v2 (join-list list (split-list list)))
       (equal (v0 (join-list list (split-list list)))
              list)
       (not (consp (v1 (join-list list (split-list list))))))
  :hints (("goal" :induct (split-list list))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
                         :in-theory (enable binary-append)
                         :do-not-induct t))))

;;
;; Here is the real thing ..
;;

(defun f*-rec (spec)
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((size (slot-size slot))
                  (off  (slot-off  slot)))
              (cons (sblk size off)
                    (f*-rec (cdr spec))))
          (f*-rec (cdr spec))))
    nil))

(defun s*-rec (spec ram)
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((off  (slot-off  slot))
                  (size (slot-size slot))
                  (value (slot-val slot)))
              (let ((ram (wx size off value ram)))
                (s*-rec (cdr spec) ram)))
          (s*-rec (cdr spec) ram)))
    ram))

(defun g*-rec (spec ram)
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((off   (slot-off  slot))
                  (size  (slot-size slot)))
              (cons (update-slot slot :val (rx size off ram))
                    (g*-rec (cdr spec) ram)))
          (cons slot
                (g*-rec (cdr spec) ram))))
    spec))

(defthm true-listp-g*-rec
  (equal (true-listp (g*-rec rec ram))
         (true-listp rec)))

(defthm len-g*-rec
  (equal (len (g*-rec rec ram))
         (len rec)))

(defthm g*-rec-append
  (equal (g*-rec (append x y) ram)
         (append (g*-rec x ram) (g*-rec y ram))))

(defun spec->rec (op ptr spec)
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how op)))
              (let ((off  (slot-off  slot))
                    (size (slot-size slot))
                    (type (slot-type slot))
                    (skel (slot-skel slot))
                    (value (slot-val slot)))
                (let ((read value))
                  (let ((base (skel-base skel)))
                    (let ((base (if (ptr? type) (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                       (op-base h type base read))
                                  base)))
                      (let ((slot (update-slot slot
                                               :val (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                           value)
                                               :off (+<> off ptr)
                                               :skel (skel base nil))))
                        (let ((blk (if (whichtype w type) (list slot) nil)))
                          (let ((rec (if (ptr? type) (spec->rec op base (skel-spec skel)) nil)))
                            (append blk
                                    rec
                                    (spec->rec op ptr (cdr spec)))))))))))
          (spec->rec op ptr (cdr spec))))
    nil))

(defthm open-spec->rec
  (implies
   (consp spec)
   (equal (spec->rec op ptr spec)
          (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how op)))
              (let ((off  (slot-off  slot))
                    (size (slot-size slot))
                    (type (slot-type slot))
                    (skel (slot-skel slot))
                    (value (slot-val slot)))
                (let ((read value))
                  (let ((base (skel-base skel)))
                    (let ((base (if (ptr? type) (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                       (op-base h type base read))
                                  base)))
                      (let ((slot (update-slot slot
                                               :val (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                           value)
                                               :off (+<> off ptr)
                                               :skel (skel base nil))))
                        (let ((blk (if (whichtype w type) (list slot) nil)))
                          (let ((rec (if (ptr? type) (spec->rec op base (skel-spec skel)) nil)))
                            (append blk
                                    rec
                                    (spec->rec op ptr (cdr spec)))))))))))
          (spec->rec op ptr (cdr spec))))))
  :hints (("goal" :in-theory '(spec->rec))))

(defthm true-listp-spec->rec
  (true-listp (spec->rec op ptr spec)))

(defthm atomic-spec->rec-replacement
  (implies
   (syntaxp (symbolp op))
   (equal (spec->rec op ptr spec)
          (spec->rec (xop op) ptr spec))))

(defthm len-spec->rec-reduction
  (implies
   (syntaxp (not (quotep ptr)))
   (equal (len (spec->rec op ptr spec))
          (len (spec->rec op 0 spec)))))

(defthm len-spec->rec-g*-spec-reduction
  (equal (len (spec->rec op ptr (g*-spec op ptr spec ram)))
         (len (spec->rec op ptr spec)))
  :hints (("goal" :in-theory (enable len))))

(defthm len-spec->rec-h*-spec-reduction
  (equal (len (spec->rec op ptr (h*-spec op spec)))
         (len (spec->rec op ptr spec)))
  :hints (("goal" :in-theory (enable len))))

(defthm s*-rec-append
  (equal (s*-rec (append x y) ram)
         (s*-rec y (s*-rec x ram)))
  :hints (("goal" :in-theory (enable binary-append)
           :induct (s*-rec x ram))))

(defthmd s*-spec-s*-rec-reduction
  (equal (s*-spec op ptr spec ram)
         (s*-rec (spec->rec op ptr spec) ram)))

(defun rec->spec (op spec rec)
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how   op)))
              (let ((size  (slot-size slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot))
                    (value (slot-val  slot))
                    )
                (if (and (whichtype w type) (not (consp rec))) (mv spec rec nil)
                  (let ((read (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                             (slot-val (car rec))))
                        (rec  (if (whichtype w type) (cdr rec) rec)))
                    (let ((base (if (ptr? type) (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                               (skel-base skel)) (skel-base skel))))
                      (let ((value (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                          (if (whichtype w type) read value))))
                        (let ((base (op-base h type base value)))
                          (let ((skel-spec (skel-spec skel)))
                            (met ((skel-spec rec hit1) (if (ptr? type)
                                                           (rec->spec op skel-spec rec)
                                                         (mv skel-spec rec t)))
                                 (let ((skel (skel base skel-spec)))
                                   (met ((spec rec hit2) (rec->spec op (cdr spec) rec))
                                        (mv (cons (update-slot slot :val value :skel skel) spec)
                                            rec (and hit1 hit2)))))))))))))
          (met ((spec rec hit) (rec->spec op (cdr spec) rec))
               (mv (cons slot spec) rec hit))))
    (mv spec rec t)))

(defthm open-rec->spec
  (and
   (implies
    (consp spec)
    (equal (rec->spec op spec rec)
           (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how   op)))
              (let ((size  (slot-size slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot))
                    (value (slot-val  slot))
                    )
                (if (and (whichtype w type) (not (consp rec))) (mv spec rec nil)
                  (let ((read (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                             (slot-val (car rec))))
                        (rec  (if (whichtype w type) (cdr rec) rec)))
                    (let ((base (if (ptr? type) (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                               (skel-base skel)) (skel-base skel))))
                      (let ((value (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                  (if (whichtype w type) read value))))
                        (let ((base (op-base h type base value)))
                          (let ((skel-spec (skel-spec skel)))
                            (met ((skel-spec rec hit1) (if (ptr? type)
                                                           (rec->spec op skel-spec rec)
                                                         (mv skel-spec rec t)))
                                 (let ((skel (skel base skel-spec)))
                                   (met ((spec rec hit2) (rec->spec op (cdr spec) rec))
                                        (mv (cons (update-slot slot :val value :skel skel) spec)
                                            rec (and hit1 hit2)))))))))))))
          (met ((spec rec hit) (rec->spec op (cdr spec) rec))
               (mv (cons slot spec) rec hit))))
    (mv spec rec t))))
   (implies
    (not (consp spec))
    (equal (rec->spec op spec rec) (mv spec rec t)))
   )
  :hints (("goal" :in-theory '(rec->spec))))

(defthm atomic-rec->spec-replacement
  (implies (syntaxp (symbolp op))
           (equal (rec->spec op spec rec)
                  (rec->spec (xop op) spec rec)))
  :hints (("Goal" :in-theory (disable numwhich
                                      numtype
                                      op-base
                                      ptr?
                                      WHICHTYPE
                                      slot-p
                                      SLOT-EXTENSIONALITY!!
                                      SKEL-EXTENSIONALITY
                                      SKEL-EXTENSIONALITY!
                                      SLOT-EXTENSIONALITY
                                      ))))

(in-theory (disable (:definition rec->spec)))

(defthm rec->spec-append-reduction
  (implies (v2 (rec->spec op spec x))
           (and (v2 (rec->spec op spec (append x y)))
                (equal (v0 (rec->spec op spec (append x y)))
                       (v0 (rec->spec op spec x)))
                (equal (v1 (rec->spec op spec (append x y)))
                       (append (v1 (rec->spec op spec x)) y))))
  :hints (("goal" :do-not '(generalize eliminate-destructors
                                       fertilize eliminate-irrelevance)
           :in-theory (e/d (LIST::CDR-APPEND
                            LIST::CAR-APPEND
                                        ;binary-append
                            SLOT-EXTENSIONALITY
                            SKEL-EXTENSIONALITY
                            )
                           (;for efficiency:
                            ATOMIC-REC->SPEC-REPLACEMENT
                            BINARY-APPEND
                            SLOT-P
                            skel-extensionality!
                            SLOT-EXTENSIONALITY!!
                            default-car
                            numwhich
                            numtype
                            ptr?
                            op-base
                            whichtype
                            ;OPEN-REC->SPEC
                            ;; non-integer-size-wfixn
                            ))
           :do-not-induct t
           :induct (rec->spec op spec x))
          ))

(defun not-which (op)
  (let ((which (op-which op)))
    (let ((nwhich (numwhich which)))
      (let ((not-nwhich (logxor #x3 nwhich)))
        (update-op op :which (whichnum not-nwhich))))))

(defthm op-base-of-op-base
  (equal (OP-BASE h
                  type
                  (OP-BASE h
                           type
                           base
                           valu)
                  valu)
         (OP-BASE h
                  type
                  base
                  valu)))

(defthm rec->spec-of-spec->rec-h*-spec-helper
  (let ((template (h*-spec (not-which op) spec)))
    (and (v2 (rec->spec op template (spec->rec op ptr spec)))
         (equal (v0 (rec->spec op template (spec->rec op ptr spec)))
                (h*-spec (update-op op :which :all) spec))
         (not (consp (v1 (rec->spec op template (spec->rec op ptr spec)))))))
  :rule-classes nil
  :hints (("goal" :induct (spec->rec op ptr spec)
           :do-not '(generalize eliminate-destructors
                                fertilize eliminate-irrelevance)
           :in-theory (e/d (binary-append) (numwhich
                                            numtype
                                            op-base
                                            ;;whichtype
                                            ;;ptr?
                                            ;;not-which
                                            whichnum
                                            slot-p
                                            ))
           :do-not-induct t)
          ))

(defthm rec->spec-of-spec->rec-h*-spec-raw
  (and (v2 (rec->spec op spec (spec->rec op ptr spec)))
       (equal (v0 (rec->spec op spec (spec->rec op ptr spec)))
              (h*-spec (update-op op :which :all) spec))
       (not (consp (v1 (rec->spec op spec (spec->rec op ptr spec))))))
  :hints (("goal" :induct (spec->rec op ptr spec))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors
                                      fertilize eliminate-irrelevance)
                         :in-theory (e/d (binary-append)
                                         (numwhich numtype
                                                   SLOT-EXTENSIONALITY
                                                   ;ptr?
                                                   op-base
                                                   whichtype
                                                   slot-p
                                                   ))
                         :do-not-induct t))))


(defthm rec->spec-of-spec->rec-h*-spec
  (implies
   (equal template (h*-spec (not-which op) spec))
   (and (v2 (rec->spec op template (spec->rec op ptr spec)))
        (equal (v0 (rec->spec op template (spec->rec op ptr spec)))
               (h*-spec (update-op op :which :all) spec))
        (not (consp (v1 (rec->spec op template (spec->rec op ptr spec)))))))
  :hints (("goal" :in-theory nil
           :use (:instance rec->spec-of-spec->rec-h*-spec-helper))))

(defthmd rec->spec-h*-spec-not-which-introduction-1
  (implies (and (x? op)
                (syntaxp (not (and (consp spec) (equal (car spec) 'h*-spec)))))
           (implies
            (v2 (rec->spec op (h*-spec (not-which op) spec) rec))
            (equal (v1 (rec->spec op spec rec))
                   (v1 (rec->spec op (h*-spec (not-which op) spec) rec)))))
  :otf-flg t
  :hints (("goal" :do-not '(generalize preprocess eliminate-destructors
                                       fertilize eliminate-irrelevance)
           :in-theory (e/d (g? binary-append)
                           (SKEL-EXTENSIONALITY!
                            ;;GACC::ATOMIC-REC->SPEC-REPLACEMENT ;made things worse...
                            numwhich
                            op-base
                            slot-p
                            ;; numtype
                            whichnum
                            whichtype
                            x?
                            ptr?
                            not-which
                            ))
           :do-not-induct t
           :induct (rec->spec op spec rec))
          ))

(defthmd rec->spec-h*-spec-not-which-introduction-2
  (implies (and (x? op)
                (syntaxp (not (and (consp spec) (equal (car spec) 'h*-spec)))))
           (implies
            (v2 (rec->spec op (h*-spec (not-which op) spec) rec))
            (equal (v0 (rec->spec op spec rec))
                   (v0 (rec->spec op (h*-spec (not-which op) spec) rec)))))
;  :otf-flg t
  :hints (("goal" :do-not '(generalize preprocess eliminate-destructors
                                       fertilize eliminate-irrelevance)
           :in-theory (e/d (g? rec->spec-h*-spec-not-which-introduction-1)
                           (SKEL-EXTENSIONALITY!
                            SLOT-EXTENSIONALITY!!
                            SLOT-EXTENSIONALITY
                            ;;GACC::ATOMIC-REC->SPEC-REPLACEMENT ;made things worse...
;                            numwhich
;                            op-base
                            ;; numtype
 ;                           whichnum
                            ;;whichtype
                            ;; ;x?
              ;              ptr?
               ;             not-which
                            ))
           :do-not-induct t
           :induct (rec->spec op spec rec))
          ))

(defthmd rec->spec-h*-spec-not-which-introduction-3
  (implies (and (x? op)
                (syntaxp (not (and (consp spec) (equal (car spec) 'h*-spec)))))
           (equal (v2 (rec->spec op spec rec))
                  (v2 (rec->spec op (h*-spec (not-which op) spec) rec))))
  :hints (("goal" :do-not '(generalize preprocess eliminate-destructors
                                       fertilize eliminate-irrelevance)
           :in-theory (e/d (g? rec->spec-h*-spec-not-which-introduction-1)
                           (SKEL-EXTENSIONALITY!
                            ;;GACC::ATOMIC-REC->SPEC-REPLACEMENT ;made things worse...
                            numwhich
                            numtype
                            whichnum
                             op-base
                            ;; whichtype
                            ;;x?
                            ptr?
                            ;; not-which
                            ))
           :do-not-induct t
           :induct (rec->spec op spec rec))
          ))

(defun rec->spec-of-spec->rec-hyp (op template spec)
  (equal (h*-spec (not-which op) template)
         (h*-spec (not-which op) spec)))

(defthmd rec->spec-of-spec->rec
  (implies
   (and
    (x? op)
    (force (rec->spec-of-spec->rec-hyp op template spec)))
   (equal (v0 (rec->spec op template (spec->rec op ptr spec)))
          (h*-spec (update-op op :which :all) spec)))
  :hints (("goal" :in-theory (enable rec->spec-of-spec->rec-hyp
                                     rec->spec-h*-spec-not-which-introduction-1
                                     rec->spec-h*-spec-not-which-introduction-2
                                     rec->spec-h*-spec-not-which-introduction-3
                                     rec->spec-of-spec->rec-h*-spec
                                     ))))



(defthm g*-rec-g*-spec-commute
  (implies
   (x? op)
   (equal (g*-rec (spec->rec op ptr spec) ram)
          (spec->rec op ptr (g*-spec op ptr spec ram))))
  :hints (("goal" :in-theory (disable; WFIXN-DOES-NOTHING-REWRITE
                                      ;UNFIXED-SIZE-WFIXN-0-TO-8 ;why?
                                      )
           :induct (g*-spec op ptr spec ram))))

(defthm g*-spec-default-which
  (implies
   (and (syntaxp (not (quotep w)))
        (not (equal w :all))
        (not (equal w :ptr))
        (not (equal w :nil)))
   (equal (g*-spec (op w h) ptr spec ram)
          (g*-spec (op :val h) ptr spec ram)))
  :hints (("Goal" :in-theory (disable ACL2::LOGAND-EXPT-CONSTANT-VERSION ;why?
                                      ))))

(defthmd g*-spec-g*-rec-reduction
  (implies
   (x? op)
   (equal (g*-spec op ptr spec ram)
          (v0 (rec->spec op spec (g*-rec (spec->rec op ptr spec) ram)))))
  :hints (("goal" :in-theory (enable rec->spec-of-spec->rec acl2::logbit))))

(defthm f*-rec-append
  (equal (f*-rec (append x y))
         (append (f*-rec x) (f*-rec y))))

(defthmd f*-spec-f*-rec-reduction
  (equal (f*-spec op ptr spec)
         (f*-rec (spec->rec op ptr spec))))

(defun h*-rec (rec)
  (if (consp rec)
      (let ((slot (car rec)))
        (if (slot-p slot)
            (let ((size  (slot-size slot))
                  (value (slot-val  slot)))
              (let ((slot (update-slot slot :val (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                                value))))
                (cons slot (h*-rec (cdr rec)))))
          (cons slot
                (h*-rec (cdr rec)))))
    rec))

(defthm true-listp-h*-rec
  (equal (true-listp (h*-rec rec))
         (true-listp rec)))

(defthm len-h*-rec
  (equal (len (h*-rec rec))
         (len rec)))

(defthm h*-rec-append
  (equal (h*-rec (append x y))
         (append (h*-rec x) (h*-rec y))))

(defthm h*-spec-h*-spec-commute
  (implies
   (implies (g-op op) (optype op :ptr))
   (equal (h*-rec (spec->rec op ptr spec))
          (spec->rec op ptr (h*-spec op spec))))
  :hints (("goal" :in-theory (enable g?))))


;; ===============================================
;;
;; z* rules
;;
;; ===============================================

(in-theory (disable z*))

(defthm s*-rec-over-wx
  (implies
   (disjoint (sblk size off) (flat (f*-rec spec)))
   (equal (s*-rec spec (wx size off value ram))
          (wx size off value (s*-rec spec ram))))
  :hints (("goal" :in-theory (enable ;my-wx-over-wx
                                     flat))))

;; We are beginning to see a weakness in our representation. There
;; is no good reason for (f*-rec rec) to be unique in the following
;; theorem, except that it makes it convenient to prove the result.
;; Our use of s*-rec type functions should have gone all the way down
;; to rd/wr.  There should be generic r*/w* functions that take an
;; association list of _atomic_ addresses and updates/inserts that
;; list.  These association lists could then have been lifted into
;; rx/wx and, ultimately, into g*/s*.  The fact that rx/wx is our
;; atomic operation is a weakness in expressing the sorts of things
;; we want to say.


(defthm s*-rec-over-z*
  (implies
   (and
    (unique (flat (f*-rec rec)))
    (disjoint-list (flat (f*-rec rec)) zlist))
   (equal (z* zlist (s*-rec rec ram))
          (s*-rec rec (z* zlist ram))))
  :hints (("goal" :in-theory (enable
                              flat
                              z*-over-wx-commute
                              bag::disjoint-list-reduction
                              ))))


(defthm z*-s*-rec-introduction
  (implies (unique (flat (f*-rec rec)))
           (equal (equal ram1 (s*-rec rec ram2))
                  (and (equal (z* (list (flat (f*-rec rec))) ram1)
                              (z* (list (flat (f*-rec rec))) ram2))
                       (equal (g*-rec rec ram1)
                              (h*-rec rec)))))
  :hints (("Goal" :in-theory (enable flat))))

(defthmd z*-cons-reduction
  (implies
   (syntaxp (not (quotep b)))
   (equal (z* (cons a b) ram)
          (z* b (z* (list a) ram))))
  :hints (("goal" :in-theory (enable z*))))

(defthm z*-commute
  (equal (z* a (z* b ram))
         (z* b (z* a ram)))
  :hints (("goal" :in-theory (enable z*-reduction)))
  :rule-classes ((:rewrite :loop-stopper ((a b)))))

(defthm g*-rec-over-z*
  (implies
   (disjoint-list (flat (f*-rec rec)) zlist)
   (equal (g*-rec rec (z* zlist ram))
          (g*-rec rec ram)))
  :hints (("goal" :in-theory (enable flat bag::disjoint-list-reduction))))


(defthm z*-s*-rec-induction
  (implies (and (unique (flat (f*-rec rec)))
                (disjoint-list (flat (f*-rec rec)) zlist))
           (equal (equal (z* zlist (s*-rec rec ram1))
                         (z* zlist ram2))
                  (and (equal (z* (cons (flat (f*-rec rec)) zlist) ram1)
                              (z* (cons (flat (f*-rec rec)) zlist) ram2))
                       (equal (h*-rec rec)
                              (g*-rec rec ram2)))))
  :hints (("goal" :in-theory `(g*-rec-over-z*
                               z*-commute
                               z*-cons-reduction
                               s*-rec-over-z*
                               z*-s*-rec-introduction))))

(defthm z*-s*-rec-elimination
  (implies
   (and
    (unique (flat (f*-rec rec)))
    (any-subbagp (flat (f*-rec rec)) zlist))
   (equal (z* zlist (s*-rec rec ram))
          (z* zlist ram))))

(defthmd g*-spec-h*-spec-equality-reduction
  (implies
   (x? op)
   (equal (equal (g*-spec op ptr spec ram)
                 (h*-spec (op :all :x) spec))
          (equal (g*-rec (spec->rec op ptr spec) ram)
                 (h*-rec (spec->rec op ptr spec)))))
  :hints (("goal" :induct (spec->rec op ptr spec) :in-theory (disable
                                                              ;UNFIXED-SIZE-WFIXN-0-TO-8 ;bzo think about this
                                                              ))))

(defthm z*-s*-spec-introduction
  (implies
   (and
    (x? op)
    (unique (flat (f*-spec op ptr spec))))
   (equal (equal ram1 (s*-spec op ptr spec ram2))
          (and (equal (z* (list (flat (f*-spec op ptr spec))) ram1)
                      (z* (list (flat (f*-spec op ptr spec))) ram2))
               (equal (g*-spec op ptr spec ram1)
                      (h*-spec (op :all :x) spec)))))
  :hints (("goal" :in-theory '(z*-s*-rec-introduction
                               s*-spec-s*-rec-reduction
                               f*-spec-f*-rec-reduction
                               g*-spec-h*-spec-equality-reduction
                               ))))

(defthm z*-s*-spec-induction
  (implies
   (and
    (x? op)
    (unique (flat (f*-spec op ptr spec)))
    (disjoint-list (flat (f*-spec op ptr spec)) zlist))
   (equal (equal (z* zlist (s*-spec op ptr spec ram1))
                      (z* zlist ram2))
               (and (equal (z* (cons (flat (f*-spec op ptr spec)) zlist) ram1)
                           (z* (cons (flat (f*-spec op ptr spec)) zlist) ram2))
                    (equal (h*-spec (op :all :x) spec)
                           (g*-spec op ptr spec ram2)))))
  :hints (("goal" :in-theory '(z*-s*-rec-induction
                               s*-spec-s*-rec-reduction
                               f*-spec-f*-rec-reduction
                               g*-spec-h*-spec-equality-reduction
                               ))))


(defthm z*-s*-spec-elimination
  (implies
   (and
    (unique (flat (f*-spec op ptr spec)))
    (any-subbagp (flat (f*-spec op ptr spec)) zlist))
   (equal (z* zlist (s*-spec op ptr spec ram))
          (z* zlist ram)))
  :hints (("goal" :in-theory '(s*-spec-s*-rec-reduction
                               f*-spec-f*-rec-reduction
                               z*-s*-rec-elimination
                               ))))

(defthm s*-spec-over-z*
  (implies
   (and
    (unique (flat (f*-spec op ptr spec)))
    (disjoint-list (flat (f*-spec op ptr spec)) zlist))
   (equal (z* zlist (s*-spec op ptr spec ram))
          (s*-spec op ptr spec (z* zlist ram))))
  :hints (("goal" :in-theory '(s*-rec-over-z*
                               s*-spec-s*-rec-reduction
                               f*-spec-f*-rec-reduction
                               ))))

(defthm g*-spec-over-z*
  (implies
   (and
    (x? op)
    (disjoint-list (flat (f*-spec op ptr spec)) zlist))
   (equal (g*-spec op ptr spec (z* zlist ram))
          (g*-spec op ptr spec ram)))
  :hints (("goal" :in-theory '(g*-spec-g*-rec-reduction
                               f*-spec-f*-rec-reduction
                               g*-rec-over-z*
                               ))))

(defthm s*-list-over-z*
  (implies
   (and
    (x? op)
    (unique (flat (f*-list op spec)))
    (disjoint-list (flat (f*-list op spec)) zlist))
   (equal (z* zlist (s*-list op spec ram))
          (s*-list op spec (z* zlist ram))))
  :hints (("goal" :in-theory (e/d ((:induction s*-list)) (
                                                          ;(:META BAG::*META*-SUBBAGP-LIST)
                                                          ))
;           :do-not '(generalize eliminate-destructors)
           :induct (s*-list op spec ram))))

(defthm z*-s*-list-elimination
  (implies
   (and
    (unique (flat (f*-list op spec)))
    (any-subbagp (flat (f*-list op spec)) zlist))
   (equal (z* zlist (s*-list op spec ram))
          (z* zlist ram)))
  :hints (("goal" :in-theory (enable (:induction s*-list)))))


(defthm rs-of-h*-spec
  (implies
   (not (g-op op))
   (equal (rs size off base (h*-spec op spec))
          (skel (if (equal (op-how op) :z) 0
                  (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                 (skel-base (rs size off base spec))))
                (h*-spec op (skel-spec (rs size off base spec))))))
  :hints (("goal" :in-theory (enable g? ;unfixed-size-wfixn
                                     )
           :induct (rs size off base spec))))

(defthm zz-of-ws
  (implies
   (memberp (sblk wsize (+<> woff base)) slist)
   (equal (zz vlist slist base (ws wsize woff base v spec))
          (zz vlist slist base spec)))
  :hints (("goal" :in-theory (enable zs-over-ws zz))))

(defthm zz-of-wv
  (implies
   (memberp (sblk wsize (+<> woff base)) vlist)
   (equal (zz vlist slist base (wv wsize woff base v spec))
          (zz vlist slist base spec)))
  :hints (("goal" :in-theory (enable zv-over-wv zz))))

;;
;;
;; Spec type
;;
;;

(defun spec-type (spec type)
  (equal (h*-spec (op :nil :z) spec) type))

(defthm spec-type-nil-reduction
  (equal (spec-type list nil)
         (equal list nil))
  :hints (("goal" :in-theory (enable spec-type))))

(defthm spec-type-h*-spec-reduction
  (implies
   (and
    (equal hspec (h*-spec (op :nil :z) spec))
    (syntaxp (not (equal hspec spec)))
    )
   (equal (spec-type spec type)
          (spec-type (h*-spec (op :nil :z) spec) type)))
  :hints (("goal" :in-theory (enable spec-type))))

(defthm spec-type-free
  (implies
   (spec-type (h*-spec (op :nil :z) spec) type)
   (equal (h*-spec (op :nil :z) spec)
          type)))

(defthm spec-type-equality
  (implies
   (and
    (equal hspec (h*-spec (op :nil :z) spec))
    (syntaxp (equal hspec type))
    (equal hspec type)
    )
   (spec-type spec type)))

(in-theory (disable spec-type))

(defthm rv-of-wv-all
  (implies (memberp (sblk size (|+<>| off base))
                   (keys-spec :all base spec))
           (equal (rv size
                      off base (wv size off base value spec))
                  (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                 value
                         )))
  :hints (("goal" :in-theory nil
           :use ((:instance rv-of-wv (w :all))))))

;;
;; Some useful bind-free stuff ..
;;

(defun fn-instance-rec (arglist fname term)
  (declare (type t arglist fname term))
  (if (consp term)
      (if arglist
          (or (fn-instance-rec nil fname (car term))
              (fn-instance-rec t   fname (cdr term)))
        (let ((fn (car term)))
          (if (equal fn fname)
              (cdr term)
            (fn-instance-rec t fname (cdr term)))))
    nil))

(defun bind-keys (args term)
  (declare (type t args term))
  (if (and (consp args)
           (consp term))
      (cons (cons (car args) (car term))
            (bind-keys (cdr args) (cdr term)))
    nil))

(defun fn-instance-fn (fname args arglist term)
  (declare (type t fname args term))
  (let ((term (fn-instance-rec arglist fname term)))
    (bind-keys args term)))


(defun fn-instance-wrapper (fname args term hyps mfc acl2::state)
  (declare (xargs :stobjs (acl2::state)
                  :verify-guards t)
           (ignore acl2::state))
  (let ((hit (fn-instance-fn fname args nil term)))
    (or hit
        (and hyps
             (let ((hyps (acl2::mfc-clause mfc)))
               (fn-instance-fn fname args t hyps))))))

(defmacro fn-instance (fname args term &key (hyps 'nil))
  `(fn-instance-wrapper ,fname ,args ,term ,hyps acl2::mfc acl2::state))

(defmacro bind-fn-instance (fn term &key (hyps 'nil))
  `(bind-free (fn-instance (quote ,(car fn)) (quote ,(cdr fn)) ,term :hyps ,hyps) ,(cdr fn)))

(defmacro bind-fn-instance-equal (fn term &key (hyps 'nil))
  `(and (bind-fn-instance ,fn ,term :hyps ,hyps)
        (equal ,term ,fn)))

;(in-theory (disable acl2::LEN-REDUCTION))

(defun split-blk-fix-slot (slot)
  (if (slot-p slot)
      (let ((slot (fix-slot slot)))
        (let ((type (slot-type slot))
              (skel (slot-skel slot)))
          (if (ptr? type)
              (let ((base (skel-base skel)))
                (let ((slot (update-slot slot :skel (skel base nil))))
                  slot))
            slot)))
    slot))

(defthm v0-split-blk
  (equal (v0 (split-blk (cons slot list)))
         (cons (split-blk-fix-slot slot) (v0 (split-blk list)))))

(in-theory (disable open-split-blk))

(defthm h*-spec-wv-val
  (implies
   (and
    (not (optype hop :val))
    (not (memberp (sblk wsize (+<> woff base)) (keys-spec :ptr base spec))))
   (equal (h*-spec hop (wv wsize woff base value spec))
          (h*-spec hop spec)))
  :hints (("goal" :induct (wv wsize woff base value spec)
           :in-theory (enable open-split-blk open-wv memberp))))

(defthm h*-spec-wv-val-2
  (implies (and (not (optype hop :val))
                (equal v (h*-spec hop spec))
                (not (memberp (sblk wsize (|+<>| woff base))
                              (keys-spec :ptr base v))))
           (equal (h*-spec hop (wv wsize woff base value spec))
                  v))
  :hints (("goal" :in-theory '(h*-spec-wv-val split-blk-h*-spec))))

(in-theory
 (disable
  h*-spec-wv-val
  h*-spec-wv-val-2
  ))

(defthm f*-spec-h*-spec-introduction
  (implies
   (and
    (x? fop)
    (equal hspec (h*-spec (op :nil :x) spec))
    (syntaxp (not (equal hspec spec))))
   (equal (f*-spec fop base spec)
          (f*-spec fop base hspec)))
  :hints (("goal''" :induct (f*-spec fop base spec))))

(defthm f*-list-h*-list-introduction
  (implies
   (and
    (x? fop)
    (equal hlist (h*-list (op :nil :x) list))
    (syntaxp (not (equal hlist list))))
   (equal (f*-list fop list)
          (f*-list fop hlist)))
  :hints (("goal''" :induct (f*-list fop list))))

(in-theory
 (disable
  f*-spec-h*-spec-introduction
  f*-list-h*-list-introduction
  ))

(defthm f*-spec-h*-spec-reduction
  (implies
   (and
    (x? fop)
    (x? hop))
   (equal (f*-spec fop base (h*-spec hop spec))
          (f*-spec fop base spec))))

(theory-invariant
 (incompatible
  (:rewrite f*-spec-h*-spec-reduction)
  (:rewrite f*-spec-h*-spec-introduction)
  ))

(in-theory
 (disable
  g*-spec-default-which
  ))



;;
;; blog
;;

(defthm f*-spec-of-g*-spec
  (implies
   (and
    (x? fop)
    (equal (op-how gop) :x))
   (equal (f*-spec fop fptr (g*-spec gop gptr spec ram))
          (f*-spec fop fptr spec)))
  :hints (("goal" :induct (F*-G*-INDUCTION FOP FPTR GOP GPTR SPEC RAM))))

(defthm f*-list-of-g*-list
  (implies
   (and
    (x? fop)
    (equal (op-how gop) :x))
   (equal (f*-list fop (g*-list gop list ram))
          (f*-list fop list)))
  :hints (("goal" :induct (g*-list gop list ram)
           :in-theory (enable (:induction g*-list))
           )))


(defun rd-spec (list ram)
  (if (consp list)
      (cons (rd-list (car list) ram)
            (rd-spec (cdr list) ram))
    nil))

(defun wr-spec (list value ram)
  (if (and (consp list)
           (consp value))
      (let ((ram (wr-list (car list) (enlistw (len (car list)) (car value)) ram)))
        (wr-spec (cdr list) (cdr value) ram))
    ram))

(defun g*-rd (spec list)
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((value (wintlist (car list))))
              (cons (update-slot (car spec) :val value)
                    (g*-rd (cdr spec) (cdr list))))
          (cons slot
                (g*-rd (cdr spec) list))))
    spec))

(defun v*-rec (spec)
  (if (consp spec)
      (let ((slot (car spec)))
           (if (slot-p slot)
               (let ((size (slot-size slot))
                     (value (slot-val slot)))
                    (cons (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                         value)
                          (v*-rec (cdr spec))))
               (v*-rec (cdr spec))))
      nil))

(defthm s*-rec-reduction
  (equal (s*-rec spec ram)
         (wr-spec (f*-rec spec) (v*-rec spec) ram))
  :hints (("goal" :in-theory (e/d (WX-TO-WR-LIST-REDUCTION) (UNFIXED-SIZE-SBLK)))))

(defun list->rec (op list)
  (if (consp list)
      (let ((line (car list)))
        (if (line-p line)
            (let ((key  (line-key  line))
                  (skel (line-skel line)))
              (let ((base (op-base (op-how op) :ptr (skel-base skel) key)))
                (append (spec->rec op base (skel-spec skel))
                        (list->rec op (cdr list)))))
          (list->rec op (cdr list))))
    nil))

(defun rec->list (op list rec)
  (if (consp list)
      (let ((line (car list)))
        (if (line-p line)
            (let ((key  (line-key  line))
                  (skel (line-skel line)))
              (let ((base (op-base (op-how op) :ptr (skel-base skel) key)))
                (met ((spec rec hit) (rec->spec op (skel-spec skel) rec))
                     (if (not hit) (mv list rec nil)
                       (met ((list rec hit) (rec->list op (cdr list) rec))
                            (mv (cons (update-line line :skel (skel base spec))
                                      list)
                                rec
                                hit))))))
          (met ((list rec hit) (rec->list op (cdr list) rec))
               (mv (cons line list) rec hit))))
    (mv list rec t)))


(defthm open-rec->list
  (and
   (implies
    (consp list)
    (equal (rec->list op list rec)
           (let ((line (car list)))
             (if (line-p line)
                 (let ((key  (line-key  line))
                       (skel (line-skel line)))
                   (let ((base (op-base (op-how op) :ptr (skel-base skel) key)))
                     (met ((spec rec hit) (rec->spec op (skel-spec skel) rec))
                          (if (not hit) (mv list rec nil)
                            (met ((list rec hit) (rec->list op (cdr list) rec))
                                 (mv (cons (update-line line :skel (skel base spec))
                                           list)
                                     rec
                                     hit))))))
               (met ((list rec hit) (rec->list op (cdr list) rec))
                    (mv (cons line list) rec hit))))))
   (implies
    (not (consp list))
    (equal (rec->list op list rec)
           (mv list rec t))))
  :hints (("goal" :in-theory '(rec->list))))

(defthm atomic-rec->list-replacement
  (implies
   (syntaxp (symbolp op))
   (equal (rec->list op list rec)
          (rec->list (xop op) list rec))))

(defthm rec->list-append-reduction
  (implies
   (v2 (rec->list op list x))
   (and (v2 (rec->list op list (append x y)))
        (equal (v0 (rec->list op list (append x y)))
               (v0 (rec->list op list x)))
        (equal (v1 (rec->list op list (append x y)))
               (append (v1 (rec->list op list x)) y))))
  :hints (("goal" :induct (rec->list op list x))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors
                                      fertilize eliminate-irrelevance)
                         :in-theory (enable binary-append)
                         :do-not-induct t))))


(defthm rec->list-of-list->rec-h*-list-helper
  (let ((template (h*-list (not-which op) list)))
    (and (v2 (rec->list op template (list->rec op list)))
         (equal (v0 (rec->list op template (list->rec op list)))
                (h*-list (update-op op :which :all) list))
         (not (consp (v1 (rec->list op template (list->rec op list)))))))
  :rule-classes nil
  :hints (("goal" :induct (list->rec op list))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors
                                      fertilize eliminate-irrelevance)
                         :in-theory (enable binary-append)
                         :do-not-induct t))))

(defthm rec->list-of-list->rec-h*-list-raw
  (and (v2 (rec->list op list (list->rec op list)))
       (equal (v0 (rec->list op list (list->rec op list)))
              (h*-list (update-op op :which :all) list))
       (not (consp (v1 (rec->list op list (list->rec op list))))))
  :hints (("goal" :induct (list->rec op list))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors
                                      fertilize eliminate-irrelevance)
                         :in-theory (enable binary-append)
                         :do-not-induct t))))

(defthm rec->list-of-list->rec-h*-list
  (implies
   (equal template (h*-list (not-which op) list))
   (and (v2 (rec->list op template (list->rec op list)))
        (equal (v0 (rec->list op template (list->rec op list)))
               (h*-list (update-op op :which :all) list))
        (not (consp (v1 (rec->list op template (list->rec op list)))))))
  :hints (("goal" :in-theory nil
           :use (:instance rec->list-of-list->rec-h*-list-helper))))

(defthm rec->list-h*-list-not-which-introduction
  (implies
   (and (x? op)
        (syntaxp (not (and (consp list) (equal (car list) 'h*-list))))
        (v2 (rec->list op (h*-list (not-which op) list) rec)))
   (and (iff (v2 (rec->list op list rec))
             (v2 (rec->list op (h*-list (not-which op) list) rec)))
        (implies
         (v2 (rec->list op (h*-list (not-which op) list) rec))
         (and (equal (v1 (rec->list op list rec))
                     (v1 (rec->list op (h*-list (not-which op) list) rec)))
              (equal (v0 (rec->list op list rec))
                     (v0 (rec->list op (h*-list (not-which op) list) rec)))))))
  :hints (("goal" :induct (rec->list op list rec))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors
                                      fertilize eliminate-irrelevance)
                         :in-theory (e/d (rec->spec-h*-spec-not-which-introduction-1
                                            rec->spec-h*-spec-not-which-introduction-2
                                            rec->spec-h*-spec-not-which-introduction-3
                                            g? ;binary-append
                                            )
                                         (numwhich
                                          whichnum
                                          op-base
                                          ;not-which
                                          ))
                         :do-not-induct t))))

(in-theory
 (disable
  rec->list-h*-list-not-which-introduction
  ))


(defun rec->list-of-list->rec-hyp (op template list)
   (equal (h*-list (not-which op) template)
          (h*-list (not-which op) list)))

(defthm rec->list-of-list->rec
  (implies
   (and
    (x? op)
    (rec->list-of-list->rec-hyp op template list))
   (equal (v0 (rec->list op template (list->rec op list)))
          (h*-list (update-op op :which :all) list)))
  :hints (("goal" :in-theory `(rec->list-of-list->rec-hyp
                               rec->list-h*-list-not-which-introduction
                               rec->list-of-list->rec-h*-list
                               ))))

(defthm g*-rec-g*-list-commute
  (implies (x? op)
           (equal (g*-rec (list->rec op list) ram)
                  (list->rec op (g*-list op list ram))))
  :hints (("goal" :induct (g*-list op list ram)
           :do-not '(generalize preprocess eliminate-destructors
                                fertilize eliminate-irrelevance)
           :in-theory (enable g? open-g*-list (:induction g*-list))
           :do-not-induct t)))

(defthmd g*-list-g*-rec-commute
  (implies
   (x? op)
   (equal (list->rec op (g*-list op list ram))
          (g*-rec (list->rec op list) ram))))

(defthm g*-list-default-which
  (implies
   (and (syntaxp (not (quotep w)))
        (not (equal w :all))
        (not (equal w :ptr))
        (not (equal w :nil)))
   (equal (g*-list (op w h) list ram)
          (g*-list (op :val h) list ram)))
  :hints (("goal" :in-theory (enable g*-list g*-spec-default-which))))

(defthmd g*-rec-reduction
  (equal (g*-rec spec ram)
         (g*-rd spec (rd-spec (f*-rec spec) ram)))
  :hints (("Goal" :in-theory (enable RX-TO-RD-LIST-REDUCTION))))

;(local (in-theory (enable LEN)))

(defthm len-v1-rec->spec
  (implies (x? op)
           (equal (len (v1 (rec->spec op spec rec)))
                  (nfix (- (len rec) (len (f*-spec op 0 spec))))))
  :hints (("goal" :in-theory (disable numwhich numtype whichtype ptr? slot-p op-base len x? whichtype
                                      ATOMIC-F*-OP-REPLACEMENT ;looped!
                                      ATOMIC-REC->SPEC-REPLACEMENT
                                      )
           :induct (rec->spec op spec rec))))

(defthm v2-rec->spec-reduction
  (implies (x? op)
           (iff (v2 (rec->spec op spec rec))
                (<= (len (f*-spec op ptr spec)) (len rec))))
  :hints (("goal" :in-theory (disable numwhich numtype op-base ptr? whichtype)
           :induct (rec->spec op spec rec))))

(defthm len-spec->rec
  (equal (len (spec->rec op ptr spec))
         (len (f*-spec op ptr spec)))
  :hints (("Goal" :in-theory (disable numwhich numtype whichtype ptr? slot-p op-base len))))

;bzo
(defthmd append-len0
  (implies (equal (len x) 0)
           (equal (append x y) y))
  :hints (("goal" :in-theory (enable binary-append))))

(defthmd g*-list-g*-rec-reduction
  (implies
   (x? op)
   (equal (g*-list op list ram)
          (v0 (rec->list op list (g*-rec (list->rec op list) ram)))))
  :hints (("goal" :induct (list->rec op list)
           :in-theory (e/d (APPEND-LEN0 ;bzo
                              rec->spec-h*-spec-not-which-introduction-1
                              rec->spec-h*-spec-not-which-introduction-2
                              rec->spec-h*-spec-not-which-introduction-3
                              g*-spec-default-which
                              rec->list-of-list->rec
                              rec->spec-of-spec->rec)
                           (;numwhich
                            )))))

(defthmd f*-list-f*-rec-reduction
  (equal (f*-list op list)
         (f*-rec (list->rec op list)))
  :hints (("goal" :in-theory (enable f*-spec-f*-rec-reduction))))

(defthm h*-rec-h*-list-commute
  (implies
   (implies (g-op op) (optype op :ptr))
   (equal (h*-rec (list->rec op list))
          (list->rec op (h*-list op list))))
  :hints (("goal" :in-theory (enable g?))))

(defthm list-rec-h*-list-reduction
   (implies
    (x? op)
    (equal
     (list->rec op (h*-list op list))
     (list->rec op list))))

(defthm atomic-list->rec-op-replacement
  (implies
   (syntaxp (symbolp op))
   (equal (list->rec op list)
          (list->rec (xop op) list))))

(defthm h*-list-h*-rec-reduction
  (implies
   (and
    (x? op)
    (equal (op-which op) :all))
   (equal (h*-list op list)
          (v0 (rec->list op list (h*-rec (list->rec op list)))))))

(in-theory
 (disable
  h*-list-h*-rec-reduction
  ))

(in-theory
 (disable
  s*-rec-reduction
  ))

(defthm s*-rec-over-s*-rec
  (implies
   (and
    (unique (flat (f*-rec list2)))
    (disjoint (flat (f*-rec list1)) (flat (f*-rec list2))))
   (equal (s*-rec list1 (s*-rec list2 ram))
          (s*-rec list2 (s*-rec list1 ram))))
  :hints (("goal"
           :in-theory (e/d (flat) ( Z*-S*-REC-INTRODUCTION))
           :induct (s*-rec list2 ram))))

(in-theory (disable s*-list-s*-rec-reduction))

(defun flattenlistw (addr vals)
  (if (and (consp addr)
           (consp vals))
      (append (enlistw (len (car addr)) (car vals))
              (flattenlistw (cdr addr) (cdr vals)))
    nil))

(defthm wr-spec-wr-rec-reduction
  (implies (and (equal (len addr) (len vals)) ;hyp added by Eric after changing wr-list..
                (unique (flat addr)))
           (equal (wr-spec addr vals ram)
                  (wr-list (flat addr) (flattenlistw addr vals) ram)))
  :hints (("Goal" :in-theory (enable flat))))

(defthm rd-spec-rd-rec-reduction
  (equal (flat (rd-spec addrs ram))
         (rd-list (flat addrs) ram))
  :hints (("Goal" ; :do-not '(generalize eliminate-destructors)
           :in-theory (enable flat append))))

(defun slot-p-list (list)
  (if (consp list)
      (and (slot-p (car list))
           (slot-p-list (cdr list)))
    t))

(defthm OFFSET-SIZE-expanded-max-offset
  (EQUAL (OFFSET-SIZE (+ -1 (* 1/8 (FIX-SIZE SIZE))))
         (FIX-SIZE SIZE))
  :hints (("Goal" :use (:instance OFFSET-SIZE-MAX-OFFSET)
           :in-theory (disable OFFSET-SIZE-MAX-OFFSET))))

(defthm v0-sblk-parms
  (equal (v0 (sblk-parms base (sblk size off)))
         (fix-size size))
  :hints (("goal" :in-theory (enable sblk-parms))))


;move?
(defthm max-offset-offset-size
  (equal (max-offset (offset-size n))
         (nfix n))
  :hints (("goal" :induct (offset-size n)
           :in-theory (e/d (max-offset)
                           (
                        unfixed-size-max-offset
                        offset-size-max-offset-free
                       )))))

(defthm len-sblkp
  (implies
   (and
    (sblkp sblk)
    (consp sblk))
   (equal (len sblk)
          (1+ (max-offset (v0 (sblk-parms 0 sblk))))))
  :hints (("goal" :in-theory (enable sblk-parms))))

(defun sblkp-list (list)
  (if (consp list)
      (and (sblkp (car list))
           (consp (car list))
           (sblkp-list (cdr list)))
    t))

(defun h*-rd (flat list)
  (if (consp flat)
      (let ((value (wintlist (car list))))
        (met ((size base) (sblk-parms 0 (car flat)))
             (declare (ignore base))
             (cons (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                  value)
                   (h*-rd (cdr flat) (cdr list)))))
    nil))

(defthm slot-p-append
  (equal (slot-p-list (append x y))
         (and (slot-p-list x)
              (slot-p-list y))))

(defthm slot-p-list-spec->rec
  (slot-p-list (spec->rec op ptr spec)))

(defthm slot-p-list-list->rec
  (slot-p-list (list->rec op list)))

(defthm v*-rec-g*-rd
  (implies
   (and
    (equal (len slist)
           (len vals))
    (slot-p-list slist))
   (equal (v*-rec (g*-rd slist vals))
          (h*-rd (f*-rec slist) vals)))
  :hints (("goal" :in-theory (enable ;unfixed-size-wfixn
                                     ))))

(defthm len-rd-spec
  (equal (len (rd-spec list ram))
         (len list)))

(defthm len-f*-rec
  (implies
   (slot-p-list list)
   (equal (len (f*-rec list))
          (len list))))

(defthm f*-rec-g*-rd
  (equal (f*-rec (g*-rd slist vals))
         (f*-rec slist)))

(defun fixlistw (f list)
  (if (consp list)
      (append (enlistw (len (car f)) (wintlist (car list)))
              (fixlistw (cdr f) (cdr list)))
    nil))

(defthm fixlistw-rd-spec
  (equal (fixlistw f (rd-spec f ram))
         (rd-list (flat f) ram))
  :hints (("Goal" :in-theory (enable flat))))

(defthm sblkp-list-f*-rec
  (sblkp-list (f*-rec rec)))

(defthm flattenlistw-h*-rd
  (implies
   (and
    (sblkp-list f)
    (equal (len f)
           (len list)))
   (equal (flattenlistw f (h*-rd f list))
          (fixlistw f list)))
  :hints (("goal" :in-theory (e/d (unfixed-size-max-offset)
                                  (wintlist enlistw)))))

(defthm true-listp-v1-rec->spec
  (implies
   (true-listp rec)
   (true-listp (v1 (rec->spec op spec rec)))))

;; ;bzo
;; (defthm nthcdr-nthcdr
;;   (equal (nthcdr n (nthcdr m list))
;;          (nthcdr (+ (nfix n) (nfix m)) list))
;;   :hints (("Goal" :in-theory (enable nthcdr))))



(local (in-theory (enable nthcdr))) ;bzo


;bzo
(defthmd nthcdr-of-one-more
  (implies (and (integerp n)
                (<= 0 n))
           (equal (NTHCDR (+ 1 n) l)
                  (nthcdr n (cdr l)))))

(in-theory
 (disable
  acl2::s-equal-differential
  ))

(defthm atomic-g*-list-op-replacment
  (implies
   (syntaxp (symbolp gop))
   (equal (g*-list gop list ram)
          (g*-list (xop gop) list ram)))
  :hints (("Goal" :in-theory (enable g*-list))))

;tried replacing iff with equal, but the proof broke..
(defthm g*-list-h*-list-equality-reduction
  (implies
   (x? op)
   (iff (equal (g*-list op list ram) (h*-list (op :all :x) list))
        (equal (g*-rec (list->rec op list) ram) (h*-rec (list->rec op list)))))
  :hints (("goal" :induct (list->rec op list))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors
                                      fertilize eliminate-irrelevance)
                         :in-theory (enable g?
                                            g*-spec-h*-spec-equality-reduction)
                         :do-not-induct t))))

(defthm z*-s*-list-introduction
  (implies
   (and
    (x? op)
    (unique (flat (f*-list op list))))
   (equal (equal ram1 (s*-list op list ram2))
          (and (equal (z* (list (flat (f*-list op list))) ram1)
                      (z* (list (flat (f*-list op list))) ram2))
               (equal (g*-list op list ram1)
                      (h*-list (op :all :x) list)))))
  :hints (("goal" :in-theory '(z*-s*-rec-introduction
                               s*-list-s*-rec-reduction
                               f*-list-f*-rec-reduction
                               g*-list-h*-list-equality-reduction
                               ))))

(defthm z*-s*-list-induction
  (implies
   (and
    (x? op)
    (unique (flat (f*-list op list)))
    (disjoint-list (flat (f*-list op list)) zlist))
   (equal (equal (z* zlist (s*-list op list ram1))
                 (z* zlist ram2))
          (and (equal (z* (cons (flat (f*-list op list)) zlist) ram1)
                      (z* (cons (flat (f*-list op list)) zlist) ram2))
               (equal (h*-list (op :all :x) list)
                      (g*-list op list ram2)))))
  :hints (("goal" :in-theory '(z*-s*-rec-induction
                               s*-list-s*-rec-reduction
                               f*-list-f*-rec-reduction
                               g*-list-h*-list-equality-reduction
                               ))))


(in-theory (disable g*-list-default-which len-sblkp g*-list-h*-list-equality-reduction))

;;
;; Ray's theorem
;;

(defun fix-memory (skels ram)
  (s*-list (op :val :x) (g*-list (op :val :x) skels ram) nil))

(defun fix-memory-list (a-list ram)
   (if (consp a-list)
      (wr
         (car a-list)
         (rd (car a-list) ram)
         (fix-memory-list (cdr a-list) ram))
      nil))

(defthm fix-memory-list-reduction
  (equal (fix-memory-list list ram)
         (wr-list list (rd-list list ram) nil)))

(defthm len-of-h*-rd
  (equal (len (H*-RD FLAT LIST))
         (len FLAT)))


;bzo gross hints
(defthm fix-memory-list-fix-memory-equiv
  (implies
   (and
    (equal list (flat (f*-list (op :val :x) skels)))
    (unique list))
   (equal (fix-memory skels ram)
          (fix-memory-list list ram)))
  :hints (("goal" :in-theory nil)
          ("goal'" :in-theory `((x?)
                                (op)
                                (op-how)
                                fix-memory
                                fix-memory-list-reduction
                                s*-list-s*-rec-reduction
                                f*-list-of-g*-list
                                ))
          ("goal'''" :in-theory `(len-of-h*-rd
                                  (x?)
                                  (op)
                                  (op-how)
                                  len-f*-rec
                                  len-rd-spec
                                  flattenlistw-h*-rd
                                  fixlistw-rd-spec
                                  slot-p-list-list->rec
                                  sblkp-list-f*-rec
                                  fix-memory
                                  fix-memory-list-reduction
                                  g*-list-g*-rec-commute
                                  f*-list-f*-rec-reduction
                                  s*-rec-reduction
                                  g*-rec-reduction
                                  wr-spec-wr-rec-reduction
                                  rd-spec-rd-rec-reduction
                                  f*-rec-g*-rd
                                  v*-rec-g*-rd
                                  ))))

;(in-theory (disable wfix wint))


;; begin stuff from push-gacc:


(in-theory (disable ;sblk
                    (sblk) ;move up?
                    ))

(in-theory
 (disable
  (:CONGRUENCE BAG::PERM-IMPLIES-equal-MEMBERp-2)
  (:CONGRUENCE BAG::PERM-IMPLIES-PERM-APPEND-2)
  (:CONGRUENCE BAG::PERM-IMPLIES-PERM-CONS-2)
  ))

(in-theory (enable acl2::default-car))

(in-theory (enable skel-extensionality!))

(in-theory (disable open-split-blk))



;;  in gacc
;; (defthm f*-spec-h*-spec-introduction
;;   (implies
;;    (and
;;     (x? fop)
;;     (equal hspec (h*-spec (op :nil :x) spec))
;;     (syntaxp (not (equal hspec spec))))
;;    (equal (f*-spec fop base spec)
;;           (f*-spec fop base hspec)))
;;   :hints (("goal''" :induct (f*-spec fop base spec))))

;; (defthm f*-list-h*-list-introduction
;;   (implies
;;    (and
;;     (x? fop)
;;     (equal hlist (h*-list (op :nil :x) list))
;;     (syntaxp (not (equal hlist list))))
;;    (equal (f*-list fop list)
;;           (f*-list fop hlist)))
;;   :hints (("goal''" :induct (f*-list fop list))))

;; (in-theory
;;  (disable
;;   f*-spec-h*-spec-introduction
;;   f*-list-h*-list-introduction
;;   ))

;; (defthm f*-spec-h*-spec-reduction
;;   (implies
;;    (and
;;     (x? fop)
;;     (x? hop))
;;    (equal (f*-spec fop base (h*-spec hop spec))
;;           (f*-spec fop base spec))))

;; (theory-invariant
;;  (incompatible
;;   (:rewrite f*-spec-h*-spec-reduction)
;;   (:rewrite f*-spec-h*-spec-introduction)
;;   ))



(defthm h*-spec-over-rs
  (equal (h*-spec (op :nil :z) (skel-spec (rs size off base spec)))
         (skel-spec (rs size off base (h*-spec (op :nil :z) spec)))))

(in-theory
 (disable
  rs-of-h*-spec
  ))

(defthm f*-spec-v0-split-blk-h*-spec-introduction
  (implies
   (and
    (equal hspec (h*-spec (op :nil :z) spec))
    (syntaxp (not (equal hspec spec))))
   (equal (f*-spec fop fptr (v0 (split-blk spec)))
          (f*-spec fop fptr (v0 (split-blk hspec)))))
  :hints (("goal''" :in-theory (enable open-split-blk open-wv)
           :induct (split-blk spec))))

(in-theory
 (disable
  SPLIT-BLK-H*-SPEC
  ))

(defthm h*-spec-v0-split-blk
  (equal (h*-spec op (v0 (split-blk spec)))
         (v0 (split-blk (h*-spec op spec))))
  :hints (("goal" :in-theory (enable open-split-blk))))

(defthm skel-p-rs
  (skel-p (rs size off base spec)))

(defthm fixed-spec-p-skel-base-rs
  (implies
   (fixed-spec-p spec)
   (acl2::unsigned-byte-p (fix-size size) ;wintn 8 size
          (skel-base (rs size off base spec))))
  :hints (("goal" :in-theory (enable ;unfixed-size-wintn
                                     )
           :induct (rs size off base spec))))

(defun syntax-unfixed-int (n)
  (declare (type t n))
  (or (not (consp n))
      (and (not (equal (car n) 'quote))
           (not (equal (car n) 'ifix)))))

(defthmd unfixed-int-sblk-parms
  (implies (syntaxp (syntax-unfixed-int base))
           (equal (sblk-parms base sblk)
                  (sblk-parms (ifix base) sblk)))
  :hints (("goal" :in-theory (enable sblk-parms))))

(defthmd unfixed-int-ws
  (implies (syntaxp (syntax-unfixed-int off))
           (equal (ws size off base v spec)
                  (ws size (ifix off) base v spec)))
  :hints (("goal" :in-theory (e/d (ws) (zz-ws-introduction)))))



;bzo

(defthmd len-0-not-consp-fwd
  (implies (equal (len list) 0)
           (not (consp list)))
  :rule-classes (:forward-chaining))

;(in-theory (disable consp-h*-spec))

;(local (in-theory (disable bag::SUBBAGP-DISJOINT bag::SUBBAGP-DISJOINT-commute)))
(local (in-theory (disable acl2::S-EQUAL-DIFFERENTIAL)))

;try
(local (in-theory (disable RX-NON-NEGATIVE-LINEAR ACL2::LOGHEAD-UPPER-BOUND)))

(local (in-theory (disable
;                   ACL2::LOGAND-WITH-MASK-ERIC
                   ACL2::UNSIGNED-BYTE-P-LOGHEAD-FORWARD-CHAINING ;bzo
                   ACL2::LOGHEAD-NONNEGATIVE-LINEAR
                   ACL2::LOGHEAD-LEQ
                   acl2::NOT-EVENP-FORWARD-TO-ODDP
                   ACL2::EVENP-FORWARD-TO-NOT-ODDP
  ;                 ACL2::LOGBITP-FORWARD-TO-LOGBIT-ONE
 ;                  ACL2::LOGBITP-FORWARD-TO-LOGBIT-zero
                   BAG::ZP-NFIX
                   )))

(in-theory (disable ifix))

(defun which-covers (w1 w2)
  (declare (type t w1 w2))
  (let ((nw1 (numwhich w1))
        (nw2 (numwhich w2)))
    (equal nw2 (logand nw1 nw2))))

(defun wop-covers (op1 op2)
  (declare (type (satisfies op-p) op1 op2))
  (let ((w1 (op-which op1))
        (w2 (op-which op2)))
    (let ((nw1 (numwhich w1))
          (nw2 (numwhich w2)))
      (equal nw2 (logand nw1 nw2)))))

(local (in-theory (disable nfix))) ;trying...



;(in-theory (disable mv-nth))

;bzo
(in-theory
 (disable
  (:DEFINITION LOGBITP)
  (:DEFINITION ODDP)
  (:DEFINITION EVENP)
  (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT)
  (:DEFINITION ACL2::INTEGER-RANGE-P)
  (:DEFINITION ACL2::BINARY-LOGAND)
  (:DEFINITION FLOOR)
  (:DEFINITION ACL2::UNSIGNED-BYTE-P)
  ))

(in-theory
 (disable
  (:TYPE-PRESCRIPTION PERM)
  (:REWRITE bag::PERM-NIL-Y)
;  (:FORWARD-CHAINING bag::PERM-NOT-CONSP-NIL)
  ))

(in-theory (disable (op)))

(in-theory (enable slot-p))

(in-theory (enable skel-extensionality!))

(local (in-theory (disable skel-extensionality!)))

(in-theory (disable max-offset))
(local (in-theory (disable slot-p)))

(defthm slot-extensionality!!
  (implies
   (skel-p skel)
   (and (equal (equal x (slot name off size val type skel))
               (and (slot-p x)
                    (equal (slot-name x) name)
                    (equal (slot-off  x) off)
                    (equal (slot-size x) size)
                    (equal (slot-val  x) val)
                    (equal (slot-type x) type)
                    (equal (slot-skel x) skel)))
;;         (equal (equal (slot name off size val type skel) x)
;;                (and (slot-p x)
;;                     (equal name (slot-name x) )
;;                     (equal off  (slot-off  x) )
;;                     (equal size (slot-size x) )
;;                     (equal val  (slot-val  x) )
;;                     (equal type (slot-type x) )
;;                     (equal skel (slot-skel x) )))
        ))
  :hints (("goal" :in-theory (enable ; slot-skel
; slot-name
;slot-off
;slot-size
;slot-val
;slot-type
;slot
;slot-p
;weak-slot-p
                              ))))

(defthm h*-spec-g*-spec-track
  (and (implies (consp (h*-spec hop spec))
                (consp (g*-spec gop gptr spec ram)))
       (implies (not (consp (h*-spec hop spec)))
                (not (consp (g*-spec gop gptr spec ram)))))
  :hints (("goal" :induct (len spec) :in-theory (enable (:induction len)))))





(in-theory
 (enable
  (:induction g*-spec)
  (:induction f*-spec)
  (:induction h*-spec)
  (:induction s*-spec)
  ))

(in-theory
 (enable
;;  wx-of-rx
  ))

(defun which-union (w1 w2)
  (let ((n1 (numwhich w1))
        (n2 (numwhich w2)))
    (let ((n (logand #x3 (logior n1 n2))))
      (case n
            (3 :all)
            (2 :ptr)
            (1 :val)
            (t :nil)))))

(defun how-which (op1)
  (if (equal (op-how op1) :x) :nil :ptr))

(defun f*-g* (op)
  (op (which-union (how-which op) (op-which op)) :x))

(defun g? (how)
  (and (not (equal how :x))
       (not (equal how :z))))

(defun g-op (op)
  (g? (op-how op)))

(defun x-op (op)
  (not (g? (op-how op))))

(defun g*-wx (op)
  (if (or (equal (op-how op) :x)
          (equal (op-how op) :z)) op
    (op (which-union (how-which op)
                     (op-which op))
        :x)))

(defthm numtype-when-not-pointer
  (implies (not (equal :ptr type))
           (equal (numtype type)
                  1)))

(defthm numtype-when-ptr
  (implies (ptr? type)
           (equal (numtype type)
                  2)))

(defthm g*-spec-over-wx
  (implies
   (and
    (disjoint
     (sblk wsize wptr)
     (flat (f*-spec (g*-wx gop) gptr (if (g-op gop) (g*-spec gop gptr gspec ram) gspec))))
    )
   (equal (g*-spec gop gptr gspec (wx wsize wptr wvalue ram))
          (g*-spec gop gptr gspec ram)))
  :hints (("goal" :induct (g*-spec gop gptr gspec ram)
           :in-theory (e/d (bag::flat-of-cons)
                           (numwhich
                            numtype
                            ;; which-union
                            ;; op-base
                            ))
           :do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t)))



(defthm g*-spec-g-over-wx
  (implies
   (and
    (g-op gop)
    (equal v (g*-spec gop gptr gspec ram))
    (disjoint
     (sblk wsize wptr)
     (flat (f*-spec (g*-wx gop) gptr v)))
    )
   (equal (g*-spec gop gptr gspec (wx wsize wptr wvalue ram))
          v)))

(defthm g*-spec-x-over-wx
  (implies
   (and
    (x-op gop)
    (disjoint
     (sblk wsize wptr)
     (flat (f*-spec gop gptr gspec)))
    )
   (equal (g*-spec gop gptr gspec (wx wsize wptr wvalue ram))
          (g*-spec gop gptr gspec ram))))

;;
;; For efficiency, we usually want either x or g.
;;

(in-theory
 (disable
  g*-spec-over-wx
  ))

(defthm rx-over-s*-spec
  (implies
   (disjoint
    (sblk rsize rptr)
    (flat (f*-spec sop sptr sspec)))
   (equal (rx rsize rptr (s*-spec sop sptr sspec ram))
          (rx rsize rptr ram)))
  :hints (("goal" :in-theory (e/d (bag::flat-of-cons ;bzo
;                                   wx-of-rx
                                   )
                                  (numwhich
                                   numtype
                                   op-base
                                   whichtype
                                   ptr?
                                   ))
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :induct (s*-spec sop sptr sspec ram))
          ))

(defthm s*-spec-over-wx
  (implies
   (disjoint
    (sblk wsize wptr)
    (flat (f*-spec sop sptr sspec)))
   (equal (s*-spec sop sptr sspec (wx wsize wptr wvalue ram))
          (wx wsize wptr wvalue (s*-spec sop sptr sspec ram))))
  :hints (("goal" :in-theory (e/d (bag::flat-of-cons ;wx-of-rx
                                                     ) (numwhich numtype op-base whichtype ptr?))
           :induct (s*-spec sop sptr sspec ram)
           :do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t)
          ))

(defthm s*-list-over-wx
  (implies
   (disjoint
    (sblk wsize wptr)
    (flat (f*-list sop sspec)))
   (equal (s*-list sop sspec (wx wsize wptr wvalue ram))
          (wx wsize wptr wvalue (s*-list sop sspec ram))))
  :hints (("goal" :in-theory (enable s*-list)
           :induct (s*-list sop sspec ram))))

(defthm s*-spec-over-s*-spec
  (implies
   (disjoint
    (flat (f*-spec sop1 sptr1 sspec1))
    (flat (f*-spec sop2 sptr2 sspec2)))
   (equal (s*-spec sop1 sptr1 sspec1 (s*-spec sop2 sptr2 sspec2 ram))
          (s*-spec sop2 sptr2 sspec2 (s*-spec sop1 sptr1 sspec1 ram))))
  :hints (("goal" :in-theory (e/d (bag::flat-of-cons ;bzo. prove a meta rule to handle this?
                                   ;wx-of-rx
                                     )
                                  (numwhich numtype op-base whichtype ptr?))
           :do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :induct (s*-spec sop2 sptr2 sspec2 ram))
          ))

(defthm op-base-lemma-1
  (implies (not (EQUAL TYPE :PTR))
           (equal (OP-BASE H TYPE BASE VALU)
                  base)))

(defthm S*-SPEC-when-ptr-is-not-an-integerp
  (implies (not (integerp ptr))
           (equal (S*-SPEC OP PTR SPEC RAM)
                  (S*-SPEC OP 0 SPEC RAM)))
  :hints (("Goal" :in-theory (e/d (S*-SPEC ifix) (numwhich numtype op-base ptr? whichtype)))))

(defthm wx-when-v-is-not-an-integerp
  (implies (not (integerp v))
           (equal (WX SIZE A V RAM)
                  (WX SIZE A 0 RAM)))
  :hints (("Goal" :in-theory (enable wx))))

(defthm g*-spec-over-s*-spec
  (implies (and (g-op gop)
                (equal v (g*-spec gop gptr gspec ram))
                (disjoint (flat (f*-spec sop sptr sspec))
                          (flat (f*-spec (f*-g* gop) gptr v))))
           (equal (g*-spec gop gptr gspec (s*-spec sop sptr sspec ram))
                  v))
  :hints (("goal" :induct (s*-spec sop sptr sspec ram)
           :do-not-induct t
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :expand ((F*-SPEC SOP 0 SSPEC)
                    (F*-SPEC SOP SPTR SSPEC))
           :in-theory (e/d (BAG::FLAT-OF-CONS)
                           (ptr?
                            ;;g?
                            ;;whichtype
                            WHICH-UNION ;helped a lot
                            ;;G*-WX
                            numwhich ;this made a huge difference
                            NUMTYPE ;this made a big difference
                            HOW-WHICH ;did this hurt things?
                            op-base
                            ATOMIC-S*-OP-REPLACEMENT
                            ATOMIC-F*-OP-REPLACEMENT
                            ATOMIC-G*-OP-REPLACEMENT
                            OPEN-F*-SPEC
                            ;; bag::memberp-implies-subbagp-flat
                            ;; bag::subbagp-disjoint-commute
                            ;; s*-spec-over-wx
                            ;; skel-extensionality!
                            ;; bag::subbagp-implies-membership
                            ;; WX-OF-RX
                            ;; ACL2::LOGAND-WITH-MASK-ERIC
                            ACL2::UNSIGNED-BYTE-P-LOGHEAD-FORWARD-CHAINING ;bzo
                            ACL2::LOGHEAD-NONNEGATIVE-LINEAR
                            ACL2::LOGHEAD-LEQ
                            BINARY-APPEND  ;bzo
                            ;;disable more fwc rules?
                            acl2::NOT-EVENP-FORWARD-TO-ODDP
                            ACL2::EVENP-FORWARD-TO-NOT-ODDP
                            ;; ACL2::LOGBITP-FORWARD-TO-LOGBIT-ONE
                            ;; ACL2::LOGBITP-FORWARD-TO-LOGBIT-zero
                            BAG::ZP-NFIX
                            ACL2::UNSIGNED-BYTE-P-LOGHEAD-FORWARD-CHAINING ;bzo
                            ACL2::LOGHEAD-NONNEGATIVE-LINEAR
                            ACL2::LOGHEAD-LEQ
                            )))))


(defthm x*-spec-over-s*-spec
  (implies
   (and
    (x-op gop)
    (disjoint
     (flat (f*-spec sop sptr sspec))
     (flat (f*-spec gop gptr gspec))))
   (equal (g*-spec gop gptr gspec (s*-spec sop sptr sspec ram))
          (g*-spec gop gptr gspec ram)))
  :hints (("goal" :induct (s*-spec sop sptr sspec ram)
           :do-not-induct t
           :do-not '(generalize ;preprocess
                     eliminate-destructors fertilize eliminate-irrelevance)
           :in-theory (e/d (bag::flat-of-cons) (;for efficiency:
                                                numwhich
                                                g?
                                                ;x-op
                                                ptr?
                                                whichtype
                                                numtype
                                                op-base)))))

(defun subwhich (w1 w2)
  (let ((n1 (numwhich w1))
        (n2 (numwhich w2)))
    (let ((n (logand n1 (lognot n2))))
      (whichnum n))))

(in-theory (disable g?))

(defun s*-g*-equal-induction (gop gptr gspec sop sptr sspec ram)
  (if (and (consp gspec)
           (consp sspec))
      (let ((gslot (car gspec))
            (sslot (car sspec)))
        (if (and (slot-p gslot)
                 (slot-p sslot))
            (let ((gw (op-which gop))
                  (gh (op-how   gop))
                  (sw (op-which sop))
                  (sh (op-how   sop)))
              (let ((goff   (slot-off  gslot))
                    (gsize  (slot-size gslot))
                    (gtype  (slot-type gslot))
                    (gskel  (slot-skel gslot))
                    (gvalue (slot-val  gslot))
                    (soff   (slot-off  sslot))
                    (ssize  (slot-size sslot))
                    (stype  (slot-type sslot))
                    (sskel  (slot-skel sslot))
                    (svalue (slot-val  sslot))
                    )
                (let ((gread (rx gsize (+<> goff gptr) ram))
                      (sread svalue))
                  (let ((gbase (skel-base gskel))
                        (sbase (skel-base sskel)))
                    (let ((gbase (acl2::loghead (gacc::fix-size gsize) ;wfixn 8 gsize
                                        (op-base gh gtype gbase gread)))
                          (sbase (acl2::loghead (gacc::fix-size ssize) ;wfixn 8 ssize
                                        (op-base sh stype sbase sread))))
                      (let ((gvalue (acl2::loghead (gacc::fix-size gsize) ;wfixn 8 gsize
                                                   (if (whichtype gw gtype) gread gvalue)))
                            (svalue (acl2::loghead (gacc::fix-size ssize) ;wfixn 8 ssize
                                                   (if (whichtype sw stype) svalue
                                                     (rx ssize (+<> soff sptr) ram)))))
                        (let ((gskel (update-skel gskel :base gbase)))
                          (let ((ram (wx ssize (+<> soff sptr) svalue ram)))
                            (met ((gspex ramx) (s*-g*-equal-induction
                                                gop gbase (skel-spec gskel)
                                                sop sbase (skel-spec sskel) ram))
                                 (let ((gskelx (skel gbase gspex)))
                                   (let ((gskel (if (ptr? gtype) gskelx gskel))
                                         (ram   (if (ptr? stype) ramx ram)))
                                     (met ((gspex sram) (s*-g*-equal-induction
                                                         gop gptr (cdr gspec)
                                                         sop sptr (cdr sspec) ram))
                                          (mv (cons (update-slot gslot
                                                                 :val  gvalue
                                                                 :skel gskel
                                                                 )
                                                    gspex)
                                              sram)))))))))))))
          (if (and (not (slot-p gslot))
                   (not (slot-p sslot)))
              (s*-g*-equal-induction gop gptr (cdr gspec)
                                     sop sptr (cdr sspec) ram)
            (mv nil (s*-spec sop sptr sspec ram)))))
    (if (consp sspec)
        (mv nil (s*-spec sop sptr sspec ram))
      (mv nil ram))))

(defthm mv-nth-s*-g*-equal-induction
  (equal (v1 (s*-g*-equal-induction gop gbase gspec sop sbase sspec ram))
         (s*-spec sop sbase sspec ram))
  :hints (("goal" :induct (s*-g*-equal-induction gop gbase gspec sop sbase sspec ram)
           :do-not-induct t
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :in-theory (disable ;efficiency:
                       numwhich numtype op-base ptr?))))



(defun f*-f*-induction (aop aptr aspec bop bptr bspec)
  (if (and (consp aspec)
           (consp bspec))
      (let ((aslot (car aspec))
            (bslot (car bspec)))
        (if (and (slot-p aslot)
                 (slot-p bslot))
            (let ((aw (op-which aop))
                  (ah (op-how   aop))
                  (bw (op-which bop))
                  (bh (op-how   bop)))
              (let ((aoff  (slot-off  aslot))
                    (asize (slot-size aslot))
                    (atype (slot-type aslot))
                    (askel (slot-skel aslot))
                    (avalue (slot-val aslot))
                    (boff  (slot-off  bslot))
                    (bsize (slot-size bslot))
                    (btype (slot-type bslot))
                    (bskel (slot-skel bslot))
                    (bvalue (slot-val bslot)))
                (let ((aread avalue)
                      (bread bvalue))
                  (let ((abase (skel-base askel))
                        (bbase (skel-base bskel)))
                    (let ((abase (acl2::loghead (gacc::fix-size asize) ;wfixn 8 asize
                                                (op-base ah atype abase aread)))
                          (bbase (acl2::loghead (gacc::fix-size bsize) ;wfixn 8 bsize
                                                (op-base bh btype bbase bread))))
                      (let ((ablk (if (whichtype aw atype) (sblk asize (+<> aoff aptr)) nil))
                            (bblk (if (whichtype bw btype) (sblk bsize (+<> boff bptr)) nil)))
                        (let ((recx (f*-f*-induction aop abase (skel-spec askel)
                                                     bop bbase (skel-spec bskel))))
                          (append ablk bblk
                                  recx
                                  (f*-f*-induction aop aptr (cdr aspec)
                                                   bop bptr (cdr bspec))))))))))
          (if (and (not (slot-p aslot))
                   (not (slot-p bslot)))
              (f*-f*-induction aop aptr (cdr aspec)
                               bop bptr (cdr bspec))
            (list aop aptr aspec
                  bop bptr bspec))))
    (list aop aptr aspec
          bop bptr bspec)))

(local (in-theory (disable LIST::LEN-OF-CDR)))
(local (in-theory (enable len)))

(defthm len-f*-spec-under-h*-spec-equality
  (implies (equal (h*-spec hop fspec)
                  (h*-spec hop hspec))
           (equal (equal (len (f*-spec fop fptr fspec))
                         (len (f*-spec fop hptr hspec)))
                  t))
  :hints (("goal" :induct (f*-f*-induction fop fptr fspec fop hptr hspec)
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :in-theory (disable ;for efficiency:
                       ptr? OP-BASE numwhich numtype whichtype
                       )
           :do-not-induct t)))


;causes a case-split.
(defthm logbitp-1-of-numwhich
  (equal (LOGBITP 1 (NUMWHICH which))
         (or (equal :all which)
             (equal :ptr which))))


(defthm f*-spec-under-h*-spec-equality
  (implies
   (and
    (x-op fop)
    (equal (h*-spec hop fspec)
           (h*-spec hop hspec))
    (syntaxp (not (acl2::term-order fspec hspec)))
    (x? hop)
    )
   (equal (f*-spec fop fptr fspec)
          (f*-spec fop fptr hspec)))
  :hints (("goal" :induct (f*-f*-induction fop fptr fspec fop fptr hspec)
           :do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :in-theory (e/d (g?
                            ) ( ;;for efficiency:
                            numwhich
                            numtype
                            whichtype
                            ;;op-base
                            )))))

(defun w-not (w)
  (whichnum (logand #x3 (lognot (numwhich w)))))

(defun wop-not (op)
  (update-op op :which (w-not (op-which op))))

(defun wall (op)
  (update-op op :which :all))

;; ;Bbzo this has been replaced!
;; ;and now we're including all of super-ihs anyway?
;; ;try to not have this book rely on this...
;;  (DEFTHM
;;    ACL2::EQUAL-LOGAND-EXPT-REWRITE
;;    (IMPLIES (AND (SYNTAXP (QUOTEP ACL2::N))
;;                  (EQUAL (EXPT 2 (1- (INTEGER-LENGTH ACL2::N)))
;;                         ACL2::N)
;;                  (INTEGERP ACL2::N)
;;                  (INTEGERP ACL2::X)
;;                  (INTEGERP ACL2::K))
;;             (EQUAL (EQUAL (LOGAND ACL2::N ACL2::X) ACL2::K)
;;                    (IF (LOGBITP (1- (INTEGER-LENGTH ACL2::N))
;;                                 ACL2::X)
;;                        (EQUAL ACL2::K ACL2::N)
;;                        (EQUAL ACL2::K 0))))
;;    :HINTS
;;    (("goal"
;;      :IN-THEORY (ENABLE ACL2::LRDT)
;;      :USE (:INSTANCE ACL2::EQUAL-LOGAND-EXPT
;;                      (ACL2::N (1- (INTEGER-LENGTH ACL2::N))))))))


(defthm usb2-of-numwhich
  (ACL2::UNSIGNED-BYTE-P 2 (NUMWHICH which)))

(defthm usb2-of-numtype
  (ACL2::UNSIGNED-BYTE-P 2 (NUMtype which)))




(defthm logbitp-1-of-numtype
  (equal (LOGBITP 1 (NUMTYPE type))
         (equal :ptr type)))

;bzo gen
(defthm loghead-lognot-hack
  (implies (and (syntaxp (quotep k))
                (acl2::unsigned-byte-p 2 k)
                (integerp x)
;                (integerp n)
 ;               (<= 0 n)
                )
           (equal (EQUAL (ACL2::LOGHEAD 2 (LOGNOT x)) k)
                  (EQUAL (ACL2::LOGHEAD 2 x) (acl2::loghead 2 (lognot k)))))
  :hints (("Goal" :in-theory (enable acl2::loghead acl2::lognot))))

(defthm numtype-equal-own-logcar-rewrite
  (equal (EQUAL (NUMTYPE type) (ACL2::LOGCAR (NUMTYPE type)))
         (not (equal :ptr type))))

(defthm op-base-one
  (equal (OP-BASE :X :PTR base valu)
         base))

(defthm numwhich-cases
  (implies (and (NOT (EQUAL (NUMWHICH which) 0))
                (NOT (EQUAL (NUMWHICH which) 1))
                (NOT (EQUAL (NUMWHICH which) 2)))
           (equal (NUMWHICH which)
                  3))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0 0)))
  )



(defthm loghead-of-op-base
  (equal (acl2::loghead n (OP-BASE H TYPE BASE VALU))
         (OP-BASE H TYPE (acl2::loghead n BASE) (acl2::loghead n VALU))))

(defthm whichtype-of-all
  (equal (whichtype :all type)
         t
         ))

(defthm whichnum-equal-all-rewrite
  (equal (EQUAL :ALL (WHICHNUM which))
         (equal 3 which)))

(defthm whichnum-equal-ptr-rewrite
  (equal (EQUAL :ptr (WHICHNUM which))
         (equal 2 which)))

(defthm numwhich-equal-0-rewrite
  (equal (EQUAL (NUMWHICH which) 0)
         (EQUAL which :NIL)))

(defthm numwhich-equal-2-rewrite
  (equal (EQUAL (NUMWHICH which) 2)
         (EQUAL which :ptr)))

(defthm numwhich-equal-3-rewrite
  (equal (EQUAL (NUMWHICH which) 3)
         (EQUAL which :all)))

(defthm numwhich-equal-1-rewrite
  (equal (EQUAL (NUMWHICH which) 1)
         (and (not (equal which :all))
              (not (equal which :ptr))
              (not (equal which :nil)))))


;bzo
(defthm numwhich-of-whichnum
  (implies (acl2::unsigned-byte-p 2 n)
           (equal (numwhich (whichnum n))
                  n)))



(defthm evenp-of-numwhich
  (equal (evenp (numwhich which))
         (or (equal :nil which)
             (equal :ptr which))))

(defthm logcar-of-numwhich
  (equal (equal 0 (acl2::logcar (numwhich which)))
         (or (equal :nil which)
             (equal :ptr which))))

(defthm whichtype-of-nil
  (equal (WHICHTYPE :NIL type)
         nil))


(defthm w-not-equal-all-rewrite
  (equal (EQUAL :ALL (W-NOT w))
         (equal w :nil)))

(defthm w-not-equal-nil-rewrite
  (equal (EQUAL :nil (W-NOT w))
         (equal w :all)))

(defthm w-not-equal-ptr-rewrite
  (equal (EQUAL :ptr (W-NOT w))
         (and (not (EQUAL :val (W-NOT w)))
              (not (EQUAL :nil (W-NOT w)))
              (not (EQUAL :all (W-NOT w)))
              )))

(defthm w-not-equal-val-rewrite
  (equal (equal :val (w-not w))
         (equal :ptr w)))

;; (defthm slot-p-of-slot-forward-chaining
;;   (implies (SKEL-P SKEL)
;;            (slot-p (slot NAME OFF SIZE VAL TYPE SKEL)))
;;   :rule-classes ((:forward-chaining :trigger-terms ((slot NAME OFF SIZE VAL TYPE SKEL)))))

(defthm not-equal-slot-hack-cheap
  (implies (and (not (slot-p blah))
                (SKEL-P SKEL))
           (not (equal blah (slot NAME OFF SIZE VAL TYPE SKEL))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  )

;; (defun double-cdr-induct (a b)
;;   (if (endp a)
;;       (list a b)
;;     (double-cdr-induct (cdr a) (cdr b))))

(defthm subbagp-f*-spec-cdr-lemma
  (implies t ; (subbagp spec spec2)
           (subbagp (f*-spec op ptr (cdr spec)) (f*-spec op ptr spec)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;          :induct (double-cdr-induct spec spec2)
           :expand ((F*-SPEC OP PTR SPEC2))
           :in-theory (disable ATOMIC-F*-OP-REPLACEMENT NUMTYPE numwhich op-base))))


(defthm x*-spec-of-s*-spec
  (implies
   (and
    (x? gop)
    (equal sop gop)
    (equal gptr sptr)
    (unique (flat (f*-spec sop sptr sspec)))
    (equal (h*-spec (wop-not gop) gspec)
           (h*-spec (wop-not gop) sspec)))
   (equal (g*-spec gop gptr gspec (s*-spec sop sptr sspec ram))
          (h*-spec (wall gop) sspec)))
  :hints (("goal" :induct (s*-g*-equal-induction gop gptr gspec sop sptr sspec ram)
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :expand (;bzo
                    (F*-SPEC GOP GPTR SSPEC)
                    (:free (op) (H*-SPEC op GSPEC))
                    (:free (op) (H*-SPEC op sSPEC))
                    (S*-SPEC GOP GPTR SSPEC RAM))
           :do-not-induct t
           :in-theory (e/d (bag::flat-of-cons)
                           ( ;mostly for efficiency:
                            OPEN-F*-SPEC
                            OPEN-G*-SPEC
                            OPEN-S*-SPEC ;didn't help much?
                            OPEN-H*-SPEC
                            ;f*-spec
                            FIXED-SPEC-P
                            ATOMIC-G*-OP-REPLACEMENT
                            ATOMIC-S*-OP-REPLACEMENT
                            ATOMIC-F*-OP-REPLACEMENT
                            numwhich
                            WHICHNUM
                            numtype
                            op-base
                            which-union
                            binary-append
                            flat
                            w-not
                            ;SKEL-EXTENSIONALITY
                            ;;SLOT-EXTENSIONALITY
                            SLOT-EXTENSIONALITY!!
                            ;;x-op
                            ;;PTR?
                            )))))

(in-theory
 (disable
  f*-spec-under-h*-spec-equality
  len-f*-spec-under-h*-spec-equality
  ))

(defun f*-h*-op (fop hop)
  (if (x? fop)
      (update-op fop :how (op-how hop))
    fop))

(defun w-all? (op)
  (equal (op-which op) :all))

(defthm len-f*-spec-base
  (implies
   (syntaxp (not (quotep fptr)))
   (equal (len (f*-spec fop fptr fspec))
          (len (f*-spec fop 0 fspec)))))

(defun f*-h*-induction (fop fptr hop spec)
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((hh (op-how   hop))
                  (fh (op-how   fop)))
              (let ((size  (slot-size slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot))
                    (value (slot-val  slot))
                    )
                (let ((read value))
                  (let ((base (skel-base skel)))
                    (let ((hbase (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                (op-base hh type base read))))
                      (let ((fbase (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                  (op-base fh type hbase read))))
                        (let ((skelx (skel fbase (f*-h*-induction fop fbase hop (skel-spec skel)))))
                          (let ((skel (update-skel skel :base fbase)))
                            (let ((skel (if (ptr? type) skelx skel)))
                              (let ((slot (update-slot slot :skel skel)))
                                (cons slot
                                      (f*-h*-induction fop fptr hop (cdr spec)))))))))))))
          (cons slot
                (f*-h*-induction fop fptr hop (cdr spec)))))
    fptr))

(defthm len-f*-spec-of-h*-spec
  (implies
   (w-all? hop)
   (equal (len (f*-spec fop fptr (h*-spec hop spec)))
          (len (f*-spec (f*-h*-op fop hop) fptr spec))))
  :hints (("goal" :induct (f*-h*-induction fop fptr hop spec)
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :in-theory (e/d (g?) (;F*-H*-OP
                                 numwhich numtype op-base WHICHTYPE ptr? x?)))
          ))

(defthm f*-spec-of-h*-spec
  (implies
   (w-all? hop)
   (equal (f*-spec fop fptr (h*-spec hop spec))
          (f*-spec (f*-h*-op fop hop) fptr spec)))
  :hints (("goal" :induct (f*-h*-induction fop fptr hop spec)
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :in-theory (e/d (g?) (numwhich numtype)))))

(defthm g*-spec-to-h*-spec
  (implies
   (and
    (x? gop)
    (equal (op-which gop) :nil))
   (equal (g*-spec gop gptr gspec ram)
          (h*-spec (wall gop) gspec)))
  :hints (("goal" :induct (g*-spec gop gptr gspec ram))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
                         :do-not-induct t
                         ))))

(defun which-intersect (op1 op2)
  (declare (type (satisfies op-p) op1 op2))
  (let ((nw1 (numwhich (op-which op1)))
        (nw2 (numwhich (op-which op2))))
    (let ((nw (logand nw1 nw2)))
      (whichnum nw))))

(defun h*-h*-op (op1 op2)
  (declare (type (satisfies op-p) op1 op2))
  (let ((op1 (if (x? op1) (update-op op1 :how (op-how op2)) op1)))
    (update-op op1 :which (which-intersect op1 op2))))

(defun h*-h*-hyp (op1 op2)
  (implies (or (g-op op1) (g-op op2)) (optype op2 :ptr)))

(defthm logand-equal-3-rewrite
  (implies (and (acl2::unsigned-byte-p 2 x)
                (acl2::unsigned-byte-p 2 y))
           (equal (EQUAL (LOGAND x y) 3)
                  (and (equal x 3)
                       (equal y 3)))))

(defthm h*-spec-of-h*-spec
  (implies
   (h*-h*-hyp op1 op2)
   (equal (h*-spec op1 (h*-spec op2 spec))
          (h*-spec (h*-h*-op op1 op2) spec)))
  :hints (("goal" :induct (h*-spec op2 spec)
           :do-not '(generalize eliminate-destructors
                                fertilize eliminate-irrelevance)
           :do-not-induct t
           :expand ((H*-SPEC OP2 SPEC))
           :in-theory (e/d (g?) (;numwhich
                                 ;numtype
                                 ;whichtype
                                 open-h*-spec
                                 ATOMIC-H*-OP-REPLACEMENT
                                 )))))

(defun s*-h*-induction (sop sptr hop spec sram)
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((sw (op-which sop))
                  (sh (op-how   sop))
                  (hh (op-how   hop)))
              (let ((off   (slot-off  slot))
                    (size  (slot-size slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot))
                    (value (slot-val  slot))
                    )
                (let ((read value))
                  (let ((base (skel-base skel)))
                    (let ((hbase (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                (op-base hh type base read))))
                      (let ((sbase (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                  (op-base sh type hbase read))))
                        (let ((svalue (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                     (if (whichtype sw type) value (rx size (+<> off sptr) sram)))))
                          (let ((sram (wx size (+<> off sptr) svalue sram)))
                            (let ((sram (if (ptr? type)
                                            (s*-h*-induction sop sbase hop (skel-spec skel) sram)
                                          sram)))
                              (s*-h*-induction sop sptr hop (cdr spec) sram))))))))))
          (s*-h*-induction sop sptr hop (cdr spec) sram)))
    sram))

(defthm s*-h*-induction-reduction
  (implies
   (and
    (x-op sop)
    (wop-covers hop sop))
   (equal (s*-h*-induction sop sptr hop spec sram)
          (s*-spec sop sptr (h*-spec hop spec) sram)))
  :hints (("goal" :induct (s*-h*-induction sop sptr hop spec sram)
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :in-theory (e/d (g?) (numwhich
                                 numtype
                                 ;op-base
                                 ;whichtype
                                 )))))

(defthm s*-spec-with-h*-spec
  (implies
   (and
    (x-op sop)
    (wop-covers hop sop))
   (equal (s*-spec sop sptr (h*-spec hop spec) ram)
          (s*-spec (f*-h*-op sop hop) sptr spec ram)))
  :hints (("goal" :induct (s*-h*-induction sop sptr hop spec ram)
           :do-not '(generalize
                     preprocess ;;
                     eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :in-theory (e/d (g?) (numwhich ;numtype ;slowed things down?
                                          )))))

(defun g*-h*-induction (gop gptr hop spec ram)
  (if (consp spec)
      (let ((op gop)
            (ptr gptr))
        (let ((slot (car spec)))
          (if (slot-p slot)
              (let ((hh (op-how   hop))
                    (w  (op-which op))
                    (h  (op-how   op)))
                (let ((off   (slot-off  slot))
                      (size  (slot-size slot))
                      (type  (slot-type slot))
                      (skel  (slot-skel slot))
                      (value (slot-val  slot))
                      )
                  (let ((read (rx size (+<> off ptr) ram)))
                    (let ((base (skel-base skel)))
                      (let ((hbase (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                  (op-base hh type base read))))
                        (let ((base (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                   (op-base h type hbase read))))
                          (let ((value (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                      (if (whichtype w type) read value))))
                            (let ((skel (update-skel skel :base base)))
                              (let ((skelx (skel base (g*-h*-induction gop base hop (skel-spec skel) ram))))
                                (let ((skel (if (ptr? type) skelx skel)))
                                  (cons (update-slot slot
                                                     :val  value
                                                     :skel skel
                                                     )
                                        (g*-h*-induction gop gptr hop (cdr spec) ram))))))))))))
            (cons slot
                  (g*-h*-induction gop gptr hop (cdr spec) ram)))))
    nil))

(defthm g*-spec-with-h*-spec
  (implies
   (and
    (wop-covers hop (wop-not gop))
    (not (g? (op-how hop))))
   (equal (g*-spec gop gptr (h*-spec hop spec) ram)
          (g*-spec (f*-h*-op gop hop) gptr spec ram)))
  :hints (("goal" :induct (g*-h*-induction gop gptr hop spec ram)
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :in-theory (e/d (g?) (numwhich numtype
                                          ;whichnum
                                          )))
          ))

(defun hop-not (op)
  (let ((w (numwhich (op-which op))))
    (let ((w (whichnum (logxor w #x3))))
      (op w (op-how op)))))

(defun hop- (op1 op2)
  (let ((w1 (numwhich (op-which op1)))
        (w2 (numwhich (op-which op2))))
    (let ((w (whichnum (logand (lognot w1) w2))))
      (op w (op-how op2)))))

(defthm h*-spec-over-g*-spec
  (implies
   (x? hop)
   (equal (h*-spec hop (g*-spec gop gptr gspec ram))
          (g*-spec (hop- (hop-not hop) gop) gptr (h*-spec (hop- gop hop) gspec) ram)))
  :hints (("goal" :induct (g*-spec gop gptr gspec ram)
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :in-theory (disable ;numwhich numtype
                               ))))

(defun w-nill (op)
  (update-op op :which :nil))

(defun f*-g*-induction (fop fptr op ptr spec ram)
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how   op))
                  (fh (op-how   fop)))
              (let ((off   (slot-off  slot))
                    (size  (slot-size slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot))
                    (value (slot-val  slot))
                    )
                (let ((read (rx size (+<> off ptr) ram)))
                  (let ((base (skel-base skel)))
                    (let ((base (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                               (op-base h type base read))))
                      (let ((value (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                  (if (whichtype w type) read value))))
                        (let ((fbase (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                    (op-base fh type base value))))
                          (let ((skel (update-skel skel :base base)))
                            (let ((skelx (skel base (f*-g*-induction fop fbase op base (skel-spec skel) ram))))
                              (let ((skel (if (ptr? type) skelx skel)))
                                (let ((slot (update-slot slot :skel skel)))
                                  (cons slot
                                        (f*-g*-induction fop fptr op ptr (cdr spec) ram)))))))))))))
          (cons slot
                (f*-g*-induction fop fptr op ptr (cdr spec) ram))))
    (list fop fptr)))

(defthm f*-spec-of-g*-spec-reduction
  (implies
   (and
    (not (equal (op-which gop) :nil))
    (x-op fop)
    )
   (equal (f*-spec fop fptr (g*-spec gop gptr spec ram))
          (f*-spec fop fptr (g*-spec (w-nill gop) gptr spec ram))))
  :hints (("goal" :induct (f*-g*-induction fop fptr gop gptr spec ram))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
                         :do-not-induct t
                         :in-theory (enable g?)
                         ))))

(defun op-which-subbagp-< (op1 op2)
  (let ((w1 (op-which op1))
        (w2 (op-which op2)))
    (let ((n1 (numwhich w1))
          (n2 (numwhich w2)))
      (equal n1 (logand n1 n2)))))

(defun g*-g*-induction (gop1 gptr1 ram1 op ptr spec ram)
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w  (op-which  op))
                  (h  (op-how    op))
                  (w1 (op-which gop1))
                  (h1 (op-how   gop1)))
              (let ((off   (slot-off  slot))
                    (size  (slot-size slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot))
                    (value (slot-val  slot))
                    )
                (let ((read  (rx size (+<> off ptr) ram))
                      (read1 (rx size (+<> off gptr1) ram1)))
                  (let ((base (skel-base skel)))
                    (let ((base (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                               (op-base h type base read))))
                      (let ((base1 (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                  (op-base h1 type base read1))))
                        (let ((value (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                    (if (whichtype w type) read value))))
                          (let ((value1 (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                       (if (whichtype w1 type) read1 value))))
                            (let ((skel (update-skel skel :base base1)))
                              (let ((skelx (skel base1 (g*-g*-induction gop1 base1 ram1 op base (skel-spec skel) ram))))
                                (let ((skel (if (ptr? type) skelx skel)))
                                  (let ((slot (update-slot slot :val value1 :skel skel)))
                                    (cons slot
                                          (g*-g*-induction gop1 gptr1 ram1 op ptr (cdr spec) ram))))))))))))))
          (cons slot
                (g*-g*-induction gop1 gptr1 ram1 op ptr (cdr spec) ram))))
    nil))

(defthm g*-spec-with-x*-spec
  (implies
   (and
    (or (g-op gop1) (x? gop2))
    (op-which-subbagp-< gop2 gop1))
   (equal (g*-spec gop1 gptr1 (g*-spec gop2 gptr2 spec ram2) ram1)
          (g*-spec gop1 gptr1 spec ram1)))
  :hints (("goal" :induct (g*-g*-induction gop1 gptr1 ram1 gop2 gptr2 spec ram2)
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :in-theory (e/d (g?) (numwhich numtype)))
          ))

(defun w-nil? (op)
  (equal (op-which op) :nil))

(defthm h*-spec-of-g*-spec-reduction
  (implies
   (and
    (x-op hop)
    (w-nil? hop)
    (not (w-nil? gop))
    )
   (equal (h*-spec hop (g*-spec gop gptr spec ram))
          (h*-spec hop (g*-spec (update-op gop :which :nil) gptr spec ram))))
  :hints (("goal"  :induct (g*-spec gop gptr spec ram)
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :in-theory (enable g?))
          ))


;; ====================================================
;;
;; split-blk
;;
;; ====================================================

(defun fix-slot (slot)
  (declare (type (satisfies slot-p) slot))
  (let ((size  (slot-size slot))
        (value (slot-val  slot))
        (type  (slot-type slot))
        (skel  (slot-skel slot)))
    (let ((skel (if (ptr? type)
                    (let ((base (skel-base skel)))
                      (update-skel skel :base (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                                                     (ifix base)
                                                     )))
                  skel)))
      (update-slot slot
                   :val (acl2::loghead (gacc::fix-size size) ;wfixn 8 size
                               (ifix value)
                               )
                   :skel skel))))

;bzo will these let us disable fix-slot?
(defthm slot-type-of-fix-slot
 (equal (slot-type (fix-slot slot))
        (slot-type slot))
 :hints (("Goal" :in-theory (enable slot-type fix-slot slot))))

(defthm slot-size-of-fix-slot
 (equal (slot-size (fix-slot slot))
        (slot-size slot))
 :hints (("Goal" :in-theory (enable slot-size fix-slot slot))))

(defthm slot-off-of-fix-slot
 (equal (slot-off (fix-slot slot))
        (slot-off slot))
 :hints (("Goal" :in-theory (enable slot-off fix-slot slot))))


(defun split-blk (spec)
  (declare (type (satisfies wf-spec) spec))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((slot (fix-slot slot)))
              (let ((type (slot-type slot))
                    (skel (slot-skel slot)))
                (if (ptr? type)
                    (let ((base (skel-base skel)))
                      (let ((line (line base skel)))
                        (let ((slot (update-slot slot :skel (skel base nil))))
                          (met ((spec list) (split-blk (cdr spec)))
                               (mv (cons slot spec)
                                   (cons line list))))))
                  (met ((spec list) (split-blk (cdr spec)))
                       (mv (cons slot spec) list)))))
          (met ((spec list) (split-blk (cdr spec)))
               (mv (cons slot spec) list))))
    (mv spec nil)))

(defun join-blk (spec list)
  (declare (type (satisfies wf-spec) spec))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((type (slot-type slot)))
              (if (and (ptr? type)
                       (consp list))
                  (let ((line (car list)))
                    (if (line-p line)
                        (let ((slot (update-slot slot :skel (line-skel line))))
                          (cons slot
                                (join-blk (cdr spec) (cdr list))))
                      (cons slot
                            (join-blk (cdr spec) list))))
                (cons slot
                      (join-blk (cdr spec) list))))
          (cons slot
                (join-blk (cdr spec) list))))
    spec))

(defthm join-blk-split-blk
  (implies
   (equal (h*-spec (op :all :x) spec)
          spec)
   (equal (join-blk (v0 (split-blk spec))
                    (v1 (split-blk spec)))
          spec))
  :hints (("goal" :in-theory (enable skel-extensionality!)
           :induct (split-blk spec))))

(defun f*-blk (fop ptr spec)
  (met ((spec list) (split-blk spec))
       (append (f*-spec fop ptr spec)
               (f*-list fop list))))


(defthm f*-blk-perm
  (implies
   (x? fop)
   (perm (f*-spec fop ptr spec)
         (f*-blk  fop ptr spec)))
  :hints (("goal'" :induct (split-blk spec))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
                         :do-not-induct t))))

(defthm f*-blk-perm?
  (implies (and (x? fop)
                (equal v (f*-blk  fop ptr spec)))
           (equal (perm (f*-spec fop ptr spec) v) t))
  :hints (("goal" :use (:instance f*-blk-perm)
           :in-theory nil)))

(defthm v0-split-blk-over-g*-spec
  (equal (v0 (split-blk (g*-spec gop ptr skel ram)))
         (g*-spec gop ptr (v0 (split-blk skel)) ram))
  :hints (("goal" :induct (split-blk skel))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
                         :do-not-induct t))))

(defthm v1-split-blk-over-g*-spec
  (implies
   (x? gop)
   (equal (v1 (split-blk (g*-spec gop ptr skel ram)))
          (g*-list gop (v1 (split-blk skel)) ram)))
  :hints (("goal" :induct (split-blk skel))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
                         :do-not-induct t))))


(defun s*-blk (sop ptr spec ram)
  (met ((spec list) (split-blk spec))
       (let ((ram (s*-spec sop ptr spec ram)))
         (s*-list sop list ram))))

(defthm disjoint-f*-cdr-reduction
  (implies
   (x? fop)
   (and (equal (disjoint (flat (f*-spec fop fptr (cdr spec))) y)
               (disjoint (flat (f*-blk fop fptr (cdr spec))) y))
        ;(equal (disjoint y (flat (f*-spec fop fptr (cdr spec))))
        ;       (disjoint y (flat (f*-blk fop fptr (cdr spec)))))
        ))
  :hints (("goal" :in-theory (disable f*-blk x? bag::flat-append))))

(in-theory
 (disable
  f*-blk-perm
  ))

(defthm s*-blk-implements-s*-spec
  (implies
   (and
    (x? sop)
    (unique (flat (f*-blk sop sptr spec)))
    )
   (equal (s*-blk sop sptr spec ram)
          (s*-spec sop sptr spec ram)))
  :hints (("goal'" :in-theory (enable flat)
           :induct (split-blk spec))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
                         :in-theory (disable numwhich)
                         :do-not-induct t))))
(in-theory
 (disable
  f*-blk-perm?
  s*-blk-implements-s*-spec
  disjoint-f*-cdr-reduction
  ))

;; ====================================================
;;
;; split-list
;;
;; ====================================================

(defun key-lst (list)
  (if (consp list)
      (let ((line (car list)))
        (if (line-p line)
            (cons (line-key line)
                  (key-lst (cdr list)))
          (key-lst (cdr list))))
    nil))

(defun split-lst (key list)
  (if (consp list)
      (let ((line (car list)))
        (if (line-p line)
            (let ((ptr (line-key line)))
              (if (equal ptr key)
                  (let ((skel (line-skel line)))
                    (let ((line (update-line line :skel (skel (skel-base skel) nil))))
                      (mv skel (cons line (cdr list)))))
                (met ((skel list) (split-lst key (cdr list)))
                     (mv skel (cons line list)))))
          (met ((skel list) (split-lst key (cdr list)))
               (mv skel (cons line list)))))
    (mv nil list)))

(defun join-lst (key skel list)
  (if (consp list)
      (let ((line (car list)))
        (if (line-p line)
            (let ((ptr (line-key line)))
              (if (equal ptr key)
                  (let ((line (update-line line :skel skel)))
                    (cons line (cdr list)))
                (cons line (join-lst key skel (cdr list)))))
          (cons line
                (join-lst key skel (cdr list)))))
    list))

(defthm join-lst-split-lst
  (equal (join-lst key
                   (v0 (split-lst key list))
                   (v1 (split-lst key list)))
         list))

(defun f*-lst (fop key list)
  (met ((skel list) (split-lst key list))
       (append (f*-spec fop (skel-base skel) (skel-spec skel))
               (f*-list fop list))))

(defthm f*-lst-perm
  (implies
   (x? fop)
   (perm (f*-lst fop key list)
         (f*-list fop list)))
  :hints (("goal'" :induct (split-lst key list))))

(defthm f*-lst-perm?
  (implies
   (and (x? fop)
        (bind-free (list (cons 'term v)) (term))
        (equal v term)
        (equal term (f*-lst fop key list)))
   (equal (perm (f*-list fop list) v)
          t))
  :hints (("goal" :in-theory (disable f*-lst))))

(defthm v0-split-lst-over-g*-spec
  (implies
   (memberp key (key-lst list))
   (equal (v0 (split-lst key (g*-list gop list ram)))
          (let ((skel (v0 (split-lst key list))))
            (let ((base (cond
                         ((equal (op-how gop) :z) 0)
                         ((equal (op-how gop) :x) (skel-base skel))
                         (t                       key))))
              (skel base (g*-spec gop base (skel-spec skel) ram))))))
  :hints (("goal" :induct (split-lst key list)
           :do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :expand  (G*-LIST GOP LIST RAM)
           :in-theory (enable memberp))
          ))

(defthm v1-split-lst-over-g*-spec
  (equal (v1 (split-lst key (g*-list gop list ram)))
         (g*-list gop (v1 (split-lst key list)) ram))
  :hints (("goal" :induct (split-lst key list))))

(defun s*-lst (sop key list ram)
  (met ((skel list) (split-lst key list))
       (let ((ram (s*-list sop list ram)))
         (s*-spec sop (skel-base skel) (skel-spec skel) ram))))

(in-theory
 (disable
  f*-lst-perm
  ))

(defthm s*-lst-implements-s*-list
  (implies
   (and
    (x? sop)
    (unique (flat (f*-lst sop key list)))
    )
   (equal (s*-lst sop key list ram)
          (s*-list sop list ram)))
  :hints (("goal'" :induct (split-lst key list))))

(defun which-disjoint (op1 op2)
  (declare (type (satisfies op-p) op1 op2))
  (let ((nw1 (numwhich (op-which op1)))
        (nw2 (numwhich (op-which op2))))
    (equal (logand nw1 nw2) 0)))

(defun h*-g*-op (op1 op2)
  (if (x? op1) (update-op op1 :how (op-how op2))
    (update-op op1)))

(defun h*-g*-hyp (hop gop)
  (and (which-disjoint hop gop)
       (implies (g-op gop) (and (or (not (optype hop :ptr))
                                    (not (optype gop :ptr)))
                                (equal (op-how hop) :z)))
       (implies (g-op hop) (not (optype gop :ptr)))))

(defthm min-self
  (equal (min x x)
         x)
  :hints (("Goal" :in-theory (enable min))))

(defthm min-known-1
  (implies (and (<=  x y)
                (acl2-numberp x)
                (acl2-numberp y))
           (equal (min x y)
                  x))
  :hints (("Goal" :cases ((ACL2-NUMBERP X))
           :in-theory (enable min))))

(defthm min-known-2
  (implies (and (<= y x)
                (acl2-numberp x)
                (acl2-numberp y))
           (equal (min x y)
                  y))
  :hints (("Goal" :cases ((ACL2-NUMBERP X))
           :in-theory (enable min))))

(defthm op-base-of-z-and-ptr
  (equal (OP-BASE :Z :PTR base valu)
         0))

(defthm op-base-equal-same-h-and-type-rewrite
  (equal (equal (OP-BASE H TYPE BASE1 VALU1) (OP-BASE H TYPE BASE2 VALU2))
         (if (or (not (equal type :ptr))
                 (equal h :x))
             (equal base1 base2)
           (if (equal h :z)
               t
             (equal valu1 valu2)))))

(defthm h*-spec-of-g*-spec
  (implies (h*-g*-hyp hop gop)
           (equal (h*-spec hop (g*-spec gop gptr spec ram))
                  (h*-spec (h*-g*-op hop gop) spec)))
  :hints (("subgoal *1/2"
           :in-theory (e/d (g?)
                           (OPEN-H*-SPEC
                            ;CAR-H*-SPEC
                            ;;NFIX
                            numwhich
                            op-base
                            whichnum
                            numtype
                            ATOMIC-H*-OP-REPLACEMENT
                            SLOT-EXTENSIONALITY!!
                            min
                            WX-OF-RX
                            ;; ACL2::LOGAND-WITH-MASK-ERIC
                            ACL2::UNSIGNED-BYTE-P-LOGHEAD-FORWARD-CHAINING ;bzo
                            ACL2::LOGHEAD-NONNEGATIVE-LINEAR
                            ACL2::LOGHEAD-LEQ
                            ;;g-op
                            ;;x?
                            )))
          ("goal" :induct (g*-spec gop gptr spec ram)
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :expand ((:free (x)  (H*-SPEC x SPEC)))
           :in-theory (e/d (g?) (OPEN-H*-SPEC
                                 FIXED-SPEC-P
                                 G*-SPEC-TO-H*-SPEC
                                 ATOMIC-G*-OP-REPLACEMENT
                                 ;;NFIX
                                 ;;numwhich
                                 ;;op-base
                                 whichnum
                                 numtype
                                 ATOMIC-H*-OP-REPLACEMENT
                                 SLOT-EXTENSIONALITY!!
                                 min
                                 WX-OF-RX
                                 ;; ACL2::LOGAND-WITH-MASK-ERIC
                                 ACL2::UNSIGNED-BYTE-P-LOGHEAD-FORWARD-CHAINING ;bzo
                                 ACL2::LOGHEAD-NONNEGATIVE-LINEAR
                                 ACL2::LOGHEAD-LEQ
                                 ;;g-op
                                 ;;x?
                                 ))
           :do-not-induct t
           )))

;; Read the bytes from RAM that reside at the addresses in LIST.  Return a
;; list of the bytes in the same order as the addresses.  bzo disable this?
;;

(defund rd-list (list ram)
  (declare (type t list ram))
  (if (consp list)
      (cons (rd (car list) ram)
            (rd-list (cdr list) ram))
    nil))

(defthm rd-list-append
  (equal (rd-list (append x y) ram)
         (append (rd-list x ram)
                 (rd-list y ram)))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm len-rd-list
  (equal (len (rd-list list ram))
         (len list))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm car-of-rd-list
  (equal (car (rd-list lst ram))
         (if (consp lst)
             (rd (car lst) ram)
           nil))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm consp-of-rd-list
  (equal (consp (rd-list lst ram))
         (consp lst))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm cdr-of-rd-list
  (equal (cdr (rd-list list ram))
         (if (endp list)
             nil
           (rd-list (cdr list) ram)))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm integer-listp-of-rd-list
  (integer-listp (rd-list list ram))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm rd-list-of-singleton
  (equal (rd-list (list ad) ram)
         (list (rd ad ram)))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm rd-list-of-cons
  (equal (rd-list (cons ad ads) ram)
         (cons (rd ad ram) (rd-list ads ram)))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm rd-list-when-ads-is-not-a-consp
  (implies (not (consp ads))
           (equal (rd-list ads ram)
                  nil))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm nthcdr-of-rd-list
  (equal (nthcdr n (rd-list ads ram))
         (rd-list (nthcdr n ads) ram))
  :hints (("Goal" :in-theory (enable nthcdr rd-list))))

(defthm nth-of-rd-list
  (equal (nth n (rd-list ads ram))
         (if (< (nfix n) (len ads))
             (rd (nth n ads) ram)
           nil))
  :hints (("Goal" :in-theory (enable nth))))

(defthm firstn-of-rd-list
  (equal (firstn n (rd-list ads ram))
         (rd-list (firstn n ads) ram))
  :hints (("Goal" :in-theory (enable rd-list (:induction firstn)))))

;;
;; WR-LIST
;;
;;
;; Write to RAM each value from VALS at the corresponding address from LIST.
;; Stop when you run out of addresses.
;;
;; Note that once VALS runs out we use nil as the value for each subsequent
;; write.  You may think we should write 0's instead, but wr treats nil as a 0
;; when writing it.
;;
;;I changed this to not stop when vals runs out.  A key property of wr-list is
;;that we should be able to tell what addresses get changes just by looking at
;;LIST -- not by looking at VALS.  (Consider the case in which we call wr with
;;some address ad and then call wr-list with a list of addresses that contains
;;ad.  We should be able to prove that the call to wr can be dropped, and we
;;don't want to consider the case when the call to wr-list ends early because
;;it runs out of values. I proved that the new and old behvior is identical in
;;the one place in the regression suite that wr-list is called by another
;;defun. -ews
;;
;bzo rename list param to ads?
;bzo disable

;bzo give a fast body?
(defund wr-list (list vals ram)
  (declare (type t list ram)
           (type (satisfies true-listp) vals))
  (if (and (consp list)
           ;(consp vals)
           )
      (wr (car list) (car vals)
          (wr-list (cdr list) (cdr vals) ram))
    ram))

(defthmd open-wr-list
  (implies
   (consp list)
   (equal (wr-list list vals ram)
          (wr (car list) (car vals)
              (wr-list (cdr list) (cdr vals) ram))))
  :hints (("goal" :in-theory (enable wr-list))))

(defthm wr-list-of-cons-one
  (equal (wr-list (cons ad ads) vals ram)
         (wr ad (car vals)  (wr-list ads (cdr vals) ram)))
  :hints (("Goal" :in-theory (enable wr-list))))

(defthm wr-list-of-cons-two
  (equal (wr-list ads (cons v vals) ram)
         (if (consp ads)
             (wr (car ads) v (wr-list (cdr ads) vals ram))
           ram))
  :hints (("Goal" :in-theory (enable wr-list))))

(defthm wr-list-of-cons-and-cons
  (equal (wr-list (cons ad list) (cons val vals) ram)
         (wr ad val (wr-list list vals ram))))

(defthm wr-list-when-ads-is-not-a-consp
  (implies (not (consp ads))
           (equal (wr-list ads vals ram)
                  ram))
  :hints (("Goal" :in-theory (enable wr-list))))

(defthm wr-list-over-wr
  (implies (not (memberp x list))
           (equal (wr-list list vals (wr x v ram))
                  (wr x v (wr-list list vals ram))))
  :hints (("Goal" :in-theory (enable list::memberp-of-cons wr-list))))

(defthm wr-list-append
  (implies (and (disjoint x y)
                (equal (len x)
                       (len a)))
           (equal (wr-list (append x y) (append a b) ram)
                  (wr-list y b (wr-list x a ram))))
  :hints (("goal" :induct (list::len-len-induction x a)
           :in-theory (enable disjoint binary-append))))

(defthm rd-list-of-wr-irrel
  (implies (not (list::memberp ad ads))
           (equal (rd-list ads (wr ad v ram))
                  (rd-list ads ram)))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm wfixlist-rd-list
  (equal (wfixlist (rd-list list ram))
         (rd-list list ram))
  :hints (("Goal" :in-theory (enable wfixlist rd-list))))

;; (thm
;;  (equal (wr-list ads v1 (wr-list ads v2 ram))
;;         (wr-list ads v1 ram))
;;  :hints (("Goal" :in-theory (enable wr==r!))))

;bzo move
(defthm wr-list-of-wr-same
  (implies (memberp x list)
           (equal (wr-list list vals (wr x v ram))
                  (wr-list list vals ram)))
  :hints (("Goal" :in-theory (enable wr-list))))





;bzo move
(defthm wr-list-of-wr-list-subbagp
  (implies (bag::subbagp ads2 ads1)
           (equal (wr-list ads1 vals1 (wr-list ads2 vals2 ram))
                  (wr-list ads1 vals1 ram)))
  :Hints (("Goal" :induct (wr-list ads2 vals2 ram)
           :in-theory (enable wr-list)
           )))

(defthm wr-list-of-what-was-already-there
  (implies (equal vals (rd-list ads ram))
           (equal (wr-list ads vals ram)
                  ram))
  :hints (("Goal" :in-theory (enable wr-list))))

(defthm wr-list-of-what-was-already-there-cheap
  (equal (wr-list ads (rd-list ads ram) ram)
         ram))

(defthm wfixedlist-of-rd-list
  (wfixedlist (rd-list ads ram))
  :hints (("Goal" :in-theory (enable wfixedlist rd-list)))
  )


(defthm wr-list-of-wr-list-diff
  (implies (bag::disjoint list1 list2)
           (equal (wr-list list1 vals1 (wr-list list2 vals2 ram))
                  (wr-list list2 vals2 (wr-list list1 vals1 ram))))
  :hints (("Goal" :in-theory (enable wr-list))))

(defthm rd-of-wr-list-diff
  (implies (not (memberp ad ads))
           (equal (rd ad (wr-list ads val ram))
                  (rd ad ram)))
  :hints (("Goal" :in-theory (enable wr-list))))

(defthm rd-list-of-wr-list-diff
  (implies (bag::disjoint ads1 ads2)
           (equal (rd-list ads1 (wr-list ads2 vals ram))
                  (rd-list ads1 ram)))
  :hints (("Goal" :in-theory (enable wr-list))))


;; (defun clr-list (ads ram)
;;   (if (endp ads)
;;       ram
;;     (clr-list (cdr ads) (clr (car ads) ram))))

(defun clr-list (ads ram)
  (if (consp ads)
      (clr-list (cdr ads) (memory-clr (car ads) ram))
    ram))

(defthmd open-clr-list
  (implies
   (consp ads)
   (equal (clr-list ads ram)
          (clr-list (cdr ads) (memory-clr (car ads) ram)))))

(defthmd clr-list-over-memory-clr
  (equal (clr-list list (memory-clr x r))
         (memory-clr x (clr-list list r)))
  :hints (("Subgoal *1/1" :cases ((equal x (car list))))))

#+joe
(defund clr-list (ads ram)
  (wr-list ads nil ram))

(defthm clr-list-when-ads-is-not-a-consp
  (implies (not (consp ads))
           (equal (clr-list ads ram)
                  ram))
  :hints (("Goal" :in-theory (enable clr-list))))



(defthm clr-list-of-wr-list-same
  (equal (clr-list ads (wr-list ads vals ram1))
         (clr-list ads ram1))
  :hints (("Goal" :in-theory (enable clr-list-over-memory-clr wr-list open-wr-list open-clr-list))))

(defthm clr-list-of-cons
  (equal (clr-list (cons ad ads) ram)
         (memory-clr ad (clr-list ads ram)))
  :hints (("Goal" :in-theory (enable clr-list-over-memory-clr  clr-list))))

(defthm clr-list-of-wr-cover
  (implies (list::memberp ad ads)
           (equal (clr-list ads (wr ad val ram))
                  (clr-list ads ram)))
  :hints (("Goal" :in-theory (enable clr-list))))

(local (defun my-induct (ads vals ram)
         (if (endp ads)
             (list ads vals ram)
           (my-induct (cdr ads) (cdr vals) (wr (car ads) (car vals) ram)))))

;; The unique hyp is necessary (unless we are willing to make the RHS more
;; complicated).  Consider: (rd-list '(0 0 0) (wr-list '(0 0 0) '(1 2 3) nil))
;; = (1 1 1)
;;
(defthm rd-list-of-wr-list-same
  (implies (bag::unique ads)
           (equal (rd-list ads (wr-list ads vals ram))
                  (my-wfixlist (len ads) vals)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable rd-list wr-list my-wfixlist)
           :induct (my-induct ads vals ram))))


;version for rd-list?
(defthm rd-subst-when-wr-list-equal
  (implies (and (equal (wr-list ads v ram1)
                       (wr-list ads v ram2))
                (syntaxp (acl2::smaller-term ram2 ram1))
                (not (memberp ad ads)))
           (equal (rd ad ram1)
                  (rd ad ram2)))
  :hints (("Goal" :use ((:instance rd-of-wr-list-diff (val v) (ram ram1))
                        (:instance rd-of-wr-list-diff (val v) (ram ram2))))))

(defthm wr-list-subst-wr-list
  (implies (and (equal (wr-list ads1 v1 ram1)
                       (wr-list ads1 v1 ram2))
                (syntaxp (acl2::smaller-term ram1 ram2))
                (subbagp ads1 ads2))
           (equal (wr-list ads2 v2 ram2)
                  (wr-list ads2 v2 ram1)))
  :hints (("Goal" :use ((:instance wr-list-of-wr-list-subbagp (ads1 ads2) (ads2 ads1) (vals1 v2) (vals2 v1) (ram ram2))
                        (:instance wr-list-of-wr-list-subbagp (ads1 ads2) (ads2 ads1) (vals1 v2) (vals2 v1) (ram ram1)))
           :do-not '(generalize eliminate-destructors)
           :in-theory (disable wr-list-of-wr-list-subbagp))))

;It's a bit odd to replace vals with NIL, since NIL has a shorter length, but
;we do it anyway...
;
(defthm wr-list-equal-rewrite-vals-to-nil
  (implies (syntaxp (not (equal vals ''nil)))
           (equal (equal (wr-list ads vals ram2) (wr-list ads vals ram1))
                  (equal (wr-list ads nil ram2) (wr-list ads nil ram1)))))


;gen the len of ads?
(defthm wr-list-of-my-wfixlist
  (equal (wr-list ads (my-wfixlist (len ads) vals) ram)
         (wr-list ads vals ram))
  :hints (("Goal" :in-theory (enable wr-list my-wfixlist))))

(defthm wr-list-subst-vals
  (implies (and (equal (my-wfixlist (len ads) vals1)
                       (my-wfixlist (len ads) vals2))
                (syntaxp (acl2::smaller-term vals2 vals1)))
           (equal (wr-list ads vals1 ram)
                  (wr-list ads vals2 ram)))
  :hints (("Goal" :use ((:instance wr-list-of-my-wfixlist (vals vals1))
                        (:instance wr-list-of-my-wfixlist (vals vals2)))
           :in-theory (disable wr-list-of-my-wfixlist) )))


;; The (unique ads) hyp is necessary.  If ads contains duplicates but the
;; corresponding values in vals don't agree, then (my-wfixlist (len ads) vals)
;; will contain an incorrect value....
;bzo explain this better
;;

(defthmd wr-list-nil-to-clr-list
  (equal (wr-list ads nil ram)
         (clr-list ads ram))
  :hints (("goal" :in-theory (e/d (wr-list memory-clr)
                                  (wr==r!)))))

(defthm wr-list-equal-rewrite
  (implies (unique ads)
           (equal (equal (wr-list ads vals ram1) ram2)
                  (and (equal (my-wfixlist (len ads) vals)
                              (rd-list ads ram2))
                       (equal (clr-list ads ram1)
                              (clr-list ads ram2)))))
  :hints (("Goal" :use (:instance wr-list-of-what-was-already-there-cheap (ram ram2))
           :in-theory (e/d (wr-list-nil-to-clr-list clr-list)
                           (wr-list-of-what-was-already-there
                            wr-list-of-what-was-already-there-cheap)))))

;;
;; logapp-list
;;

;Append j to each element of i-list.  I'm not thrilled with the order of the
;parameters here (I think j should come first, but they match the order for
;logpp).
(defund logapp-list (size i-list j)
  (declare (xargs :guard (integer-listp i-list))
           (type integer j)
           (type (integer 0 *) size))
  (if (consp i-list)
      (cons (logapp size (car i-list) j)
            (logapp-list size (cdr i-list) j))
    nil))

(defthm integer-listp-of-logapp-list
  (integer-listp (logapp-list size i-list j))
  :hints (("Goal" :in-theory (enable logapp-list))))

(defthm logapp-list-of-cons
  (equal (logapp-list size (cons i i-list) j)
         (cons (logapp size i j) (logapp-list size i-list j)))
  :hints (("Goal" :in-theory (enable logapp-list))))

(defthm consp-of-logapp-list
  (equal (consp (logapp-list size i-list j))
         (consp i-list))
  :hints (("Goal" :in-theory (enable logapp-list))))

(defthm car-of-logapp-list
  (equal (car (logapp-list size i-list j))
         (if (consp i-list)
             (logapp size (car i-list) j)
           nil))
  :hints (("Goal" :in-theory (enable logapp-list))))

(defthm cdr-of-logapp-list
  (equal (cdr (logapp-list size i-list j))
         (logapp-list size (cdr i-list) j))
  :hints (("Goal" :in-theory (enable logapp-list))))

(defthm logapp-list-when-i-list-is-not-a-consp
  (implies (not (consp i-list))
           (equal (logapp-list size i-list j)
                  nil))
  :hints (("Goal" :in-theory (enable logapp-list))))

(defthm logapp-list-when-j-is-not-an-integerp
  (implies (not (integerp j))
           (equal (logapp-list size i-list j)
                  (logapp-list size i-list 0)))
  :hints (("Goal" :in-theory (enable logapp-list))))

(defthm len-of-logapp-list
  (equal (len (logapp-list size i-list j))
         (len i-list))
  :hints (("Goal" :in-theory (enable logapp-list))))

(defthm nthcdr-of-logapp-list
  (equal (nthcdr n (logapp-list size ilist j))
         (logapp-list size (nthcdr n ilist) j))
  :hints (("Goal" :in-theory (enable nthcdr logapp-list))))

(defthm not-memberp-of-logapp-list
  (implies (not (equal (ifix j1) (ifix j2)))
           (not (list::memberp (logapp '16 offset1 j1) (logapp-list '16 vals j2))))
  :hints (("Goal" :in-theory (enable logapp-list
                                     acl2::equal-logapp-x-y-z))))

;move
(defthmd NTH-0-BECOMES-CAR-gen
  (implies (zp n)
           (equal (NTH N VALS)
                  (car vals))))

(defthm nth-of-logapp-list
  (equal (nth n (logapp-list size vals j))
         (if (< (nfix n) (len vals))
             (logapp size (nth n vals) j)
           nil))
  :hints (("Goal" :induct t
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (LIST::NTH-0-BECOMES-CAR
                             NTH-0-BECOMES-CAR-gen
                            (:induction nth)
                            logapp-list)
                           ( ACL2::EQUAL-LOGAPP-X-Y-Z ;bzo
                            ACL2::EQUAL-LOGAPP-X-Y-Z-CONSTANTS
                            )))))

;; unique of logapp-list?


;;
;; LOGEXT-LIST
;;

(defund logext-list (size i-list)
  (declare (xargs :guard (integer-listp i-list))
           (type (integer 1 *) size))
  (if (consp i-list)
      (cons (acl2::logext size (car i-list))
            (logext-list size (cdr i-list)))
    nil))

(defthm len-of-logext-list
  (equal (len (logext-list size i-list))
         (len i-list))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm consp-of-logext-list
  (equal (consp (logext-list size i-list))
         (consp i-list))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm car-of-logext-list
  (equal (car (logext-list size i-list))
         (if (consp i-list)
             (acl2::logext size (car i-list))
           nil))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm cdr-of-logext-list
  (equal (cdr (logext-list size i-list))
         (logext-list size (cdr i-list)))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm logext-list-of-cons
 (equal (logext-list size (cons i i-list))
        (cons (acl2::logext size i) (logext-list size i-list)))
 :hints (("Goal" :in-theory (enable logext-list))))

(defthm nthcdr-of-logext-list
  (equal (nthcdr n (logext-list size ads))
         (logext-list size (nthcdr n ads)))
  :hints (("Goal" :in-theory (enable nthcdr logext-list))))

;;
;; LOGCDR-LIST
;;

(defun logcdr-list (vals)
  (if (endp vals)
      nil
    (cons (acl2::logcdr (car vals))
          (logcdr-list (cdr vals)))))

;;
;; IFIX-LIST
;;

(defun ifix-list (vals)
  (if (endp vals)
      vals ;return nil instead?
    (cons (ifix (car vals)) (ifix-list (cdr vals)))))

(defthm ifix-list-does-nothing
  (implies (integer-listp vals)
           (equal (ifix-list vals)
                  vals)))

(defthm integer-listp-of-logext-list
  (integer-listp (logext-list n x))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm logcdr-list-of-append
  (equal (gacc::logcdr-list (append x y))
         (append (gacc::logcdr-list x)  (gacc::logcdr-list y))))

;;
;; LOGHEAD-LIST
;;

(defun loghead-list (size i-list)
  (declare (xargs :guard (integer-listp i-list))
           (type (integer 1 *) size))
  (if (endp i-list)
      nil
    (cons (loghead size (car i-list))
          (loghead-list size (cdr i-list)))))

(defthm loghead-list-of-append
  (equal (gacc::loghead-list n (append x y))
         (append (gacc::loghead-list n x)
                 (gacc::loghead-list n y))))

(defthm integer-listp-of-loghead-list
  (integer-listp (loghead-list size i-list))
  :hints (("Goal" :in-theory (enable loghead-list))))

(defthm loghead-list-when-n-is-not-an-integerp
  (implies (not (integerp n))
           (equal (loghead-list n x)
                  (repeat (len x) 0))))

(defthm memberp-of-logapp-and-logapp-list-hack
  (equal (list::memberp (logapp '16 offset denvr) (logapp-list '16 x denvr))
         (and (consp x)
              (list::memberp (loghead 16 offset) (loghead-list '16 x))))
  :hints (("Goal" :in-theory (enable logapp-list))))

(defthm logext-list-when-i-list-is-not-a-consp
  (implies (not (consp i-list))
           (equal (logext-list size i-list)
                  nil))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm memberp-of-logext-and-logext-list
  (implies (and (integerp n)
                (< 0 n))
           (equal (list::memberp (logext n a) (logext-list n x))
                  (list::memberp (loghead n a) (loghead-list n x)))))

(defthmd logapp-list-of-loghead
  (implies (and             ; (integer-listp i-list)
            (integerp size1)
            (integerp size2)
            (<= 0 size1)
            (<= 0 size2)
            )
           (equal (logapp-list size1 i-list (loghead size2 j))
                  (loghead-list (+ size1 size2)  (logapp-list size1 i-list j))))
  :hints (("Goal" :in-theory (e/d (logapp-list
                                   ACL2::LOGTAIL-LOGHEAD-BETTER)
                                  (ACL2::LOGHEAD-LOGTAIL)))))


(defthm logext-list-of-loghead-list
  (implies (and (integerp size)
                (< 0 size))
           (equal (logext-list size (loghead-list size vals))
                  (logext-list size vals)))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm logext-list-of-loghead-list-gen
  (implies (and (<= size1 size2)
                (< 0 size2)
                (integerp size1)
                (integerp size2)
                )
           (equal (logext-list size1 (loghead-list size2 vals))
                  (logext-list size1 vals)))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm logext-list-of-append
  (equal (logext-list size (append vals1 vals2))
         (append (logext-list size vals1) (logext-list size vals2)))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm nth-of-logext-list
  (equal (nth n (logext-list size vals))
         (if (< (nfix n) (len vals))
             (logext size (nth n vals))
           nil))
  :hints (("Goal" :in-theory (enable logext-list nth))))


;bzo dup?
(defun unsigned-byte-p-list (size vals)
  (if (endp vals)
      t
    (and (unsigned-byte-p size (car vals))
         (unsigned-byte-p-list size (cdr vals)))))

(defthm unsigned-byte-p-list-of-logapp-list-hack
  (implies (and (<= 0 denvr) ;drop?
                (integerp denvr))
           (equal (unsigned-byte-p-list 31 (logapp-list 16 i denvr))
                  (or (not (consp i))
                      (unsigned-byte-p 15 denvr))))
  :hints (("Goal" :in-theory (enable logapp-list))))





(defthm logext-list-of-logapp-list
  (implies (and (< size2 size)
                (integerp size)
                (integerp size2)
                (<= 0 size2)
                )
  (equal (logext-list size (logapp-list size2 x denvr))
         (logapp-list size2 x (logext (- size size2) denvr))))
  :hints (("Goal" :in-theory (enable logext-list logapp-list acl2::logext-logapp))))

;bzo nested inductions
(defthm disjoint-of-two-calls-to-logapp-list
  (equal (disjoint (logapp-list 16 x1 y1) (logapp-list 16 x2 y2))
         (or (not (equal (ifix y1) (ifix y2)))
             (disjoint (loghead-list 16 x1) (loghead-list 16 x2))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable logapp-list))))

(defthm logapp-list-when-j-is-zero
  (equal (logapp-list size vals 0)
         (loghead-list size vals)))

(defun logtail-list (pos ivals)
  (if (endp ivals)
      nil
    (cons (acl2::logtail pos (car ivals))
          (logtail-list pos (cdr ivals)))))


;bzo param aren't really envs
(defthm hack-for-code-data-clash
  (implies (not (memberp (loghead 15 (logtail 16 denvr)) (loghead-list 15 (logtail-list 17 cenvs))))
           (not (memberp (logapp 1 0 denvr) cenvs))))

(defthm hack-for-code-data-clash2
  (implies (not (memberp (loghead 15 (logtail 16 denvr)) (loghead-list 15 (logtail-list 17 cenvs))))
           (not (memberp (logapp 1 1 denvr) cenvs)))
  :hints (("Goal" :in-theory (e/d (ACL2::LOGTAIL-LOGHEAD-BETTER) (acl2::LOGHEAD-LOGTAIL)))))

;bzo gen
(defthm logtail-list-of-logapp-list-17-16
  (equal (logtail-list 17 (logapp-list 16 ivals j))
         (repeat (len ivals) (acl2::logcdr j))))

(defthm loghead-list-of-repeat-15
  (equal (loghead-list 15 (repeat n v))
         (repeat n  (loghead 15 v)))
  :hints (("Goal" :in-theory (enable loghead-list repeat))))

(defthm logapp-list-non-memberp-hack
  (implies (not (equal (loghead 15 j) (logtail 16 (loghead 31 (car y)))))
           (not (memberp (car y) (logapp-list 16 ivals j))))
  :hints (("Goal" :in-theory (enable logapp-list))))

(defthm disjoint-of-logapp-list-hack
  (implies (not (memberp (loghead 15 j) (loghead-list 15 (logtail-list 16 y))))
           (disjoint (logapp-list 16 ivals j) y))
  :hints (("Goal" :expand ((disjoint y (logapp-list 16 ivals j))))))

;bzo gen
(defthm logtail-list-of-logcdr-list
  (equal (logtail-list '16 (logcdr-list vals))
         (logtail-list 17 vals)))
;rr
(defthm count-of-logapp-list
  (implies (integer-listp vals)
           (equal (bag::count a (logapp-list 16 vals j))
                  (if (and (integerp a)
                           (equal (ifix j) (acl2::logtail 16 a)))
                      (bag::count (loghead 16 a) (loghead-list 16 vals))
                    0)))
  :hints (("Goal" :in-theory (enable logapp-list acl2::equal-logapp-x-y-z))))

(defthm memberp-of-loghead-list
  (implies (list::memberp a x)
           (list::memberp (loghead 16 a)
                          (loghead-list 16 x))))


(local (defun double-cdr-induct (x y)
  (if (endp x)
      (list x y)
    (double-cdr-induct (cdr x) (cdr y)))))

(defthm loghead-list-of-remove-1
  (implies (list::memberp a x)
           (bag::perm (loghead-list 16 (bag::remove-1 a x))
                      (bag::remove-1 (loghead 16 a)
                                     (loghead-list 16 x))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable list::memberp bag::remove-1 loghead-list))))


(defthm loghead-list-of-remove-1-both
  (bag::perm (LOGHEAD-LIST 16 (BAG::REMOVE-1 a x))
             (if (list::member a x)
                 (bag::remove-1 (loghead 16 a) (LOGHEAD-LIST 16 x) )
               (LOGHEAD-LIST 16 x))))

(defthm subbagp-of-two-loghead-list-calls
  (implies (bag::subbagp vals1 vals2)
           (bag::subbagp (loghead-list 16 vals1)
                         (loghead-list 16 vals2)))
  :hints (("Goal" :expand (bag::subbagp vals1 vals2)
           :induct t
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (loghead-list bag::subbagp) (bag::subbagp-cdr-remove-1-rewrite ;bzo
                                                        )))))

;move
(defthm subbagp-of-two-logapp-list-calls
  (implies (and (bag::subbagp vals1 vals2)
                (integer-listp vals1)
                (integer-listp vals2)
;               (integerp j)
                )
           (bag::subbagp (logapp-list '16 vals1 j)
                         (logapp-list '16 vals2 j)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (logapp-list) ( ;bag::memberp-of-remove-bag bag::subbagp-of-cons
                                          )))))

;bzo see loghead-list-of-logapp-list
;move up
(defthm loghead-list-of-logapp-list-same-size
  (equal (loghead-list size (logapp-list size vals j))
         (loghead-list size vals)))

;move bzo rename
(defthm disjoint-of-two-loghead-list-calls
  (implies (and (integerp n)
                (< 0 n))
           (equal (disjoint (logext-list n x)
                            (logext-list n y))
                  (disjoint (loghead-list n x)
                            (loghead-list n y)))))

(defthm loghead-list-does-nothing
  (implies (unsigned-byte-p-list width x)
           (equal (loghead-list width x)
                  (list::fix x)
                  ))
  :hints (("Goal" :in-theory (enable loghead-list))))

(defthm unique-of-logext-list
  (implies (and (integerp n) (< 0 n))
           (equal (unique (logext-list n x))
                  (unique (loghead-list n x)))))

(defthm loghead-list-of-loghead-list
  (equal (loghead-list n (loghead-list n vals))
         (loghead-list n vals)))

(defthm consp-of-loghead-list
  (equal (consp (loghead-list size i-list))
         (consp i-list))
  :hints (("Goal" :in-theory (enable loghead-list))))

(defthm car-of-loghead-list
  (equal (car (loghead-list size i-list))
         (if (consp i-list)
             (loghead size (car i-list))
           nil))
  :hints (("Goal" :in-theory (enable loghead-list))))

(defthm nthcdr-of-loghead-list
  (equal (nthcdr n (loghead-list size ads))
         (loghead-list size (nthcdr n ads)))
  :hints (("Goal" :in-theory (enable nthcdr loghead-list))))

(defthm nth-of-loghead-list
  (equal (nth n (loghead-list size vals))
         (if (< (nfix n) (len vals))
             (loghead size (nth n vals))
           nil))
  :hints (("Goal" :in-theory (enable loghead-list nth))))

;bzo kill the non-gen
(defthm loghead-list-of-logapp-list
  (implies (and (< size2 size)
                (integerp size)
                (integerp size2)
                (<= 0 size2))
           (equal (loghead-list size (logapp-list size2 x denvr))
                  (logapp-list size2 x (loghead (- size size2) denvr))))
  :hints
  (("Goal" :in-theory (enable loghead-list
                              logapp-list acl2::loghead-logapp))))

;adapt this to generalize  LOGHEAD-LIST-of-LOGAPP-LIST
;; (defthm logapp-list-of-loghead
;;   (implies (and             ; (integer-listp i-list)
;;             (integerp size1)
;;             (integerp size2)
;;             (<= 0 size1)
;;             (<= 0 size2)
;;             )
;;            (equal (logapp-list size1 i-list (loghead size2 j))
;;                   (loghead-list (+ size1 size2)  (logapp-list size1 i-list j))))
;;   :hints (("Goal" :in-theory (e/d (logapp-list
;;                                    ACL2::LOGTAIL-LOGHEAD-BETTER)
;;                                   (ACL2::LOGHEAD-LOGTAIL)))))

;;
;; WINTLIST
;;

;Convert the bytes in LIST to one big bit vector.
;Note that the bytes appearing first in LIST appear as the lower-order bytes of the result.
;Eric doesn't like the name of this.

;Eric replaced wcons with logapp.
(defund wintlist (list)
  (declare (xargs :guard (integer-listp list)))
  (if (consp list)
      (acl2::logapp 8 (car list) (wintlist (cdr list)))
    0))

(defthm wintlist-of-cons
  (equal (wintlist (cons byte byte-list))
         (acl2::logapp 8 byte (wintlist byte-list)))
  :hints (("Goal" :in-theory (enable wintlist))))

(defthm wintlist-when-list-is-not-a-consp
  (implies (not (consp list))
           (equal (wintlist list)
                  0))
  :hints (("Goal" :in-theory (enable wintlist))))

;could gen the 8?
(defthm loghead-8-of-wintlist
  (equal (acl2::loghead 8 (wintlist lst))
         (if (consp lst)
             (acl2::loghead 8 (car lst))
           0))
  :hints (("Goal" :expand (wintlist lst))))

;could gen the 8?
(defthm logtail8-of-wintlist
  (equal (acl2::logtail 8 (wintlist list))
         (if (endp list)
             0
           (wintlist (cdr list)))))

;bzo gen!
(defthm loghead-16-of-wintlist
  (equal (loghead 16 (wintlist byte-list))
         (wintlist (firstn 2 byte-list)))
  :hints (("Goal" :in-theory (enable wintlist))))

(defthm wintlist-equal-0-rewrite
  (equal (equal 0 (wintlist lst))
         (equal (loghead-list 8 lst)
                (repeat (len lst) 0))))

;;
;; ENLISTW
;;

;Return a list of the SIZE low-order bytes of V.  Note that the low-order
;bytes of V appear first in the resulting list.  I wanted to get rid of the
;size parameter but realized that would cause problems because we can't tell
;by looking at v what size it is (e.g., what size is 0?).  Eric isn't thrilled
;with the name of this.

;Eric replaced wcar with loghead and wcdr with logtail.
;bzo Add guards? (may require adding ifixes here until we improve the guards on loghead and logtail). -ews
(defund enlistw (size v)
  (declare (type integer v)
           (type (integer 0 *) size))
  (if (zp size)
      nil
    (cons (acl2::loghead 8 v)
          (enlistw (1- size) (acl2::logtail 8 v)))))

(defthm enlistw-when-size-is-not-an-integerp
  (implies (not (integerp size))
           (equal (enlistw size v)
                  nil))
  :hints (("Goal" :in-theory (enable enlistw))))

(defthm enlistw-when-size-is-non-positive
  (implies (<= size 0)
           (equal (enlistw size v)
                  nil))
  :hints (("Goal" :in-theory (enable enlistw))))

(defthm enlistw-when-size-is-one
  (equal (enlistw 1 v)
         (list (acl2::loghead 8 v)))
  :hints (("Goal" :in-theory (enable enlistw))))

(defthmd enlistw-constant-opener
  (implies (and (syntaxp (quotep k))
                (not (zp k)))
           (equal (enlistw k val)
                  (cons (loghead 8 val)
                        (enlistw (1- k) (logtail 8 val)))))
  :hints (("Goal" :in-theory (enable enlistw))))

;car and cdr of enlistw?

(defthm car-of-enlistw
  (equal (car (enlistw size v))
         (if (zp size)
             nil
           (acl2::loghead 8 v)))
  :hints (("Goal" :in-theory (enable enlistw))))

(defthm cdr-of-enlistw
  (equal (cdr (enlistw size v))
         (if (zp size)
             nil
           (enlistw (+ -1 size) (acl2::logtail 8 v))))
  :hints (("Goal" :expand (ENLISTW SIZE V))))

(defthm len-enlistw
  (equal (len (enlistw size v))
         (nfix size))
  :hints (("Goal" :in-theory (enable enlistw))))

(defthm consp-of-enlistw
  (equal (consp (enlistw size v))
         (not (zp size)))
  :hints (("Goal" :in-theory (enable enlistw))))

(defthm enlistw-of-1
  (equal (enlistw 1 v)
         (list (loghead 8 v)))
  :hints (("Goal" :expand  (enlistw 1 v)
           :in-theory (enable enlistw))))

(defthm enlistw-of-0
  (equal (enlistw size 0)
         (repeat size 0))
  :hints (("Goal" :in-theory (enable enlistw repeat))))

;; (defthm enlistw-when-v-is-zero
;;   (equal (ENLISTW size 0)
;;          ...))

(defthm enlistw-when-v-is-not-an-integerp
  (implies (not (integerp v))
           (equal (enlistw size v)
                  (enlistw size 0)))
  :hints (("Goal" :in-theory (enable enlistw))))

;bzo ACL2::FLOOR-FL and other rtl rules are around

;; Fix each element of LIST to be an 8-bit byte.
;bzo guard.
(defund wfixlist (list)
  (declare (xargs :guard (integer-listp list)))
  (if (consp list)
      (cons (acl2::loghead 8 ;wfixn 8 1
                           (car list)) ;should this be  (wfixn 8 8 (car list))?
            (wfixlist (cdr list)))
    nil))

;; Check that each element of LIST is an 8-bit byte.
(defund wfixedlist (list)
  (declare (type t list))
  (if (consp list)
      (and (acl2::unsigned-byte-p 8 ;wintn 8 1
                  (car list))  ;should this be  (wintn 8 8 (car list))?
           (wfixedlist (cdr list)))
    (null list) ;maybe we don't want to do this check, now that we have nice list congruences??
    ))

(defthm wfixedlist-of-cons
  (equal (wfixedlist (cons elem list))
         (and (unsigned-byte-p 8 elem)
              (wfixedlist list)))
  :hints (("Goal" :in-theory (enable wfixedlist))))

(defthm wfixedlist-of-nthcdr
  (implies (gacc::wfixedlist lst)
           (gacc::wfixedlist (nthcdr n lst)))
  :hints (("Goal" :in-theory (enable nthcdr gacc::wfixedlist))))

(defthm wfixedlist-of-append
  (implies (true-listp x) ;annoying
           (equal (gacc::wfixedlist (append x y))
                  (and (gacc::wfixedlist x)
                       (gacc::wfixedlist y)))))

(defthm wfixedlist-wfixlist
  (implies (wfixedlist list)
           (equal (wfixlist list)
                  list))
  :hints (("Goal" :in-theory (enable wfixedlist wfixlist))))

;(local (in-theory (enable wfixn-rewrite-to-loghead))) ;bzo

(defthm enlistw-wintlist
  (implies (equal size (len list))
           (equal (enlistw size (wintlist list))
                  (wfixlist list)))
  :hints (("Goal" :in-theory (enable ;wcar ;bzo
                              enlistw
                              wfixlist
                              wintlist
                                     ))))

(defthm wintnlist-enlistw
  (equal (wintlist (enlistw size v))
         (;wfixw 8 size
          acl2::loghead (* 8 (nfix size))
          v))
  :hints (("goal" :in-theory (enable ;wintn
                                     ;open-wfixw
                              enlistw
                              ;wfixlist
                              wintlist
                              ))))

;bzo move
;rename
(defthm subbagp-hack-eric
  (implies (and (consp list1)
                (memberp (car list1) list2))
           (equal (subbagp (remove-1 (car list1) list2)
                           (cdr list1))
                  (subbagp list2 list1)))
  :hints (("Goal" :in-theory (disable bag::subbagp-implies-subbagp-cons-common
                                      bag::subbagp-of-cons)
           :do-not '(generalize eliminate-destructors)
           :use (:instance bag::subbagp-implies-subbagp-cons-common
                           (bag::a (car list1)) (bag::y (cdr list1)) (bag::x  (remove (car list1) list2))))))

;bzo move
;bzo loops with bag::count-of-cdr
(defthmd count-of-car-same
  (equal (bag::count (car x) x)
         (if (consp x)
             (+ 1 (bag::count (car x) (cdr x)))
           0)))

;bzo move
(defthmd subbagp-expand
  (equal (subbagp list2 list1)
         (if (not (consp list1))
             (not (consp list2))
           (if (memberp (car list1) list2)
               (subbagp (remove-1 (car list1) list2) (cdr list1))
             (subbagp list2 (cdr list1))))))


(defthm unsigned-byte-of-wintlist-forward-chaining
  (unsigned-byte-p (* 8 (len byte-list)) (wintlist byte-list))
  :rule-classes ((:forward-chaining :trigger-terms ((wintlist byte-list))))
  :hints (("Goal" :in-theory (enable wintlist))))

(defthm unsigned-byte-of-wintlist
  (implies (and (<= (* 8 (len byte-list)) n)
                (integerp n))
           (unsigned-byte-p n (wintlist byte-list)))
  :hints (("Goal" :in-theory (enable wintlist))))

(defthm wfixedlist-of-enlistw
  (wfixedlist (enlistw numbytes v))
  :hints (("Goal" :in-theory (enable wfixedlist enlistw))))

(defthm enlistw-iff
  (iff (enlistw numbytes v)
       (not (zp numbytes)))
  :hints (("Goal" :in-theory (enable enlistw))))

(defthm enlistw-of-one-more
  (implies (and (syntaxp (not (quotep size))) ;don't unify (+ 1 size) with constants..
                (integerp size)
                (<= 0 size))
           (equal (ENLISTW (+ 1 size) v)
                  (CONS (LOGHEAD 8 V)
                        (ENLISTW SIZE (LOGTAIL 8 V)))))
  :hints (("Goal" :in-theory (enable enlistw))))

(defthm wfixedlist-when-byte-list-is-not-a-consp
  (implies (not (consp byte-list))
           (equal (wfixedlist byte-list)
                  (equal nil byte-list)
                  ))
  :hints (("Goal" :in-theory (enable wfixedlist))))

(defund my-wfixlist (numbytes byte-list)
  (if (zp numbytes)
      nil
    (cons (loghead 8 (car byte-list))
          (my-wfixlist (+ -1 numbytes) (cdr byte-list)))))

(defthm my-wfixlist-when-numbytes-is-not-positive
  (implies (<= numbytes 0)
           (equal (my-wfixlist numbytes byte-list)
                  nil))
  :hints (("Goal" :in-theory (enable my-wfixlist))))

;gen the numbytes
(defthm my-wfixlist-of-enlistw
  (equal (my-wfixlist numbytes (enlistw numbytes v))
         (enlistw numbytes v))
  :hints (("Goal" :in-theory (enable my-wfixlist enlistw))))


;no nice lemma for rd of wr-list?  well,, you get the nth val of vals, where n is the posn of ad in ads...
;this is all probably okay?  we can implement rx/wx functionality easily enough?


(defun enlistw-n-induct (size n v)
  (if (zp size)
      (+ n v)
      (enlistw-n-induct (1- size)(1- n) (logtail 8 v))))

(defthm nth-of-enlistw
  (implies (and (< n numbytes)
                (acl2::natp n)
                (acl2::natp numbytes)
                (integerp v)
                )
           (equal (nth n (enlistw numbytes v))
                  (loghead 8 (logtail (* 8 n) v))))
  :hints (("Goal" :induct (ENLISTW-n-induct numbytes n v)
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable enlistw))))


(defun cdr-and-sub1-induct (x n)
  (if (endp x)
      (list x n)
    (cdr-and-sub1-induct (cdr x) (+ -1 n))))

(defthm logtail-of-wintlist
  (implies (integerp n) ;drop? maybe can't..
           (equal (logtail (* 8 n) (wintlist byte-list))
                  (wintlist (nthcdr n byte-list))))
  :hints (("Goal" :induct (cdr-and-sub1-induct byte-list n)
           :expand (wintlist byte-list)
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable wintlist nthcdr))))

;; ;We probably don't usually want this reduction; rather we usually want to use
;; ;facts about ads1 and ads2 being disjoint or the same (or perhaps obeying a
;; ;subbagp relation).
;; (thm
;;  (equal (wr-list ads1 vals1 (wr-list ads2 vals2 ram))
;;         (wr-list (append ads1 ads2) (append vals1 vals2) ram))
;;  :hints (("Goal" ;:induct (wr-list ads1 vals1 ram)
;;           :in-theory (enable wr-list))))


;bzo
(defthm enlistw4-of-logext
  (equal (enlistw 4 (logext 32 x))
         (enlistw 4 x)))

(defthm loghead-times-8-of-wintlist
  (implies (integerp numbytes)
           (equal (loghead (* 8 numbytes) (wintlist byte-list))
                  (wintlist (firstn numbytes byte-list))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable wintlist firstn))))

(defthm wfixedlist-of-repeat
  (equal (wfixedlist (repeat size elem))
         (if (zp size)
             t
           (unsigned-byte-p 8 elem)))
  :hints (("Goal" :in-theory (enable wfixedlist repeat))))

(defthm wintlist-of-repeat-zero
  (equal (wintlist (repeat size 0))
         0)
  :hints (("Goal" :in-theory (enable wintlist repeat))))





(defthm wfixedlist-of-firstn
  (implies (wfixedlist x)
           (wfixedlist (firstn n x)))
  :hints (("Goal" :in-theory (enable wfixedlist firstn))))

;might loop with the rule use to prove it??
(defthm wintlist-of-firstn
  (implies (and ; (<= 0 n) ;drop?
            (integerp n))
           (equal (wintlist (firstn n x))
                  (loghead (* n 8) (wintlist x))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable WINTLIST FIRSTN))))

(defthm firstn-of-enlistw-case-1
  (implies (and (<= n m)
                (integerp m))
           (equal (firstn n (enlistw m val))
                  (enlistw n val))))

;drop if we change enlistw?
(defthm unsigned-byte-p-list-8-of-enlistw
  (unsigned-byte-p-list 8 (enlistw num val))
  :hints (("Goal" :in-theory (enable enlistw
                                     unsigned-byte-p-list))))

(defthmd wintlist-of-nthcdr ;bzo may loop with the rule used to prove it
  (implies (natp n)
           (equal (gacc::wintlist (nthcdr n lst))
                  (logtail (* 8 n) (gacc::wintlist lst))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::wintlist nthcdr))))

(defthm nthcdr-of-enlistw
  (implies (and (natp n)
                (natp size))
           (equal (nthcdr n (gacc::enlistw size val))
                  (gacc::enlistw (- size n) (logtail (* 8 n) val))))
  :hints (("Goal" :in-theory (enable wintlist-of-nthcdr))))

(defthm wintlist-of-append
  (equal (gacc::wintlist (append x y))
         (logapp (* 8 (len x)) (gacc::wintlist x) (gacc::wintlist y))))

(defthm append-of-enlistw-and-enlistw
  (implies (and (equal (* 8 n) m)
                (natp n)
                (natp mm)
                (natp m)
;                (<= n mm)
                )
           (equal (append (gacc::enlistw n val)
                          (gacc::enlistw mm (logtail m val)))
                  (gacc::enlistw (+ mm n) val))))

(defthm memberp-of-logapp-list
  (implies (and (integerp val)
                (natp n))
           (equal (memberp val (gacc::logapp-list n lst val2))
                  (and (memberp (acl2::loghead n val) (gacc::loghead-list n lst))
                       (equal (acl2::logtail n val)
                              (ifix val2)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct t
           :in-theory (enable gacc::logapp-list ACL2::EQUAL-LOGAPP-X-Y-Z))))

;bzo use quantify and make sure it gets this?
;improve the proof? prove it for arbitrary subbag?
(defthm unsigned-byte-p-list-of-remove-1
  (implies (gacc::unsigned-byte-p-list n x)
           (gacc::unsigned-byte-p-list n (bag::remove-1 a x)))
  :hints (("Goal" :in-theory (enable gacc::unsigned-byte-p-list bag::remove-1))))

(defthm unsigned-byte-p-list-implies-integer-listp
  (implies (gacc::unsigned-byte-p-list n lst) ;n is a free var
           (equal (integer-listp lst)
                  (true-listp lst))))

;bzo i don't like how integer-listp also tests for true-listp!
;use this one instead?
(DEFUN INTEGER-LISTP-better (ACL2::L)
  (DECLARE (XARGS :GUARD T))
  (COND ((ATOM ACL2::L)
         t)
        (T (AND (INTEGERP (CAR ACL2::L))
                (INTEGER-LISTP-better (CDR ACL2::L))))))

(DEFTHM GACC::IFIX-LIST-DOES-NOTHING-better
  (IMPLIES (INTEGER-LISTP-better GACC::VALS)
           (EQUAL (GACC::IFIX-LIST GACC::VALS)
                  GACC::VALS))
  :hints (("Goal" :in-theory (enable GACC::IFIX-LIST))))

(defthm unsigned-byte-p-list-implies-integer-listp-better
  (implies (gacc::unsigned-byte-p-list n lst) ;n is a free var
           (integer-listp-better lst))
  :hints (("Goal" :expand ((INTEGER-LISTP-BETTER LST)))))

;more generally wintlist of a usb8 list?
(defthm wintlist-of-loghead-list
  (equal (gacc::wintlist (gacc::loghead-list 8 lst))
         (gacc::wintlist lst)))

(defthm logapp-list-of-fix
  (equal (gacc::logapp-list 16 (list::fix x) j)
         (gacc::logapp-list 16 x j))
  :hints (("Goal" :in-theory (enable gacc::logapp-list))))

(defthm logapp-list-of-remove-1-perm
  (implies (and (bag::unique x) ;allows us to conclude equal instead of perm?
                (acl2::unsigned-byte-p 16 a)
                (gacc::unsigned-byte-p-list 16 x)
                )
           (equal (gacc::logapp-list 16 (bag::remove-1 a x) j)
                  (gacc::remove-1 (acl2::logapp 16 a j)
                                  (gacc::logapp-list 16 x j))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::logapp-list bag::remove-1))))

(local
 (defun 2-list-induct (l1 l2)
   (if (endp l1)
       (list l1 l2)
     (2-list-induct (cdr l1) (bag::remove-1 (car l1) l2)))))

;make  both an make the fw and back local
(defthm gacc::subbagp-of-two-logapp-list-calls-back
  (implies (and (bag::subbagp (gacc::logapp-list 16 vals1 j)
                              (gacc::logapp-list 16 vals2 j))
                (gacc::unsigned-byte-p-list 16 vals1)
                (gacc::unsigned-byte-p-list 16 vals2)
                (bag::unique vals2) ;okay?
                )
           (bag::subbagp vals1 vals2))
  :hints (("Goal" :induct (2-list-induct vals1 vals2)
           :expand (GACC::LOGAPP-LIST 16 VALS1 J)
           :do-not '(generalize eliminate-destructors))))

(defthm gacc::subbagp-of-two-logapp-list-calls-both
  (implies (and (gacc::unsigned-byte-p-list 16 vals1)
                (gacc::unsigned-byte-p-list 16 vals2)
                (bag::unique vals2) ;okay?
                (true-listp vals1)
                (true-listp vals2)
                )
           (equal (bag::subbagp (gacc::logapp-list 16 vals1 j)
                                (gacc::logapp-list 16 vals2 j))
                  (bag::subbagp vals1 vals2))))

(defthm find-index-of-logapp-list
  (implies (and (equal (acl2::logtail 16 val) val2) ;handle the other case?
                (integerp val)
                (acl2::integer-listp lst))
           (equal (list::find-index val (gacc::logapp-list 16 lst val2))
                  (list::find-index (acl2::loghead 16 val) (gacc::loghead-list 16 lst))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::logapp-list
                              (:definition list::find-index)
                              ))))

;If we decide to back out of the fast memories change, we can just make these always return t.
(defun ramp (ram)
  (declare (type t ram))
  (mem::memory-p ram))

;; (defun addressp (address ram)
;;   (declare (type t address)
;;            (xargs :guard (mem::memory-p ram))
;;            )
;;   (mem::address-p address ram))


;; ;bzo dup?
;; (defun unsigned-byte-p-list (size vals)
;;   (declare (type t size vals))
;;   (if (consp vals)
;;       (and (unsigned-byte-p size (car vals))
;;            (unsigned-byte-p-list size (cdr vals)))
;;     t))

(defun addressp (address ram)
  (declare (type t address)
           (xargs :guard (mem::memory-p ram)))
  (mem::address-p address ram))

;being agnostic about the size of the ram?
(defun address-listp
  (ad-list ram)
  (declare (type t ad-list)
           (xargs :guard (mem::memory-p ram)))
  (if (consp ad-list)
      (and (addressp (car ad-list) ram)
           (address-listp (cdr ad-list)
                          ram))
    t))

;not right: need to take log base 2 of the size... ugh...
;; (defun address-listp (ad-list ram)
;;   (declare (type t ad-list)
;;            (xargs :guard (mem::memory-p ram))
;;            )
;;   (unsigned-byte-p-list (mem::size ram) ad-list))


;; Operations for reading and writing lists of bytes.  Perhaps all fancier
;; reads and writes should be phrased in terms of rd-list and wr-list?  If so,
;; the interesting parts of those fancier operations would be how they
;; generate the lists of bytes and indices to be operated on by rd-list and
;; wr-list.

;;
;; RD-LIST
;;

;; Read the bytes from RAM that reside at the addresses in LIST.  Return a
;; list of the bytes in the same order as the addresses.  bzo disable this?
;;

(defund rd-list (list ram)
  (declare ;(type t list ram)
           (xargs :guard (and (ramp ram)
                              (address-listp list ram))
                  :guard-hints (("Goal"; :induct t
                                 :in-theory (enable RAMP MEM::ADDRESS-P)
                                 :do-not '(generalize eliminate-destructors))))
           )
  (if (consp list)
      (cons (rd (car list) ram)
            (rd-list (cdr list) ram))
    nil))

(defthm rd-list-append
  (equal (rd-list (append x y) ram)
         (append (rd-list x ram)
                 (rd-list y ram)))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm len-rd-list
  (equal (len (rd-list list ram))
         (len list))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm car-of-rd-list
  (equal (car (rd-list lst ram))
         (if (consp lst)
             (rd (car lst) ram)
           nil))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm consp-of-rd-list
  (equal (consp (rd-list lst ram))
         (consp lst))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm cdr-of-rd-list
  (equal (cdr (rd-list list ram))
         (if (endp list)
             nil
           (rd-list (cdr list) ram)))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm integer-listp-of-rd-list
  (integer-listp (rd-list list ram))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm rd-list-of-singleton
  (equal (rd-list (list ad) ram)
         (list (rd ad ram)))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm rd-list-of-cons
  (equal (rd-list (cons ad ads) ram)
         (cons (rd ad ram) (rd-list ads ram)))
  :hints (("Goal" :in-theory (enable rd-list))))


(defthm rd-list-when-ads-is-not-a-consp
  (implies (not (consp ads))
           (equal (rd-list ads ram)
                  nil))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm nthcdr-of-rd-list
  (equal (nthcdr n (rd-list ads ram))
         (rd-list (nthcdr n ads) ram))
  :hints (("Goal" :in-theory (enable nthcdr rd-list))))

(in-theory (enable (:induction nth))) ;bzo

(defthm nth-of-rd-list
  (equal (nth n (rd-list ads ram))
         (if (< (nfix n) (len ads))
             (rd (nth n ads) ram)
           nil)))

(defthm firstn-of-rd-list
  (equal (firstn n (rd-list ads ram))
         (rd-list (firstn n ads) ram))
  :hints (("Goal" :in-theory (enable rd-list (:induction firstn)))))

;;
;; WR-LIST
;;
;;
;; Write to RAM each value from VALS at the corresponding address from LIST.
;; Stop when you run out of addresses.
;;
;; Note that once VALS runs out we use nil as the value for each subsequent
;; write.  You may think we should write 0's instead, but wr treats nil as a 0
;; when writing it.
;;
;;I changed this to not stop when vals runs out.  A key property of wr-list is
;;that we should be able to tell what addresses get changes just by looking at
;;LIST -- not by looking at VALS.  (Consider the case in which we call wr with
;;some address ad and then call wr-list with a list of addresses that contains
;;ad.  We should be able to prove that the call to wr can be dropped, and we
;;don't want to consider the case when the call to wr-list ends early because
;;it runs out of values. I proved that the new and old behvior is identical in
;;the one place in the regression suite that wr-list is called by another
;;defun. -ews
;;
;bzo rename list param to ads?
;bzo disable

;bzo give a fast body?
(defund wr-list (list vals ram)
  (declare (xargs :guard (and (ramp ram)
                              (address-listp list ram))
                  :verify-guards nil ;we do it below
                  )
           ;; (type t list ram)
           (type (satisfies true-listp) vals)
           )
  (if (and (consp list)
;(consp vals)
           )
      (wr (car list) (car vals)
          (wr-list (cdr list) (cdr vals) ram))
    ram))

;bzo should these be about ramp?
(defthm memory-p-of-wr-list
  (implies (mem::memory-p m)
           (mem::memory-p (wr-list list vals m)))
  :hints (("Goal" :in-theory (enable wr-list))))

(defthm size-of-wr-list
  (implies (mem::memory-p mem)
           (equal (mem::size (wr-list list vals mem))
                  (mem::size mem)))
  :hints (("Goal" :in-theory (enable wr-list))))

(defthmd open-wr-list
  (implies
   (consp list)
   (equal (wr-list list vals ram)
          (wr (car list) (car vals)
              (wr-list (cdr list) (cdr vals) ram))))
  :hints (("goal" :in-theory (enable wr-list))))

(defthm wr-list-of-cons-one
  (equal (wr-list (cons ad ads) vals ram)
         (wr ad (car vals)  (wr-list ads (cdr vals) ram)))
  :hints (("Goal" :in-theory (enable wr-list))))

(defthm wr-list-of-cons-two
  (equal (wr-list ads (cons v vals) ram)
         (if (consp ads)
             (wr (car ads) v (wr-list (cdr ads) vals ram))
           ram))
  :hints (("Goal" :in-theory (enable wr-list))))

(defthm wr-list-of-cons-and-cons
  (equal (wr-list (cons ad list) (cons val vals) ram)
         (wr ad val (wr-list list vals ram))))

(defthm wr-list-when-ads-is-not-a-consp
  (implies (not (consp ads))
           (equal (wr-list ads vals ram)
                  ram))
  :hints (("Goal" :in-theory (enable wr-list))))



(defthm wr-list-over-wr
  (implies (not (memberp x list))
           (equal (wr-list list vals (wr x v ram))
                  (wr x v (wr-list list vals ram))))
  :hints (("Goal" :in-theory (enable list::memberp-of-cons wr-list))))

(defthm wr-list-append
  (implies (and (disjoint x y)
                (equal (len x)
                       (len a)))
           (equal (wr-list (append x y) (append a b) ram)
                  (wr-list y b (wr-list x a ram))))
  :hints (("goal" :induct (list::len-len-induction x a)
           :in-theory (enable disjoint binary-append))))



(defthm rd-list-of-wr-irrel
  (implies (not (list::memberp ad ads))
           (equal (rd-list ads (wr ad v ram))
                  (rd-list ads ram)))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm wfixlist-rd-list
  (equal (wfixlist (rd-list list ram))
         (rd-list list ram))
  :hints (("Goal" :in-theory (enable wfixlist rd-list))))

;; (thm
;;  (equal (wr-list ads v1 (wr-list ads v2 ram))
;;         (wr-list ads v1 ram))
;;  :hints (("Goal" :in-theory (enable wr==r!))))

;bzo move
(defthm wr-list-of-wr-same
  (implies (memberp x list)
           (equal (wr-list list vals (wr x v ram))
                  (wr-list list vals ram)))
  :hints (("Goal" :in-theory (enable wr-list))))

;bzo move
(defthm wr-list-of-wr-list-subbagp
  (implies (bag::subbagp ads2 ads1)
           (equal (wr-list ads1 vals1 (wr-list ads2 vals2 ram))
                  (wr-list ads1 vals1 ram)))
  :Hints (("Goal" :induct (wr-list ads2 vals2 ram)
           :in-theory (enable wr-list)
           )))

(defthm wr-list-of-what-was-already-there
  (implies (equal vals (rd-list ads ram))
           (equal (wr-list ads vals ram)
                  ram))
  :hints (("Goal" :in-theory (enable wr-list))))

(defthm wr-list-of-what-was-already-there-cheap
  (equal (wr-list ads (rd-list ads ram) ram)
         ram))

(defthm wfixedlist-of-rd-list
  (wfixedlist (rd-list ads ram))
  :hints (("Goal" :in-theory (enable wfixedlist rd-list)))
  )


(defthm wr-list-of-wr-list-diff
  (implies (bag::disjoint list1 list2)
           (equal (wr-list list1 vals1 (wr-list list2 vals2 ram))
                  (wr-list list2 vals2 (wr-list list1 vals1 ram))))
  :hints (("Goal" :in-theory (enable wr-list))))

(defthm rd-of-wr-list-diff
  (implies (not (memberp ad ads))
           (equal (rd ad (wr-list ads val ram))
                  (rd ad ram)))
  :hints (("Goal" :in-theory (enable wr-list))))

(defthm rd-list-of-wr-list-diff
  (implies (bag::disjoint ads1 ads2)
           (equal (rd-list ads1 (wr-list ads2 vals ram))
                  (rd-list ads1 ram)))
  :hints (("Goal" :in-theory (enable wr-list))))


;; (defun clr-list (ads ram)
;;   (if (endp ads)
;;       ram
;;     (clr-list (cdr ads) (clr (car ads) ram))))

(defun clr-list (ads ram)
  (if (consp ads)
      (clr-list (cdr ads) (memory-clr (car ads) ram))
    ram))

(defthmd open-clr-list
  (implies
   (consp ads)
   (equal (clr-list ads ram)
          (clr-list (cdr ads) (memory-clr (car ads) ram)))))

(defthmd clr-list-over-memory-clr
  (equal (clr-list list (memory-clr x r))
         (memory-clr x (clr-list list r)))
  :hints (("Subgoal *1/1" :cases ((equal x (car list))))))

#+joe
(defund clr-list (ads ram)
  (wr-list ads nil ram))

(defthm clr-list-when-ads-is-not-a-consp
  (implies (not (consp ads))
           (equal (clr-list ads ram)
                  ram))
  :hints (("Goal" :in-theory (enable clr-list))))




(defthm clr-list-of-wr-list-same
  (equal (clr-list ads (wr-list ads vals ram1))
         (clr-list ads ram1))
  :hints (("Goal" :in-theory (enable clr-list-over-memory-clr wr-list open-wr-list open-clr-list))))

(defthm clr-list-of-cons
  (equal (clr-list (cons ad ads) ram)
         (memory-clr ad (clr-list ads ram)))
  :hints (("Goal" :in-theory (enable clr-list-over-memory-clr  clr-list))))

(defthm clr-list-of-wr-cover
  (implies (list::memberp ad ads)
           (equal (clr-list ads (wr ad val ram))
                  (clr-list ads ram)))
  :hints (("Goal" :in-theory (enable clr-list))))

(local (defun my-induct (ads vals ram)
         (if (endp ads)
             (list ads vals ram)
           (my-induct (cdr ads) (cdr vals) (wr (car ads) (car vals) ram)))))

;; The unique hyp is necessary (unless we are willing to make the RHS more
;; complicated).  Consider: (rd-list '(0 0 0) (wr-list '(0 0 0) '(1 2 3) nil))
;; = (1 1 1)
;;
(defthm rd-list-of-wr-list-same
  (implies (bag::unique ads)
           (equal (rd-list ads (wr-list ads vals ram))
                  (my-wfixlist (len ads) vals)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable rd-list wr-list my-wfixlist)
           :induct (my-induct ads vals ram))))


;version for rd-list?
(defthm rd-subst-when-wr-list-equal
  (implies (and (equal (wr-list ads v ram1)
                       (wr-list ads v ram2))
                (syntaxp (acl2::smaller-term ram2 ram1))
                (not (memberp ad ads)))
           (equal (rd ad ram1)
                  (rd ad ram2)))
  :hints (("Goal" :use ((:instance rd-of-wr-list-diff (val v) (ram ram1))
                        (:instance rd-of-wr-list-diff (val v) (ram ram2))))))

(defthm wr-list-subst-wr-list
  (implies (and (equal (wr-list ads1 v1 ram1)
                       (wr-list ads1 v1 ram2))
                (syntaxp (acl2::smaller-term ram1 ram2))
                (subbagp ads1 ads2))
           (equal (wr-list ads2 v2 ram2)
                  (wr-list ads2 v2 ram1)))
  :hints (("Goal" :use ((:instance wr-list-of-wr-list-subbagp (ads1 ads2) (ads2 ads1) (vals1 v2) (vals2 v1) (ram ram2))
                        (:instance wr-list-of-wr-list-subbagp (ads1 ads2) (ads2 ads1) (vals1 v2) (vals2 v1) (ram ram1)))
           :do-not '(generalize eliminate-destructors)
           :in-theory (disable wr-list-of-wr-list-subbagp))))

;It's a bit odd to replace vals with NIL, since NIL has a shorter length, but
;we do it anyway...
;
(defthm wr-list-equal-rewrite-vals-to-nil
  (implies (syntaxp (not (equal vals ''nil)))
           (equal (equal (wr-list ads vals ram2) (wr-list ads vals ram1))
                  (equal (wr-list ads nil ram2) (wr-list ads nil ram1)))))


;gen the len of ads?
(defthm wr-list-of-my-wfixlist
  (equal (wr-list ads (my-wfixlist (len ads) vals) ram)
         (wr-list ads vals ram))
  :hints (("Goal" :in-theory (enable wr-list my-wfixlist))))

(defthm wr-list-subst-vals
  (implies (and (equal (my-wfixlist (len ads) vals1)
                       (my-wfixlist (len ads) vals2))
                (syntaxp (acl2::smaller-term vals2 vals1)))
           (equal (wr-list ads vals1 ram)
                  (wr-list ads vals2 ram)))
  :hints (("Goal" :use ((:instance wr-list-of-my-wfixlist (vals vals1))
                        (:instance wr-list-of-my-wfixlist (vals vals2)))
           :in-theory (disable wr-list-of-my-wfixlist) )))


;; The (unique ads) hyp is necessary.  If ads contains duplicates but the
;; corresponding values in vals don't agree, then (my-wfixlist (len ads) vals)
;; will contain an incorrect value....
;bzo explain this better
;;

(defthmd wr-list-nil-to-clr-list
  (equal (wr-list ads nil ram)
         (clr-list ads ram))
  :hints (("goal" :in-theory (e/d (wr-list memory-clr)
                                  (wr==r!)))))

(defthm wr-list-equal-rewrite
  (implies (unique ads)
           (equal (equal (wr-list ads vals ram1) ram2)
                  (and (equal (my-wfixlist (len ads) vals)
                              (rd-list ads ram2))
                       (equal (clr-list ads ram1)
                              (clr-list ads ram2)))))
  :hints (("Goal" :use (:instance wr-list-of-what-was-already-there-cheap (ram ram2))
           :in-theory (e/d (wr-list-nil-to-clr-list clr-list)
                           (wr-list-of-what-was-already-there
                            wr-list-of-what-was-already-there-cheap)))))

(defthm rd-of-wr-list-memberp-case
  (implies (list::memberp ad ads)
           (equal (gacc::rd ad (gacc::wr-list ads vals ram))
                  (acl2::loghead 8 (nth (list::find-index ad ads) vals))))
  :hints (("Goal" :in-theory (e/d (LIST::MEMBERP-WHEN-NOT-MEMBERP-OF-CDR gacc::wr-list list::FIND-INDEX)
                                  (bag::FIND-INDEX-OF-CDR)))))

;bzo theory invar?
(defthmd gacc::clr-list-rewrite
  (equal (gacc::clr-list x ram)
         (gacc::wr-list x (repeat (len x) 0) ram))
  :hints (("Goal" :in-theory (enable gacc::wr-list gacc::clr-list))))


(defthm clr-list-of-append
  (equal (gacc::clr-list (append x y) ram)
         (gacc::clr-list x (gacc::clr-list y ram)))
  :hints (("Goal" :in-theory (enable gacc::clr-list-rewrite))))

(defthm unsigned-byte-p-list-8-of-rd-list
  (gacc::unsigned-byte-p-list 8 (gacc::rd-list lst ram))
  :hints (("Goal" :in-theory (enable gacc::rd-list))))

(in-theory (enable (blk)))

(defun atype (m)
  (if (zp m) nil
    `(
      (a 0 0 8 0 nil)
      (b 0 1 8 0 ,(atype (1- m)))
      (c 0 2 8 0 nil)
      (g 0 6 8 0 ,(atype (1- m)))
      (d 0 3 8 0 nil)
;      (e 0 4 8 0 nil)
;      (f 0 5 8 0 nil)
;      (h 0 7 8 0 ,(atype (1- m)))
;      (i 0 8 8 0 ,(atype (1- m)))
;      (j 0 9 8 0 ,(atype (1- m)))
      )))

(defthm unique-blks-atype
  (unique (blks (atype n))))

(defthm uniform-base-atype
  (uniform-base (atype m)))

(defthm weak-skel-atype
  (and (weak-skel (atype m))
       (wf-skel (atype m))))

(defthm open-atype
  (and
   (implies
    (and
     (syntaxp (syntax-atom m))
     (not (zp m)))
    (equal (atype m)
           `(
             (a 0 0 8 0 nil)
             (b 0 1 8 0 ,(atype (1- m)))
             (c 0 2 8 0 nil)
             (g 0 6 8 0 ,(atype (1- m)))
             (d 0 3 8 0 nil)
;             (e 0 4 8 0 nil)
;             (f 0 5 8 0 nil)
;             (h 0 7 8 0 ,(atype (1- m)))
;             (i 0 8 8 0 ,(atype (1- m)))
;             (j 0 9 8 0 ,(atype (1- m)))
             )))
   (implies
    (and
     (syntaxp (syntax-atom m))
     (zp m))
    (equal (atype m) nil))))

(in-theory (disable atype))

(defun a-mark (n ptr ram)
  (if (zp n) ram
    (if (zerop ptr) ram
      (let ((vc (rx 8 (+ 2 ptr) ram)))
        (let ((vc (wfixn 8 1 (1+ vc))))
          (let ((ram (wx 8 (+ 2 ptr) vc ram)))
            (let ((pb (rx 8 (+ 1 ptr) ram)))
              (a-mark (1- n) pb ram))))))))

(defthm open-a-mark
  (and
   (implies
    (and
     (syntaxp (syntax-atom n))
     (not (zp n)))
    (equal (a-mark n ptr ram)
           (if (zerop ptr) ram
             (let ((vc (rx 8 (+ 2 ptr) ram)))
               (let ((vc (wfixn 8 1 (1+ vc))))
                 (let ((ram (wx 8 (+ 2 ptr) vc ram)))
                   (let ((pb (rx 8 (+ 1 ptr) ram)))
                     (a-mark (1- n) pb ram))))))))
   (implies
    (and
     (syntaxp (syntax-atom n))
     (zp n)
     )
    (equal (a-mark n ptr ram) ram)))
  :hints (("goal" :expand (a-mark n ptr ram))))

(in-theory (disable a-mark))
(in-theory (enable (:induction a-mark)))

(defthm a-mark-over-wx
  (let ((askel (g* mptr (atype n) ram)))
    (let ((flat (flatten askel)))
      (implies
       (and
        (disjoint (blk wptr (1+ (max-offset size))) flat)
        (unique flat)
        (integerp n)
        (integerp mptr)
        (integerp wptr)
        )
       (equal (a-mark n mptr (wx size wptr value ram))
              (wx size wptr value (a-mark n mptr ram))))))
  :hints (("goal" :induct (a-mark n mptr ram))))

(defthm rx-over-a-mark
  (let ((askel (g* mptr (atype n) ram)))
    (let ((flat (flatten askel)))
      (implies
       (and
        (disjoint (blk rptr (1+ (max-offset size))) flat)
        (unique flat)
        (integerp n)
        (integerp mptr)
        (integerp rptr)
        )
       (equal (rx size rptr (a-mark n mptr ram))
              (rx size rptr ram)))))
  :hints (("goal" :induct (a-mark n mptr ram))))

(defthm g*-over-a-mark
  (let ((mskel (g* mptr (atype n) ram))
        (askel (g* rptr rskel ram)))
    (let ((mflat (flatten mskel))
          (rflat (flatten askel)))
      (implies
       (and
        (syntaxp (not (syntax-consp-or-quote rskel)))
        (disjoint mflat rflat)
        (unique mflat)
        (wf-skel rskel)
        (integerp n)
        (integerp mptr)
        (integerp rptr))
       (equal (g* rptr rskel (a-mark n mptr ram))
              (g* rptr rskel ram)))))
  :hints (("goal" :induct (a-mark n mptr ram))))

(defthm s*-over-a-mark
  (let ((mskel (g* mptr (atype n) ram))
        (askel wskel))
    (let ((mflat (flatten mskel))
          (rflat (flatten askel)))
      (implies
       (and
        (disjoint mflat rflat)
        (unique mflat)
        (wf-skel wskel)
        (integerp n)
        (integerp mptr))
       (equal (a-mark n mptr (s* wskel ram))
              (s* wskel (a-mark n mptr ram))))))
  :hints (("goal" :induct (s* wskel ram))))

(defthm x*-over-a-mark
  (let ((mskel (g* mptr (atype n) ram))
        (askel rskel))
    (let ((mflat (flatten mskel))
          (rflat (flatten askel)))
      (implies
       (and
        (syntaxp (not (syntax-consp-or-quote rskel)))
        (disjoint mflat rflat)
        (unique mflat)
        (wf-skel rskel)
        (integerp n)
        (integerp mptr))
       (equal (x* rskel (a-mark n mptr ram))
              (x* rskel ram)))))
  :hints (("goal" :induct (a-mark n mptr ram))))

(defun a-mark-closed (n ptr ram)
  (a-mark n ptr ram))

#|

(defun updater-exists (expr args fns)
  (declare (type t expr args fns))
  (if (and (consp expr)
           (consp args))
      (or (and (equal (car args) 'ram)
               (consp (car expr))
               (memberp (caar expr) fns))
          (updater-exists (cdr expr) (cdr args) fns))
    nil))


(mutual-recursion

 (defun rx-denormal-list (term spec)
   (declare (type (satisfies eqlable-alistp) spec))
   (if (consp term)
       (or (rx-denormal (car term) spec)
           (rx-denormal-list (cdr term) spec))
     nil))

 (defun rx-denormal (term spec)
   (declare (type (satisfies eqlable-alistp) spec))
   (if (consp term)
       (let ((hit (assoc (car term) spec)))
         (if (and (consp hit)
                  (consp (cdr hit)))
             (let ((args (cadr hit))
                   (fns  (cddr hit)))
               (or (updater-exists term args fns)
                   (rx-denormal-list (cdr term) spec)))
           (rx-denormal-list (cdr term) spec)))
     nil))

 )

(defun spec ()
  `(
    (rx (size ptr ram) . (wx))
    ))


|#


(defthm a-mark-definition
  (let ((askel (g* ptr (atype n) ram)))
    (implies
     (and
      (unique (flatten askel))
      (integerp n)
      (integerp ptr)
      )
     (equal (a-mark n ptr ram)
            (s* (x* askel (a-mark-closed n ptr ram)) ram))))
  :hints (("goal" :induct (a-mark n ptr ram))
          ("Subgoal *1/3" :in-theory (cons 'open-atype (theory 'simplify-uniqueness)))
          ("Subgoal *1/3.2" :in-theory (current-theory :here))
          ("Subgoal *1/3.1" :in-theory (current-theory :here))))

(in-theory (disable a-mark-definition))

(defthm a-mark-use
  (let ((askel (g* ptr (atype n) ram)))
    (let ((ramx (s* askel st2)))
      (implies
       (and
        (unique (flatten askel))
        (integerp n)
        (integerp ptr)
        )
       (equal (x* askel (a-mark-closed n ptr ramx))
              (x* askel (a-mark-closed n ptr ram))
              ))))
  :hints (("goal" :induct (a-mark n ptr ram))
          ("Subgoal *1/3" :in-theory (cons 'open-atype (theory 'simplify-uniqueness)))
          ("Subgoal *1/3.4'" :in-theory (current-theory :here))
          ("Subgoal *1/3.3'" :in-theory (current-theory :here))
          ("Subgoal *1/3.2'" :in-theory (current-theory :here))
          ("Subgoal *1/3.1'" :in-theory (current-theory :here))
          ))

(in-theory (disable a-mark-use))
(in-theory (disable a-mark-closed))

(defthm a-mark-definition-use
  (let ((askel (g* ptr (atype n) ram)))
    (let ((ramx (s* askel st2)))
      (implies
       (and
        (free st2)
        (unique (flatten askel))
        (integerp n)
        (integerp ptr)
        )
       (equal (a-mark n ptr ram)
              (s* (x* askel (a-mark-closed n ptr ramx)) ram)))))
  :hints (("goal" :in-theory (enable a-mark-definition a-mark-use))))


#|

(defun btype (m)
  (if (zp m) nil
    `(
      (a 0 0 8 0 nil)
      (b 0 1 8 0 ,(btype (1- m)))
      (c 0 2 8 0 nil)
      (d 0 3 8 0 ,(btype (1- m)))
      )))

(defthm unique-blks-btype
  (unique (blks (btype n))))

(defthm uniform-base-btype
  (uniform-base (btype m)))

(defthm weak-skel-btype
  (and (weak-skel (btype m))
       (wf-skel (btype m))))

(defthm open-btype
  (implies
   (and
    (integerp m)
    (< 0 m))
   (equal (btype m)
          `(
            (a 0 0 8 0 nil)
            (b 0 1 8 0 ,(btype (1- m)))
            (c 0 2 8 0 nil)
            (d 0 3 8 0 ,(btype (1- m)))
            ))))


(defun b-mark (n ptr ram)
  (if (zp n) ram
    (if (zerop ptr) ram
      (let ((vc (rx 8 (+ ptr 2) ram)))
        (let ((vc (wfixn 8 1 (1+ vc))))
          (let ((ram (wx 8 (+ ptr 2) vc ram)))
            (let ((pb (rx 8 (+ ptr 1) ram)))
              (let ((ram (b-mark (1- n) pb ram)))
      (let ((va (rx 8 ptr ram)))
        (let ((va (wfixn 8 1 (1+ va))))
          (let ((ram (wx 8 ptr va ram)))
            (let ((pd (rx 8 (+ ptr 3) ram)))
              (b-mark (1- n) pd ram)))))))))))))

(defthm open-b-mark
  (and
   (implies
    (and
     (not (zp n))
     (not (zerop ptr)))
    (equal (b-mark n ptr ram)
           (let ((vc (rx 8 (+ ptr 2) ram)))
        (let ((vc (wfixn 8 1 (1+ vc))))
          (let ((ram (wx 8 (+ ptr 2) vc ram)))
            (let ((pb (rx 8 (+ ptr 1) ram)))
              (let ((ram (b-mark (1- n) pb ram)))
        (let ((va (rx 8 ptr ram)))
          (let ((va (wfixn 8 1 (1+ va))))
            (let ((ram (wx 8 ptr va ram)))
              (let ((pd (rx 8 (+ ptr 3) ram)))
                (b-mark (1- n) pd ram))))))))))))
   (implies
    (zp n)
    (equal (b-mark n ptr ram) ram))
   (implies
    (zerop ptr)
    (equal (b-mark n ptr ram) ram))))

;;
;; Here is where it starts ..
;;

#+joe
(defun-sk forall-rptr (mptr n size ram)
  (forall rptr
          (let ((askel (g* mptr (atype n) ram)))
            (let ((flat (flatten askel)))
              (implies
               (and
                (disjoint (blk rptr (1+ (max-offset size))) flat)
                (unique flat)
                (integerp n)
                (integerp mptr)
                (integerp rptr)
                )
               (equal (rx size rptr (a-mark n mptr ram))
                      (rx size rptr ram)))))))

(defthm rx-over-amark-skolem
  (forall-rptr mptr n size ram))

#+joe
(defthm rx-over-a-mark
  (let ((askel (g* mptr (atype n) ram)))
    (let ((flat (flatten askel)))
      (implies
       (and
        (disjoint (blk rptr (1+ (max-offset size))) flat)
        (memberp rptr (blk mptr (g* mptr (atype n) ram)))
        (unique flat)
        (integerp n)
        (integerp mptr)
        (integerp rptr)
        )
       (equal (rx size rptr (a-mark n mptr ram))
              (rx size rptr ram)))))
  :hints (("goal" :induct (a-mark n mptr ram))))

#+joe
(defthm b-mark-over-wx
  (let ((mskel (g* mptr (btype n) ram)))
    (let ((mflat (flatten mskel)))
      (implies
       (and
        (disjoint (blk wptr (1+ (max-offset size))) mflat)
        (unique mflat)
        (integerp n)
        (integerp mptr)
        (integerp wptr)
        )
       (equal (b-mark n mptr (wx size wptr value ram))
              (wx size wptr value (b-mark n mptr ram))))))
  :hints (("goal" :induct (b-mark n mptr ram))))

#|

(defun swap-body (ptr ram)
  (let ((vc (rx 8 (+ ptr 2) ram)))
    (let ((vc (wfixn 8 1 (1+ vc))))
      (let ((ram (wx 8 (+ ptr 2) vc ram)))
        (let ((pb (rx 8 (+ ptr 1) ram))
              (pd (rx 8 (+ ptr 3) ram)))
          (let ((ram (wx 8 (+ ptr 1) pd ram)))
            (let ((ram (wx 8 (+ ptr 3) pb ram)))
              ram)))))))

(defun swap (n ptr ram)
  (if (zp n) ram
    (if (zerop ptr) ram
      (let ((ram (swap-body ptr ram)))
        (let ((pb (rx 8 (+ ptr 1) ram))
              (pd (rx 8 (+ ptr 3) ram)))
          (let ((ram (swap (1- n) pb ram)))
            (swap (1- n) pd ram)))))))

(defthm open-swap
  (and
   (implies
    (and
     (not (zp n))
     (not (zerop ptr)))
    (equal (swap n ptr ram)
           (let ((ram (swap-body ptr ram)))
             (let ((pb (rx 8 (+ ptr 1) ram))
                   (pd (rx 8 (+ ptr 3) ram)))
               (let ((ram (swap (1- n) pb ram)))
                 (swap (1- n) pd ram))))))
   (implies
    (zp n)
    (equal (swap n ptr ram) ram))
   (implies
    (zerop ptr)
    (equal (swap n ptr ram) ram)))
  :hints (("goal" :expand (swap n ptr ram))))



(defthm swap-over-wx
  (let ((mskel (g* mptr (btype n) ram)))
    (let ((mflat (flatten mskel)))
      (implies
       (and
        (disjoint (blk wptr (1+ (max-offset size))) mflat)
        (unique mflat)
        (integerp n)
        (integerp mptr)
        (integerp wptr)
        )
       (equal (swap n mptr (wx size wptr value ram))
              (wx size wptr value (swap n mptr ram))))))
  :hints (("goal" :induct (swap n mptr ram))))

(defthm rx-over-swap
  (let ((mskel (g* mptr (btype n) ram)))
    (let ((mflat (flatten mskel)))
      (implies
       (and
        (disjoint (blk rptr (1+ (max-offset size))) mflat)
        (unique mflat)
        (integerp n)
        (integerp mptr)
        (integerp rptr)
        )
       (equal (rx size rptr (swap n mptr ram))
              (rx size rptr ram)))))
  :hints (("goal" :induct (swap n mptr ram))))

(defthm g*-over-swap
  (let ((mskel (g* mptr (btype n) ram))
        (askel (g* rptr rskel ram)))
    (let ((mflat (flatten mskel))
          (rflat (flatten askel)))
      (implies
       (and
        (disjoint mflat rflat)
        (unique mflat)
        (wf-skel rskel)
        (integerp n)
        (integerp mptr)
        (integerp rptr))
       (equal (g* rptr rskel (swap n mptr ram))
              (g* rptr rskel ram)))))
  :hints (("goal" :induct (swap n mptr ram))))
|#

;; c-mark



(defun c-type (m)
  (if (zp m) nil
    `(
      (a 0 0 8 0 nil)
      (b 0 1 8 0 ,(c-type (1- m)))
      (c 0 2 8 0 ,(c-type (1- m)))
      )))

(defthm unique-blks-c-type
  (unique (blks (c-type n))))

(defthm uniform-base-c-type
  (uniform-base (c-type m)))

(defthm weak-skel-c-type
  (and (weak-skel (c-type m))
       (wf-skel (c-type m))))

(defthm open-c-type
  (implies
   (and
    (integerp m)
    (< 0 m))
   (equal (c-type m)
          `(
            (a 0 0 8 0 nil)
            (b 0 1 8 0 ,(c-type (1- m)))
            (c 0 2 8 0 ,(c-type (1- m)))
            ))))

(defun c-mark (n ptr ram)
  (if (zp n) ram
    (if (zerop ptr) ram
      (let ((ram (wx 8 ptr 0 ram)))
        (let ((pb (rx 8 (+ ptr 1) ram)))
          (let ((ram (c-mark (1- n) pb ram)))
            (let ((pc (rx 8 (+ ptr 2) ram)))
              (let ((ram (c-mark (1- n) pc ram)))
                ram))))))))


(defthm open-c-mark
  (and
   (implies
    (and
     (not (zp n))
     (not (zerop ptr)))
    (equal (c-mark n ptr ram)
           (let ((ram (wx 8 ptr 0 ram)))
             (let ((pb (rx 8 (+ ptr 1) ram)))
               (let ((ram (c-mark (1- n) pb ram)))
                 (let ((pc (rx 8 (+ ptr 2) ram)))
                   (let ((ram (c-mark (1- n) pc ram)))
                     ram)))))))
   (implies
    (zp n)
    (equal (c-mark n ptr ram) ram))
   (implies
    (zerop ptr)
    (equal (c-mark n ptr ram) ram)))
  :hints (("goal" :expand (c-mark n ptr ram))))



(defun c-mark-body (skel ptr ram)
  (if (consp skel) (c-mark 1 ptr ram)
    ram))

(defthm c-mark-body-props
  (and
   (implies
    (not (consp skel))
    (equal (c-mark-body skel ptr ram) ram))
   (implies
    (consp skel)
    (equal (c-mark-body skel ptr ram) (c-mark 1 ptr ram)))))

(in-theory (disable c-mark-body))

(defun c-mark-rec (n ptr skel ram)
  (if (zp n) ram
    (if (zerop ptr) ram
      (if (consp skel)
          (let ((entry (car skel)))
            (let ((indx (caddr entry))       ; index
                  (type (cadddddr entry)))   ; type
              (let ((v (rx 8 (+ ptr indx) ram)))
                (let ((ram (c-mark-body type v ram)))
                  (let ((ram (c-mark-rec (1- n) v type ram)))
                    (c-mark-rec n ptr (cdr skel) ram))))))
        ram))))

(defthm open-c-mark-rec
  (and
   (implies
    (and
     (not (zp n))
     (not (zerop ptr)))
    (equal (c-mark-rec n ptr skel ram)
           (if (consp skel)
               (let ((entry (car skel)))
                 (let ((indx (caddr entry))       ; index
                       (type (cadddddr entry)))   ; type
                   (let ((v (rx 8 (+ ptr indx) ram)))
                     (let ((ram (c-mark-body type v ram)))
                       (let ((ram (c-mark-rec (1- n) v type ram)))
                         (c-mark-rec n ptr (cdr skel) ram))))))
             ram)))
   (implies
    (zp n)
    (equal (c-mark-rec n ptr skel ram) ram))
   (implies
    (zerop ptr)
    (equal (c-mark-rec n ptr skel ram) ram))))


(defthm c-mark-proof
  (implies
   (integerp ptr)
   (equal (c-mark-rec n ptr (c-type n) ram)
          ))
  :hints (("goal" :induct (c-mark n ptr ram))))

|#

(local (in-theory (disable ACL2::LOGCAR-0-REWRITE)))

;;This is a nonsense function that we can associate with the name loghead8, so
;;that the defrecord doesn't give an error when it tries to mention loghead8 in
;;theory expressions.
;;
(defun loghead8-rune (v)
  (declare (type t v))
  v)

(add-macro-alias loghead8 loghead8-rune)

;; usbp8-rd is generated by the defrecord, but we'll use unsigned-byte-p-of-rd
;; instead.
;;
(in-theory (disable usbp8-rd))

(defthm usbp8-of-rd-forward-chaining
  (acl2::unsigned-byte-p 8 (rd a ram))
  :rule-classes ((:forward-chaining :trigger-terms ((rd a ram))))
  :hints (("Goal" :in-theory (enable usbp8-rd))))

(defthm unsigned-byte-p-of-rd
  (implies (<= 8 n)
           (equal (acl2::unsigned-byte-p n (rd a ram))
                  (integerp n))))

;; See also RD-SAME-WR-HYPS and RD-DIFF-WR-HYPS.  We could leave
;; RD-OF-WR-REDUX disabled if it turns out to be expensive.
;;
(in-theory (enable rd-of-wr-redux))

;; Adding this in case we want to disable RD-SAME-WR-HYPS (in which case, we
;; should enable this rule).
;;
(defthmd rd-same-wr-hyps-cheap
  (equal (rd acl2::a (wr acl2::a acl2::v acl2::r))
         (loghead8 acl2::v)))

;bzo Should the defrecord automatically give us any of the theorems in this book?


;; See also WR-SAME-WR-HYPS and WR-DIFF-WR-HYPS.  We could disable
;; wr-of-wr-both if it turns out to be expensive (but knowing whether nested
;; writes affect the same key or different keys seems like a fundamental piece
;; of knowledge, so maybe this rules is okay or even good).
;;
(defthm wr-of-wr-both
  (equal (wr b y (wr a x r))
         (if (equal a b)
             (wr b y r)
           (wr a x (wr b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a wr)))))

;; Adding this in case we want to disable WR-SAME-WR-HYPS (in which case, we
;; should enable this rule).
;;
(defthmd wr-same-wr-hyps-cheap
  (equal (wr acl2::a acl2::y (wr acl2::a acl2::x acl2::r))
         (wr acl2::a acl2::y acl2::r)))

(defthm rd-integerp-rewrite
  (integerp (rd addr ram))
  :hints (("Goal" :in-theory (enable rd))))

(defthm rd-integerp-type-prescription
  (integerp (rd addr ram))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable rd))))

(defthm rd-non-negative
  (<= 0 (rd addr ram))
  :hints (("Goal" :expand (WF-usbp8 (G ADDR RAM))
           :in-theory (enable rd wf-usbp8))))

(defthm rd-non-negative-type-prescription
  (<= 0 (rd addr ram))
  :rule-classes :type-prescription
  :hints (("Goal" :expand (WF-usbp8 (G ADDR RAM))
           :in-theory (enable rd wf-usbp8))))

(defthm rd-non-negative-linear
  (<= 0 (rd addr ram))
  :rule-classes :linear
  :hints (("Goal" :expand (WF-usbp8 (G ADDR RAM))
           :in-theory (enable rd wf-usbp8))))


;; This rule will never fire.
;; (equal (wr ) (wr )) is reduced.
;; v2 and v2 are free variables.
(defthmd wr-equal-differential-one
  (implies (and (equal (wr a v1 ram1)
                       (wr a v2 ram2))
                (not (equal ram1 ram2)))
           (equal (equal (rd a ram1) (rd a ram2))
                  nil)))

(defthm clr-equal-differential-one
  (implies (and (equal (memory-clr a ram1)
                       (memory-clr a ram2))
                (not (equal ram1 ram2)))
           (equal (equal (rd a ram1) (rd a ram2))
                  nil))
  :hints (("goal" :in-theory '(memory-clr wr-equal-differential-one))))

;; This rule will never fire.
;; (equal (wr ) (wr )) is reduced.
; a is a free variable
(defthmd wr-equal-differential-two
  (implies (and (equal (wr a v1 ram1)
                       (wr a v2 ram2))
                (not (equal ram1 ram2)))
           (equal (equal (acl2::loghead 8 v1) (acl2::loghead 8 v2))
                  t)))

;bzo improve?
(defthm loghead-of-rd
  (equal (acl2::loghead 8 ;wfixn 8 1
                        (rd a ram))
         (rd a ram))
  :hints (("goal" :in-theory (enable ;open-wfixw ;wfixn
                                     ))))

;loop stopper?
(defthm wr-of-wr-same-value
  (equal (wr x val (wr y val ram))
         (wr y val (wr x val ram)))
  :hints (("Goal" :cases ((equal x y)))))

(defthm wr-equality
  (implies (equal (wr off val1 ram1) ;val1 is a free variable
                  (wr off val1 ram2))
           (equal (equal (wr off val2 ram1) (wr off val2 ram2))
                t))
  :hints (("Goal" :in-theory (enable wr==r!))))

(defthm rd-subst-when-wr-equal
  (implies (and (equal (wr b val ram1) (wr b val ram2))
                (syntaxp (acl2::smaller-term ram2 ram1))
                (not (equal a b)))
           (equal (rd a ram1)
                  (rd a ram2)))
  :hints (("Goal" :in-theory (disable RD-OF-WR-REDUX WR==R!)
           :use ((:instance RD-OF-WR-REDUX (acl2::a a) (acl2::b b) (acl2::v val) (acl2::r ram1))
                 (:instance RD-OF-WR-REDUX (acl2::a a) (acl2::b b) (acl2::v val) (acl2::r ram2))
                 ))))

(defthm rd-subst-when-clr-equal
  (implies (and (equal (memory-clr b ram1) (memory-clr b ram2))
                (syntaxp (acl2::smaller-term ram2 ram1))
                (not (equal a b)))
           (equal (rd a ram1)
                  (rd a ram2)))
  :hints (("Goal" :in-theory '(memory-clr rd-subst-when-wr-equal))))


;bzo gen to non-consp?
(defthm rd-of-nil
  (equal (gacc::rd a nil)
         0)
  :hints (("Goal" :in-theory (enable gacc::rd))))

;bzo add
(defthm memory-clr-of-nil
  (equal (gacc::memory-clr a nil)
         nil)
  :hints (("Goal" :in-theory (enable gacc::memory-clr))))

(local (in-theory (disable ACL2::LOGCAR-0-REWRITE)))

;;This is a nonsense function that we can associate with the name loghead8, so
;;that the defrecord doesn't give an error when it tries to mention loghead8 in
;;theory expressions.
;;
(defun loghead8-rune (v)
  (declare (type t v))
  v)

;; usbp8-rd is generated by the defrecord, but we'll use unsigned-byte-p-of-rd
;; instead.
;;
(in-theory (disable usbp8-rd))

(defthm usbp8-of-rd-forward-chaining
  (acl2::unsigned-byte-p 8 (rd a ram))
  :rule-classes ((:forward-chaining :trigger-terms ((rd a ram))))
  :hints (("Goal" :in-theory (enable usbp8-rd))))

(defthm unsigned-byte-p-of-rd
  (implies (<= 8 n)
           (equal (acl2::unsigned-byte-p n (rd a ram))
                  (integerp n))))

;; See also RD-SAME-WR-HYPS and RD-DIFF-WR-HYPS.  We could leave
;; RD-OF-WR-REDUX disabled if it turns out to be expensive.
;;
(in-theory (enable rd-of-wr-redux))

;; Adding this in case we want to disable RD-SAME-WR-HYPS (in which case, we
;; should enable this rule).
;;
(defthmd rd-same-wr-hyps-cheap
  (equal (rd acl2::a (wr acl2::a acl2::v acl2::r))
         (loghead8 acl2::v)))

;bzo Should the defrecord automatically give us any of the theorems in this book?

;trying enabled...
;; See also WR-SAME-WR-HYPS and WR-DIFF-WR-HYPS.  We could disable
;; wr-of-wr-both if it turns out to be expensive (but knowing whether nested
;; writes affect the same key or different keys seems like a fundamental piece
;; of knowledge, so maybe this rules is okay or even good).
;;
(defthm wr-of-wr-both
  (equal (wr b y (wr a x r))
         (if (equal a b)
             (wr b y r)
           (wr a x (wr b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a wr)))))

;; Adding this in case we want to disable WR-SAME-WR-HYPS (in which case, we
;; should enable this rule).
;;
(defthmd wr-same-wr-hyps-cheap
  (equal (wr acl2::a acl2::y (wr acl2::a acl2::x acl2::r))
         (wr acl2::a acl2::y acl2::r)))

(defthm rd-integerp-rewrite
  (integerp (rd addr ram))
  :hints (("Goal" :in-theory (enable rd))))

(defthm rd-integerp-type-prescription
  (integerp (rd addr ram))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable rd))))

(defthm rd-non-negative
  (<= 0 (rd addr ram))
  :hints (("Goal" :expand (WF-usbp8 (G ADDR RAM))
           :in-theory (enable rd wf-usbp8))))

(defthm rd-non-negative-type-prescription
  (<= 0 (rd addr ram))
  :rule-classes :type-prescription
  :hints (("Goal" :expand (WF-usbp8 (G ADDR RAM))
           :in-theory (enable rd wf-usbp8))))

(defthm rd-non-negative-linear
  (<= 0 (rd addr ram))
  :rule-classes :linear
  :hints (("Goal" :expand (WF-usbp8 (G ADDR RAM))
           :in-theory (enable rd wf-usbp8))))


;; This rule will never fire.
;; (equal (wr ) (wr )) is reduced.
;; v2 and v2 are free variables.
(defthmd wr-equal-differential-one
  (implies (and (equal (wr a v1 ram1)
                       (wr a v2 ram2))
                (not (equal ram1 ram2)))
           (equal (equal (rd a ram1) (rd a ram2))
                  nil)))

(defthm clr-equal-differential-one
  (implies (and (equal (memory-clr a ram1)
                       (memory-clr a ram2))
                (not (equal ram1 ram2)))
           (equal (equal (rd a ram1) (rd a ram2))
                  nil))
  :hints (("goal" :in-theory '(memory-clr wr-equal-differential-one))))

;; This rule will never fire.
;; (equal (wr ) (wr )) is reduced.
; a is a free variable
(defthmd wr-equal-differential-two
  (implies (and (equal (wr a v1 ram1)
                       (wr a v2 ram2))
                (not (equal ram1 ram2)))
           (equal (equal (acl2::loghead 8 v1) (acl2::loghead 8 v2))
                  t)))

;bzo improve?
(defthm loghead-of-rd
  (equal (acl2::loghead 8 ;wfixn 8 1
                        (rd a ram))
         (rd a ram))
  :hints (("goal" :in-theory (enable ;open-wfixw ;wfixn
                                     ))))

(defthm wr-of-wr-same-value
  (equal (wr x val (wr y val ram))
         (wr y val (wr x val ram)))
  :hints (("Goal" :cases ((equal x y)))))

(defthm wr-equality
  (implies (equal (wr off val1 ram1) ;val1 is a free variable
                  (wr off val1 ram2))
           (equal (equal (wr off val2 ram1) (wr off val2 ram2))
                t))
  :hints (("Goal" :in-theory (enable wr==r!))))


(defthm rd-subst-when-wr-equal
  (implies (and (equal (wr b val ram1) (wr b val ram2))
                (syntaxp (acl2::smaller-term ram2 ram1))
                (not (equal a b)))
           (equal (rd a ram1)
                  (rd a ram2)))
  :hints (("Goal" :in-theory (disable RD-OF-WR-REDUX WR==R!)
           :use ((:instance RD-OF-WR-REDUX (acl2::a a) (acl2::b b) (acl2::v val) (acl2::r ram1))
                 (:instance RD-OF-WR-REDUX (acl2::a a) (acl2::b b) (acl2::v val) (acl2::r ram2))
                 ))))

(defthm rd-subst-when-clr-equal
  (implies (and (equal (memory-clr b ram1) (memory-clr b ram2))
                (syntaxp (acl2::smaller-term ram2 ram1))
                (not (equal a b)))
           (equal (rd a ram1)
                  (rd a ram2)))
  :hints (("Goal" :in-theory '(memory-clr rd-subst-when-wr-equal))))

;;
;;
;; FIX-SIZE
;;
;;

(defund fix-size (size)
  (declare (type t size))
  (let ((size (nfix size)))
    (if (<= size (word-size))
        (word-size)
      (+ (word-size) (fix-size (- size (word-size)))))))

(defthm fix-size-fix-size
  (equal (fix-size (fix-size size))
         (fix-size size))
  :hints (("Goal" :in-theory (enable fix-size))))

(defthm max-offset-fix-size
  (equal (max-offset (fix-size size))
         (max-offset size))
  :hints (("Goal" :in-theory (enable max-offset fix-size))))

(defthm fix-size-+8
  (implies (and (integerp v)
                (< 0 v))
           (equal (fix-size (+ 8 v))
                  (+ 8 (fix-size v))))
  :hints (("Goal" :in-theory (enable fix-size))))

;this seems odd -why have 2 lower bounds?  make a linear rule?
(defthm fix-size-magnitude
  (and (<= 8 (fix-size s))
       (< 0 (fix-size s)))
  :hints (("Goal" :in-theory (enable fix-size))))

(defthm negative-fix-size
  (implies (<= size 0)
           (equal (fix-size size)
                  8))
  :hints (("Goal" :in-theory (enable fix-size))))

(defthm fix-size-bound
  (implies (integerp sz)
           (<= sz (fix-size sz)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable fix-size))))

;bzo move and generalize!
(defthm integerp-of-one-eighth
  (implies (not (integerp size))
           (equal (integerp (* 1/8 size))
                  (not (acl2-numberp size))))
  :hints (("Goal" :use (:instance ACL2::INTEGERP-+-MINUS-* (acl2::i 8) (acl2::j (* 1/8 size))))))


;bzo
(defthm one-eighth-rule-2
  (implies (and (integerp (* 1/8 size))
                (acl2-numberp size))
           (integerp size))
  :rule-classes :forward-chaining
  :hints (("Goal" :use (:instance ACL2::INTEGERP-+-MINUS-* (acl2::i 8) (acl2::j (* 1/8 size))))))

;bzo
(defthm one-eighth-rule-3
  (implies (and (multiple-of-8 size)
                (acl2-numberp size))
           (integerp size))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable multiple-of-8))))

(defthm fix-size-when-size-is-not-an-integerp
  (implies (not (integerp size))
           (equal (fix-size size)
                  (word-size)))
  :hints (("goal" :in-theory (enable fix-size))))


;fix-size rounds its argument up to the next multiple of 8.
(defthmd fix-size-rewrite
  (equal (fix-size size)
         (if (zp size)
             8
           (* 8 (+ 1 (floor (+ -1 size) 8)))
           ))
  :hints (("Goal" :in-theory (e/d (max-offset ;floor
                                   FIX-SIZE
                                   )
                                  ( ;UNFIXED-SIZE-MAX-OFFSET ;looped
                                   ))
           :do-not '(generalize eliminate-destructors))))


;bzo
(defthm multiple-of-8-of-fix-size
  (multiple-of-8 (fix-size size))
  :hints (("Goal" :in-theory (enable multiple-of-8 fix-size))))

(defthm fix-size-when-multiple-of-8
  (implies (multiple-of-8 size)
           (equal (fix-size size)
                  (if (< 0 size)
                      size
                    8)))
  :hints (("Goal" :in-theory (enable multiple-of-8 fix-size-rewrite))))


(defun syntax-unfixed-size (size)
  (declare (type t size) (xargs :guard-hints (("Goal" :in-theory (enable quotep)))))
  (if (and (quotep size)
           (consp (cdr size)))
      (or (equal (nfix (cadr size)) 0)
          (not (equal (mod (nfix (cadr size)) (word-size)) 0)))
    (not (and (consp size) (equal (car size) 'fix-size)))))


(defthm maxoffset-recollapse-to-fix-size
  (equal (+ 8 (* 8 (max-offset size)))
         (fix-size size))
  :hints (("Goal" :in-theory (enable fix-size))))

;;
;;
;; sblk
;;
;;

;bzo order of args doesn't match blk
;return a list of word addresses which starts at PTR and which is long enough to represent SIZE bits
;always returns a cons, since if SIZE is 0, it still returns (0).
(defund sblk (size ptr)
  (declare (type t size ptr))
  (blk ptr (1+ (max-offset size)))
;;  (gacc::addr-range ptr (1+ (MAX-OFFSET SIZE))) ;;trying this equivalent definition...
  )

(defthm consp-sblk
  (and (sblk size ptr) ;do we need this?
       (consp (sblk size ptr)))
  :hints (("goal" :in-theory (enable sblk blk ifix)
           :expand (:free (base max) (blk-rec base 0 max))
           )))

(defthm sblk-type-prescription
  (and (consp (sblk size ptr))
       (true-listp (sblk size ptr)))
  :rule-classes ((:type-prescription)))

(defthm true-listp-sblk
  (true-listp (sblk size ptr))
  :hints (("goal" :in-theory (enable sblk))))

(defthm sblk-when-size-is-not-an-integerp
  (implies (and (syntaxp (not (equal size ''0))) ;drop?
;(syntaxp (not (quotep n)))
            (not (integerp size)))
           (equal (sblk size ptr)
                  (sblk 0 ptr)))
  :hints (("goal" :in-theory (enable sblk))))

(defthm sblk-when-size-is-not-positive
  (implies (and (syntaxp (not (equal size ''0))) ;drop?
; (syntaxp (not (quotep n)))
            (<= size 0) ;(not (equal n (nfix n)))
            )
           (equal (sblk size ptr)
                  (sblk 0 ptr)))
  :hints (("goal" :in-theory (enable sblk))))

(defthm car-sblk
  (equal (car (sblk size ptr))
         (ifix ptr))
  :hints (("goal" :in-theory (enable sblk blk ifix)
           :expand (:free (base max) (blk-rec base 0 max))
           )))

(defthm len-sblk
  (equal (len (sblk size ptr))
         (1+ (max-offset size)))
  :hints (("goal" :in-theory (enable ifix sblk blk))))

(defthm sblk-linear-disjointness
  (and (implies (<= (+ (ifix rptr) (1+ (max-offset rsize))) (ifix wptr))
                (disjoint (sblk rsize rptr) (sblk wsize wptr)))
       (implies (<= (+ (ifix wptr) (1+ (max-offset wsize))) (ifix rptr))
                (disjoint (sblk rsize rptr) (sblk wsize wptr))))
  :hints (("goal" :in-theory (enable sblk
                                     blk-disjoint-from-blk-1
                                     blk-disjoint-from-blk-2))))

(defthm unique-sblk
  (unique (sblk size ptr))
  :hints (("goal" :in-theory (enable sblk))))

(defthm integer-listp-sblk
  (integer-listp (sblk size ptr))
  :hints (("goal" :in-theory (enable sblk))))

(defthmd max-offset-to-fix-size-rev
  (equal (equal (fix-size s1) (fix-size s2))
         (equal (max-offset s1) (max-offset s2))))

(defthm equal-sblk-to-equal-args
  (equal (equal (sblk s1 o1) (sblk s2 o2))
         (and (equal (fix-size s1)
                     (fix-size s2))
              (equal (ifix o1)
                     (ifix o2))))
  :otf-flg t
  :hints (("goal" :cases ((iff (integerp o1) (integerp o2)))
           :in-theory (e/d (;ifix
                            max-offset-to-fix-size-rev
                              blk
                              sblk
                              fix-size
                              )
                           (;BLK-REC-NON-INTEGER-PTR
                             max-offset-to-fix-size
                            )))))

(defthm sblkp-of-singleton
  (equal (sblkp (cons a nil))
         (integerp a))
  :hints (("Goal" :in-theory (enable sblkp))))

(defthm sblkp-of-addr-range
  (gacc::sblkp (gacc::addr-range base k))
  :hints (("Goal" :in-theory (enable gacc::addr-range gacc::sblkp))))

(defthm sblkp-sblk
  (sblkp (sblk size off))
  :hints (("goal" :in-theory (enable sblk blk))))

(defthmd sblk-8-rewrite
  (equal (sblk 8 addr)
         (list (ifix addr)))
  :hints (("Goal" :in-theory (enable sblk blk
                                     open-blk-rec
                                     ))))

(defthm sblk-when-size-is-0
  (equal (GACC::SBLK 0 PTR)
         (list (ifix ptr)))
  :hints (("Goal" :in-theory (enable gacc::sblk))))

(defthm sblk-when-size-is-1
  (equal (GACC::SBLK 1 PTR)
         (list (ifix ptr)))
  :hints (("Goal" :in-theory (enable gacc::sblk))))

;bzo


;bzo gen!
(defthmd blk-rec-goes-to-addr-range
  (IMPLIES (AND (case-split (INTEGERP SIZE))
                (case-split (< 0 SIZE))
                (case-split (integerp base))
                )
           (EQUAL (GACC::BLK-REC base 0 SIZE)
                  (GACC::ADDR-RANGE base SIZE)))
  :hints (("Goal" ;:induct (GACC::ADDR-RANGE BASE SIZE)
           :in-theory (enable gacc::sblkp))))

(defthmd sblk-as-addr-range
  (implies (and (case-split (integerp size))
                (case-split (< 0 size))
                (case-split (gacc::multiple-of-8 size)))
           (equal (gacc::sblk size x)
                  (gacc::addr-range (ifix x) (/ size 8))))
  :hints (("Goal" :in-theory (enable blk-rec-goes-to-addr-range gacc::sblk gacc::blk))))

;only works when offse is 0?
(defthmd blk-rec-goes-to-addr-range2
  (equal (gacc::blk-rec base 0 size)
         (gacc::addr-range base size))
  :hints (("Goal" ;:induct (gacc::addr-range base size)
           :in-theory (enable  blk-rec-goes-to-addr-range))))

(defthmd sblk-becomes-addr-range
  (equal (gacc::sblk size x)
         (gacc::addr-range x (1+ (MAX-OFFSET SIZE))))
  :hints (("Goal" :expand ((MAX-OFFSET SIZE)
                           (FIX-SIZE SIZE))
           :in-theory (enable blk-rec-goes-to-addr-range2 sblk-as-addr-range gacc::sblk gacc::blk))))


;;
;; lemmas about rd, wr, rx-rec, and wx-rec
;;


(defthm rx-rec-wr-non-memberp
  (implies (not (memberp x (blk-rec ptr off size)))
           (equal (rx-rec ptr off size (wr x val ram))
                  (rx-rec ptr off size ram)))
  :hints (("goal" :expand ( (RX-REC PTR 0 SIZE (WR X VAL RAM))
                             (RX-REC PTR 0 SIZE RAM))
           :in-theory (enable rx-rec blk-rec))))

(defthm rx-rec-clr-non-memberp
  (implies (not (memberp x (blk-rec ptr off size)))
           (equal (rx-rec ptr off size (memory-clr x ram))
                  (rx-rec ptr off size ram)))
  :hints (("goal" :in-theory (enable memory-clr))))

(defthm rd-over-wx-rec
  (implies
   (and
    (not (memberp rptr (blk-rec wptr woff bwmax)))
    (<= (ifix wmax) (ifix bwmax))
    (<= 0 (ifix woff))
    (<= 0 (ifix wmax))
    )
   (equal (rd rptr (wx-rec wptr woff wmax value ram))
          (rd rptr ram)))
  :hints (("goal" :in-theory (enable wx-rec blk-rec)
           :induct (WX-REC WPTR WOFF WMAX VALUE RAM)
           :expand ((WX-REC WPTR WOFF WMAX VALUE RAM)))))

(defthm rd-over-wx-rec-instance
  (implies
   (and
    (not (memberp rptr (blk-rec wptr woff wmax)))
    (<= 0 (ifix woff))
    (<= 0 (ifix wmax))
    )
   (equal (rd rptr (wx-rec wptr woff wmax value ram))
          (rd rptr ram)))
  :hints (("Goal" :in-theory (enable wx-rec))))

(defthm rx-rec-over-wr
  (implies
   (and
    (not (memberp wptr (blk-rec rptr roff brmax)))
    (<= (ifix rmax) (ifix brmax))
    (<= 0 (ifix rmax))
    (<= 0 (ifix roff))
    )
   (equal (rx-rec rptr roff rmax (wr wptr value ram))
          (rx-rec rptr roff rmax ram)))
  :hints (("Goal" :in-theory (enable rx-rec blk-rec))))

(defthm rx-rec-over-wr-instance
  (implies
   (and
    (not (memberp wptr (blk-rec rptr roff rmax)))
    (<= 0 (ifix rmax))
    (<= 0 (ifix roff))
    )
   (equal (rx-rec rptr roff rmax (wr wptr value ram))
          (rx-rec rptr roff rmax ram))))

(defthm wr-over-wx-rec-instance
  (implies
   (and
    (not (memberp a (blk-rec wptr woff wmax)))
    (<= 0 woff)
    (<= 0 wmax)
    )
   (equal (wx-rec wptr woff wmax value (wr a v ram))
          (wr a v (wx-rec wptr woff wmax value ram)))))

(defthm wx-rec-of-wx-rec
  (implies
   (and
    (equal wptr ptr)
    (equal woff off)
    (equal wmax max)
    (<= 0 off)
    (<= off max)
    )
   (equal (wx-rec ptr off max value (wx-rec wptr woff wmax wvalue ram))
          (wx-rec ptr off max value ram)))
  :hints (("Goal" :in-theory (enable wx-rec))))


(defthm wx-rec-over-wx-rec-instance
  (implies
   (and
    (disjoint (blk-rec ptr   off max)
              (blk-rec wptr woff wmax))
    (<= 0 off)
    (<= 0 max)
    (<= 0 woff)
    (<= 0 wmax)
    )
   (equal (wx-rec ptr off max value (wx-rec wptr woff wmax wvalue ram))
          (wx-rec wptr woff wmax wvalue (wx-rec ptr off max value ram))))
  :rule-classes ((:rewrite :loop-stopper ((wptr ptr wx-rec)))))

;make this an equal rule?
(defthmd ram==wx-rec
  (implies (and (equal ram2 ram1)
                (equal (;wfixw 8 (- max (ifix off))
                        acl2::loghead (* 8 (nfix  (- max (ifix off))))
                        value)
                       (rx-rec ptr off max ram1))
                (<= 0 (ifix off))
                (<= (ifix off) (ifix max))
                )
           (equal (equal ram1 (wx-rec ptr off max value ram2))
                  t))
  :hints (("Goal" :in-theory (enable wx-rec rx-rec ;open-wfixw ;wcar wcons wcdr
                                     )
           :induct (wx-rec ptr off max value ram2))))

; trying with this disabled.
(defthmd rx-rec-to-rd-list-reduction
  (implies (and (integerp roff)
                (integerp rmax)
                (<= 0 roff)
                (<= roff rmax)
                )
           (equal (rx-rec base roff rmax ram)
                  (wintlist (rd-list (blk-rec base roff rmax) ram))))
  :hints (("goal" :in-theory (enable rx-rec
                                     blk-rec
                                     ))))

; trying with this disabled.
(defthmd wx-rec-to-wr-list-reduction
  (implies (and (integerp woff)
                (integerp wmax)
                (<= 0 woff)
                (<= woff wmax)
                )
           (equal (wx-rec base woff wmax value ram)
                  (wr-list (blk-rec base woff wmax)
                           (enlistw (- wmax woff) value) ram)))
  :hints (("goal" :induct (wx-rec base woff wmax value ram)
           :in-theory (e/d (wx-rec
                            blk-rec
                            open-blk-rec
                            wr-list
                                        ;open-wx-rec
                            )
                           (wr==r!
                            ENLISTW-OF-0;bzo
                            )))))



;;
;; Z*-rec
;;

#+joe
(defun z*-rec (list ram)
  ;(declare (type t list ram))
  (if (consp list)
      (let ((ram (memory-clr (car list) ram)))
        (z*-rec (cdr list) ram))
    ram))

(defthm z*-rec-over-append
  (equal (z*-rec (append x y) ram)
         (z*-rec x (z*-rec y ram)))
  :hints (("Goal" :in-theory (enable clr-list-over-memory-clr append))))

;odd way to phrase this?
(defthm z*-rec-commutativity
  (equal (equal (z*-rec x (z*-rec y ram)) (z*-rec y (z*-rec x ram)))
         t)
  :hints (("Goal" :in-theory (enable clr-list-over-memory-clr))))


(defthmd wr==ram
  (equal (equal (wr a (loghead8 v) ram1) ram2)
         (and (equal (loghead8 v) (rd a ram2))
              (equal (z*-rec `(,a) ram1)
                     (z*-rec `(,a) ram2))))
  :hints (("Goal" :in-theory (enable wr==r!))))


(defun z*-rec-induction (a list ram1 ram2 v)
  (if (consp list)
      (z*-rec-induction a (cdr list) (memory-clr (car list) ram1)
                        (memory-clr (car list) ram2) v)
    (equal (equal a ram1) (equal ram2 v))))

(defthm z*-rec-of-wr
  (implies (not (memberp a list))
           (equal (equal (z*-rec list (wr a (loghead8 v) ram1))
                         (z*-rec list ram2))
                  (and (equal (loghead8 v) (rd a ram2))
                       (equal (z*-rec (cons a list) ram1)
                              (z*-rec (cons a list) ram2)))))
  :hints (("goal" :in-theory (enable
                              wr==r!
                              memberp ;bzo
                              )
           :do-not '(generalize eliminate-destructors)
           :induct (z*-rec-induction a list ram1 ram2 v))))

(defthm z*-rec-over-wr
  (implies (memberp a list)
           (equal (equal (z*-rec list (wr a v ram1))
                         (z*-rec list ram2))
                  (equal (z*-rec list ram1)
                         (z*-rec list ram2))))
  :hints (("goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable
;memberp ;bzo
                       ))
          ("Subgoal *1/1" :cases ((equal (car list) a)))))



(defthm rx-rec-over-z*-rec-disjoint
  (implies (disjoint (blk-rec ptr off size) list)
           (equal (rx-rec ptr off size (z*-rec list ram))
                  (rx-rec ptr off size ram))))


;stringe rule...
(defthm equality-implies-equal-reads
  (implies (equal (z*-rec list (wx-rec ptr off size value ram1))
                  (z*-rec list ram2))
           (equal (rx-rec ptr off size (z*-rec list (wx-rec ptr off size value ram1)))
                  (rx-rec ptr off size (z*-rec list ram2)))))


;;
;; RX/WX Rules
;;


(defun ram==wx-hyp (size ptr value ram)
  (declare (type t size ptr value ram))
  (equal (acl2::loghead (fix-size size) ;wfixn 8 size
                (ifix value) ;drop the ifix once loghead's guards are weakened
                )
         (rx size ptr ram)))

;tests whether the nest of calls to wx which make up RAM includes a call to wx
;with arguments of SIZE and PTR?
;;
(defun wx-instance (size ptr ram)
  (declare (type t size ptr ram))
  (if (and (consp ram)
           (equal (car ram) 'wx) ; (wx size ptr value ram)
           (consp (cdr ram))
           (consp (cddr ram))
           (consp (cdddr ram))
           (consp (cddddr ram)))
      (if (and (equal ptr  (caddr ram))
               (equal size (cadr ram)))
          t
        (wx-instance size ptr (caddddr ram)))
    nil))

;not enabled outside of this book
(defthmd ram==wx
  (implies (and (syntaxp (not (wx-instance size ptr ram1)))
                (ram==wx-hyp size ptr value ram1)
                (equal ram2 ram1)
                )
           (equal (equal ram1 (wx size ptr value ram2))
                  t))
  :hints (("Goal" :in-theory (e/d (rx wx
                                      RAM==WX-REC
                                      ram==wx-rec)
                                  ( ;WFIXN-REWRITE-TO-LOGHEAD ;why
                                   MAX-OFFSET
                                   )))))

;drop the ifixes when loghead's guard improves? -ews
;why do we have a separate function for this?
(defun wx==wx-hyp (size value1 value2)
  (declare (type t size value1 value2))
  (equal (acl2::loghead (fix-size size) ;wfixn 8 size
                (ifix value1)
                )
         (acl2::loghead (fix-size size) ;wfixn 8 size
                (ifix value2)
                )))

;(in-theory (disable (wx==wx-hyp))) ; because of encapsulated functions

;not enabled outside of this book?
(defthmd wx==wx
  (implies (and (equal addr1 addr2)
                (equal size1 size2)
                (wx==wx-hyp size2 value1 value2)
                (equal ram1 ram2))
           (equal (equal (wx size1 addr1 value1 ram1)
                         (wx size2 addr2 value2 ram2))
                  t))
  :hints (("Goal" :cases ((integerp value1))
           :in-theory (enable wx wx-rec==wx-rec))))

;exported?
(defthm rx-of-wx
  (implies (and (equal wptr rptr)
                (equal wsize rsize)
                )
           (equal (rx rsize rptr (wx wsize wptr value ram))
                  (acl2::loghead (fix-size rsize) ;wfixn 8 rsize
                                 value)))
  :hints (("Goal" :in-theory (enable rx wx))))

;exported?
(defthm wx-of-wx
  (implies (and (equal wptr ptr)
                (equal wsize size)
                )
           (equal (wx size ptr value (wx wsize wptr wvalue ram))
                  (wx size ptr value ram)))
  :hints (("Goal" :in-theory (enable wx))))

;; wx-of-rx is probably pretty expensive .. if we need this fact, I
;; think we will get it from backchaining on state equality.
;exported?
(defthmd wx-of-rx
  (implies (equal (acl2::loghead (fix-size wsize) value) (rx wsize wptr ram))
           (equal (wx wsize wptr value ram)
                  ram))
  :hints (("Goal" :cases ((integerp value))
           :in-theory (enable wx rx ram==wx-rec))))


;move this stuff?


;bzo can loop!
(defthmd unfixed-size-rx-back
  (implies (syntaxp (syntax-unfixed-size rsize))
           (equal (rx (fix-size rsize) rptr ram)
                  (rx rsize rptr ram)))
  :hints (("goal" :in-theory (enable rx))))

(defthm acl2::unsigned-byte-p-of-rx-hack
  (acl2::unsigned-byte-p (fix-size size) (rx size a ram))
  :hints (("Goal" :in-theory (e/d ( unfixed-size-rx-back) (unsigned-byte-p-of-rx))
           :use (:instance unsigned-byte-p-of-rx (a a)
                           (ram ram)
                           (size  (fix-size size))
                           (size1 (fix-size size)))
           :do-not '(generalize eliminate-destructors))))

;exported?
(defthm unsigned-byte-p-of-rx-better
  (implies (<= (fix-size size2) size1)
           (equal (acl2::unsigned-byte-p size1 (rx size2 a ram))
                  (integerp size1)))
  :hints (("Goal" :in-theory (e/d (rx) ( ;MAX-OFFSET-WHEN-MULTIPLE-OF-8
;                                        RX-REC-TO-RD-LIST-REDUCTION
                                        )))))

;do we want this?  see loghead-identity
(defthm loghead-of-rx
  (implies (<= (fix-size size2) size1)
           (equal (acl2::loghead size1 (rx size2 ad ram))
                  (if (integerp size1)
                      (rx size2 ad ram)
                    0))))

;exported?
;Matches less often (because ram appears twice, but maybe this is enough for most cases?
(defthm wx-of-rx-cheap
  (equal (wx size ptr (rx size ptr ram) ram)
         ram)
  :hints (("Goal" :in-theory (enable wx-of-rx))))

;exported?
(defthm wx-over-wx
  (implies (disjoint (sblk size  ptr)
                     (sblk wsize wptr))
           (equal (wx size ptr value (wx wsize wptr wvalue ram))
                  (wx wsize wptr wvalue (wx size ptr value ram))))
  :rule-classes ((:rewrite :loop-stopper ((wptr ptr wx))))
  :hints (("goal" :in-theory (enable wx
                                     sblk blk
                                     ))))

;exported?
(defthm rx-over-wx
  (implies (disjoint (sblk rsize rptr)
                     (sblk wsize wptr))
           (equal (rx rsize rptr (wx wsize wptr value ram))
                  (rx rsize rptr ram)))
  :hints (("goal" :in-theory (enable sblk blk
                                     rx wx
                                     ))))

;;
;; lemmas about z*-rec together with wx/rx
;;

;where should this go?
(defthm z*-rec-wr
  (implies (not (memberp woff list))
           (equal (z*-rec list (wr woff value ram))
                  (wr woff value (z*-rec list ram)))))

;where should this go?
(defthm z*-rec-blk-rec-of-wr
  (implies (< woff (+ (ifix off) (ifix ptr)))
           (equal (z*-rec (blk-rec ptr off size) (wr woff value ram1))
                  (wr woff value (z*-rec (blk-rec ptr off size) ram1)))))
;move
;not actually a linear rule...
(defthm wr-wx-rec-linear-not-memberp
  (implies (< woff (+ (ifix off) (ifix ptr)))
           (equal (wx-rec ptr off size val1
                          (wr woff val2 ram))
                  (wr woff val2
                      (wx-rec ptr off size val1 ram))))
  :hints (("Goal" :in-theory (enable wx-rec)
           :induct (wx-rec ptr off size val1
                           (wr woff val2 ram)))))

;move?
(defthmd open-wx-rec
  (and (implies (> (ifix max) (ifix off))
                (equal (wx-rec base off max value ram)
                       (let ((off (ifix off))
                             (max (ifix max)))
                         (let ((ram (wx-rec (ifix base) (1+ off) max (acl2::logtail 8 (ifix value)) ram)))
                           (wr (+ off (ifix base))
                               (acl2::loghead 8 (ifix value))
                               ram)))))
       (implies (<= (ifix max) (ifix off))
                (equal (wx-rec base off max value ram) ram)))
  :hints (("goal" :in-theory '(wx-rec))))

;move?
(defthmd open-rx-rec
  (and (implies (> (ifix max) (ifix off))
                (equal (rx-rec base off max ram)
                       (let ((off (ifix off))
                             (max (ifix max)))
                         (let ((v (rd (+ off (ifix base)) ram)))
                           (acl2::logapp ;wcons
                            8 v
                                  (rx-rec (ifix base)
                                          (1+ off)
                                          max ram))))))
       (implies (<= (ifix max) (ifix off))
                (equal (rx-rec base off max ram) 0)))
  :hints (("goal" :in-theory '(rx-rec))))


(defun wx==ram-induction-8 (off ptr ram1 size value)
  (declare (xargs :measure (nfix (- (ifix size) (ifix off)))))
  (if (< (ifix off) (ifix size))
      (wx==ram-induction-8 (+ 1 (ifix off)) (ifix ptr)
                         (wr (+ (ifix off) (ifix ptr)) (acl2::loghead ;wcar
                                                        8 value) ram1)
                         (ifix size) (acl2::logtail ;wcdr
                                      8 value))
    (equal ptr (equal ram1 value))))

(defthm z*-rec-of-wx-rec
  (equal (z*-rec (blk-rec ptr off size) (wx-rec ptr off size value ram))
         (z*-rec (blk-rec ptr off size) ram))
  :hints (("goal" :in-theory (enable open-wx-rec wx-rec blk-rec)
           :induct (wx==ram-induction-8 off ptr ram size value))
          ))

(defthm wx==ram-rec-eighth
  (implies (equal (wx-rec ptr off size value ram1) ram2)
           (equal (z*-rec (blk-rec ptr off size) ram1)
                  (z*-rec (blk-rec ptr off size) ram2)))
  :hints (("Goal" :in-theory (enable blk-rec wx-rec open-wx-rec)
           :induct (wx==ram-induction-8 off ptr ram1 size value))
          )
  :rule-classes nil)

;do we need both rules?
(defthm wx==ram-rec-eighth-2
  (implies (equal ram2 (wx-rec ptr off size value ram1))
           (equal (z*-rec (blk-rec ptr off size) ram2)
                  (z*-rec (blk-rec ptr off size) ram1)))
  :hints (("Goal" :by  wx==ram-rec-eighth)))


(defthm wx==ram-rec-value-same
  (implies (and (equal (wx-rec ptr off size value ram1) ram2)
                (integerp off)
                (integerp size)
                (< off size))
           (equal (;wfixw 8 (- size off)
                   acl2::loghead (* 8 (nfix  (- size off)))
                   value)
                  (rx-rec ptr off size ram2)))
  :hints (("Goal" :in-theory (enable rx-rec wx-rec ;open-wfixw ;WCAR
                                     open-rx-rec
                                     )
           :expand  (WX-REC PTR OFF SIZE VALUE RAM1)
           :induct (wx==ram-induction-8 off ptr ram1 size value)))
  :rule-classes nil)

;do we need both rules?

(defthm wx==ram-rec-value-same-2
  (implies (and (equal ram2 (wx-rec ptr off size value ram1))
                (integerp off)
                (integerp size)
                (< off size))
           (equal (acl2::loghead (* 8 (nfix  (- size off))) value)
                  (rx-rec ptr off size ram2)))
  :hints (("Goal" :by wx==ram-rec-value-same)))

;bzo
(defthm wr-correct-val-equal
  (implies (and (< off size)
                (integerp off)
                (integerp size)
                (<= 0 off)
                (equal (acl2::loghead (* 8 (nfix (- size off))) val)
                       (rx-rec ptr off size ram2)))
           (equal (wx-rec ptr off size val ram2)
                  ram2))
  :hints (("Goal" :in-theory (e/d (wx-rec rx-rec)
                                  (open-wx-rec open-rx-rec)))))

(defthmd z*-same-wx-rec-0
  (equal (z*-rec (blk-rec ptr off size) ram)
         (wx-rec ptr off size 0 ram))
  :hints (("Goal" :in-theory (e/d (wx-rec blk-rec)
                                  (z*-rec-of-wx-rec)))))

(defthm other-way-2
  (implies (and (equal (z*-rec (blk-rec ptr off size) ram1)
                       (z*-rec (blk-rec ptr off size) ram2))
                (equal (;wfixw 8 (- size off)
                        acl2::loghead (* 8 (nfix  (- size off)))
                              value)
                       (rx-rec ptr off size ram2))
                (< off size)
                (integerp off)
                (integerp size)
                (<= 0 off))
           (equal ram2 (wx-rec ptr off size value ram1)))
  :hints (("Goal" :use (:instance other-way-1)))
  :rule-classes nil)

;bzo -use sblk in RHS?
;exported?
(defthmd wx==ram-rec
  (implies (and (<= 0 off)
                (< off size)
                (integerp off)
                (integerp size))
           (equal (equal (wx-rec ptr off size value ram1) ram2)
                  (and (equal (z*-rec (blk-rec ptr off size) ram1)
                              (z*-rec (blk-rec ptr off size) ram2))
                       (equal (acl2::loghead (* 8 (nfix (- size off))) value)
                              (rx-rec ptr off size ram2)))))
  :hints (("Goal" :in-theory (disable open-rx-rec)
           :use ((:instance other-way-1)
                 (:instance other-way-2)
                 (:instance wx==ram-rec-eighth)
                 (:instance wx==ram-rec-eighth-2)
                 (:instance wx==ram-rec-value-same)
                 (:instance wx==ram-rec-value-same-2)))))

(defthm z*-rec-memberp
  (implies (memberp x y)
           (equal (z*-rec y (wr x val ram))
                  (z*-rec y ram)))
  :hints (("Subgoal *1/2" :cases ((equal x (car y))))))

(defthm z*-rec-switcheroo
  (equal (z*-rec (blk-rec ptr off size)
                 (z*-rec list (wx-rec ptr off size value ram1)))
         (z*-rec list (z*-rec (blk-rec ptr off size) ram1)))
  :hints (("Goal" :in-theory (disable z*-rec-commutativity
                                      open-wx-rec open-blk-rec)
           :use (:instance z*-rec-commutativity
                           (x (blk-rec ptr off size))
                           (y list)
                           (ram (wx-rec ptr off size value ram1))))))

(defthm z*-rec-over-wx-rec
  (implies
   (disjoint (blk-rec ptr off size) list)
   (equal (z*-rec list (wx-rec ptr off size value ram))
          (wx-rec ptr off size value (z*-rec list ram))))
  :hints (("goal" :induct (wx-rec ptr off size value ram)
           :in-theory (enable wx-rec blk-rec))))



(defthmd z*-rec-disjoint
  (implies (and (disjoint list (blk-rec ptr off size))
                (<= 0 off)
                (< off size)
                (integerp off)
                (integerp size))
           (equal (acl2::loghead (* 8 (nfix (- size off))) value)
                  (rx-rec ptr off size
                          (z*-rec list (wx-rec ptr off size value ram)))))
  :hints (("goal" :in-theory (e/d (;wfixw
                                     blk-rec
                                     open-rx-rec
                                     open-wx-rec
                                     ) (;open-rx-rec
                                        ;Z*-REC
                                        ))
           :induct (wx==ram-induction-8 off ptr ram size value))))

;exported?
;bzo
(defthm wx-wfixn-reduction
  (equal (wx size ptr (acl2::loghead (fix-size size) value) ram)
         (wx size ptr value ram))
  :hints (("Goal" :cases ((integerp value))
           :in-theory (enable wx ;wfixn
                              wx-rec==wx-rec))))

;(local (in-theory (disable UNFIXED-SIZE-MAX-OFFSET)))

(defthm max-offset-when-multiple-of-8
  (implies (and (multiple-of-8 size)
                (< 0 SIZE)
                )
           (equal (max-offset size)
                  (+ -1 (/ size 8))))
  :hints (("Goal" :in-theory (enable MAX-OFFSET-REWRITES-TO-FLOOR
                                     multiple-of-8))))




(defthmd rx-to-rd-list-reduction
  (equal (rx size ptr ram)
         (wintlist (rd-list (sblk size ptr) ram)))
  :hints (("goal" :in-theory (enable RX-REC-TO-RD-LIST-REDUCTION
                                     rx
                                     blk
                                     sblk))))

(defthmd wx-to-wr-list-reduction
  (equal (wx size ptr value ram)
         (wr-list (sblk size ptr) (enlistw (1+ (max-offset size)) value) ram))
  :hints (("goal" :in-theory (enable WX-REC-TO-WR-LIST-REDUCTION
                                     wx blk sblk))))

;exported?
;; Do we want this enabled?
(defthmd wr-to-wx
  (implies (integerp a)
           (equal (wr a v ram)
                  (wx 8 a v ram)))
  :hints (("goal" :in-theory (e/d (;WFIXW WINTW ;wintn ;wfix
                                   OPEN-WX-REC wx wx-rec)
                                  (WX-REC-TO-WR-LIST-REDUCTION)))))



;bzo could redo the multiple of 8 stuff using divides from super-ihs

(defthmd rx-16-rewrite
  (equal (gacc::rx 16 addr ram)
         (logapp 8 ;bzo use logapp here?
                 (gacc::rd (ifix addr) ram)
                 (gacc::rd (+ 1 (ifix addr)) ram)))
  :hints (("Goal" :expand (gacc::rx 16 addr ram)
           :in-theory (enable gacc::open-blk-rec gacc::open-rx-rec))))

(defthmd rx-rd-equivalence
  (equal (gacc::rx 8 addr ram)
         (gacc::rd (ifix addr) ram))
  :hints (("Goal" :in-theory (enable gacc::rx gacc::wintlist
                                     gacc::rx-rec
                                     gacc::blk-rec gacc::rd-list))))


;should have a rule to rewrite subbagp of sblks?
;generalize?
(defthm sblk-16-subbagp-32
  (implies (integerp addr)
           (bag::subbagp (gacc::sblk 16 (+ 2 addr))
                         (gacc::sblk 32 addr)))
  :hints (("Goal" :in-theory (e/d (gacc::sblk gacc::blk
;                                     bag::subbagp
                                     bag::memberp)
                                  (BAG::SUBBAGP-CDR-REMOVE-1-REWRITE)))))


(defthm rx-8-wx-16-hack
  (equal (gacc::rx 8 ad (gacc::wx 16 ad value ram))
         (loghead 8 value))
  :hints (("Goal" :expand  (gacc::addr-range ad 2)
           :in-theory (enable gacc::rx gacc::wx gacc::open-wx-rec gacc::open-rx-rec))))


;gen...
(defthm loghead-8-of-rx
  (equal (loghead 8 (gacc::rx 16 a ram))
         (gacc::rx 8 a ram))
  :hints (("Goal" :in-theory (enable gacc::rx gacc::open-rx-rec))))

(defthm wx-of-rx-special-case
  (equal (gacc::wx size ad (gacc::rx size ad ram) ram)
         ram)
  :hints (("Goal" :in-theory (enable gacc::wx-of-rx))))

(defthm rw-wx-8-16-lemma
  (implies (and (integerp ad2) (integerp ad))
           (equal (GACC::RX 8 ad (GACC::WX 16 ad2 VALUE RAM))
                  (if (equal ad ad2)
                      (loghead 8 value)
                    (if (equal ad (+ 1 ad2))
                        (loghead 8 (logtail 8 value))
                      (GACC::RX 8 ad RAM)))))
  :hints (("Goal" :expand ((GACC::ADDR-RANGE AD2 2)
                           (GACC::ADDR-RANGE AD 2)
                           (GACC::ENLISTW 2 VALUE))
           :in-theory (enable gacc::wx gacc::rx  gacc::open-wx-rec gacc::open-rx-rec))))


;this one has a loop-stopper....
(defthm my-wx-over-wx
  (implies (bag::disjoint (gacc::sblk size  ptr)
                          (gacc::sblk wsize wptr))
           (equal (gacc::wx size ptr value (gacc::wx wsize wptr wvalue ram))
                  (gacc::wx wsize wptr wvalue (gacc::wx size ptr value ram))))
  :rule-classes ((:rewrite :loop-stopper ((ptr wptr gacc::wx)))))

(in-theory (disable gacc::wx-over-wx))

(defthm rx-when-ad-is-not-an-integerp
  (implies (not (integerp ad))
           (equal (gacc::rx numbits ad ram)
                  (gacc::rx numbits 0 ram)))
  :hints (("Goal" :in-theory (enable gacc::rx))))

(defthm wx-when-ad-is-not-an-integerp
  (implies (not (integerp ad))
           (equal (gacc::wx numbits ad val ram)
                  (gacc::wx numbits 0 val ram)))
  :hints (("Goal" :in-theory (enable gacc::wx))))

;;
;; (defthm my-wx-over-wx-both
;;   (equal (gacc::wx size ptr value (gacc::wx wsize wptr wvalue ram))
;;          (if (bag::disjoint (gacc::sblk size  ptr)
;;                             (gacc::sblk wsize wptr))
;;              (gacc::wx wsize wptr wvalue (gacc::wx size ptr value ram))
;;            (gacc::wx size ptr value ram)
;;            ))
;;   :rule-classes ((:rewrite :loop-stopper ((ptr wptr gacc::wx))))) ;bzo eric changed loop-stopper


;(local (in-theory (enable WFIXW-REDUCTION)))

;;
;; WFIXN
;;

;; ;b should be always be (word-size).
;; ;Chop v down to fit in as many chunks as it takes to represent an N-bit value.
;; ;what if N is 0?
;; (defund wfixn (b n v)
;;   (declare (type t b n v))
;;   (wfixw b (1+ (max-offset n)) v))

;; (defthm integerp-wfixn
;;   (integerp (wfixn b n value)))

;; (defthm wfixn-0
;;   (equal (wfixn b n 0)
;;          0)
;;   :hints (("Goal" :in-theory (enable wfixn))))

;; ;consider t-p rules!
;; (defthm wfixn-non-negative
;;   (<= 0 (wfixn b n v))
;;   :hints (("Goal" :in-theory (enable wfixn))))

;; (defthm wfixn-of-nfix
;;   (equal (wfixn b (nfix n) v)
;;          (wfixn b n v))
;;   :hints (("Goal" :in-theory (enable wfixn nfix))))

;; (defthm non-integer-size-wfixn
;;   (implies (and (syntaxp (not (quotep n)))
;;                 (not (equal n (nfix n))))
;;            (equal (wfixn b n v)
;;                   (wfixn b 0 v)))
;;   :hints (("goal" :in-theory (enable wfixn max-offset))))

;; (defthm wfixn-arith-reduction
;;   (implies (and (integerp a)
;;                 (integerp x))
;;            (equal (wfixn b n (+ a (wfixn b n x)))
;;                   (wfixn b n (+ a x))))
;;   :hints (("goal" :in-theory (enable wfixn wfixw-reduction))))

;; (defthm wfixn-ifix
;;   (equal (wfixn b n (ifix x))
;;          (wfixn b n x))
;;   :hints (("goal" :in-theory (enable wfixn wfixw-reduction))))

;; (defthmd zp-wfixn
;;   (implies (and (syntaxp (not (quotep n)))
;;                 (zp n))
;;            (equal (wfixn b n v)
;;                   (wfixn b 0 v)))
;;   :hints (("goal" :in-theory (enable wfixn))))

;; ;bbzo. Strange, why the second 8 in the lhs?
;; (defthmd wfixn-unsigned-byte-p
;;   (implies (and (integerp size)
;;                 (<= 8 size))
;;            (acl2::unsigned-byte-p size (wfixn 8 size 8)))
;;   :hints (("Goal" :in-theory (e/d (wfixn) ()))))

;; ;I think n in calls to wfixn will usually be a constant and will usually be either 8(?), 16, or 32.
;; ;similar rule fro wfixw?
;; (defthm wfixn-rewrite-to-loghead
;;   (equal (wfixn 8 n v)
;;          (acl2::loghead (fix-size n) v))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable fix-size-rewrite
;;                               acl2::imod ;bzo
;;                               max-offset-rewrites-to-floor
;;                               WFIXW-REDUCTION
;;                               WFIXN
;;                               acl2::LOGHEAD))))

;; ;bzo
;; (local (in-theory (disable wfixn-rewrite-to-loghead)))

;; ;bzo
;; (defthm wfixn-unsigned-byte-p-better
;;   (implies (<= (fix-size n) m)
;;            (equal (acl2::unsigned-byte-p m (wfixn 8 n x))
;;                   (integerp m)))
;;   :hints(("goal" :in-theory (e/d (wfixn-rewrite-to-loghead) ()))))


;bzo consider killing this
;; (defthm wfixn-unsigned-byte-p
;;   (implies
;;     (or
;;      (equal size 8)
;;      (equal size 16)
;;      (equal size 32))
;;    (unsigned-byte-p size (wfixn 8 size x)))
;;   :hints(("goal" :in-theory (e/d nil (wfixw)))))

;; jsut rewrite wfixn to wcar?
;; ;trying disabled
;; (defthmd wcar-reduction
;;   (equal (equal (wcar b v) (wfixn b 1 v))
;;          t)
;;   :hints (("goal" :in-theory (enable open-wfixw wfixn))))


;; ;can this loop?
;; (defthmd unfixed-size-wfixn
;;   (implies (syntaxp (syntax-unfixed-size s))
;;            (equal (wfixn b s v)
;;                   (wfixn b (fix-size s) v)))
;;   :hints (("goal" :in-theory (enable wfixn))))


;; ;this one shouldn't loop
;; (defthm unfixed-size-wfixn-constant-version
;;   (implies (syntaxp (and (quotep s)
;;                          (not (equal (fix-size (cadr s)) (cadr s)))))
;;            (equal (wfixn b s v)
;;                   (wfixn b (fix-size s) v)))
;;   :hints (("goal" :use unfixed-size-wfixn)))

;; (defthm signed-byte-p-of-wfixn
;;   (implies (< (fix-size n) m)
;;            (equal (acl2::signed-byte-p m (wfixn 8 n x))
;;                   (integerp m)))
;;   :hints (("Goal" :in-theory (enable wfixn-rewrite-to-loghead))))


;;
;; WINTN
;;

;; ;; b should equal (wordsize).
;; ;; Test whether V is an integer which can fit in as many words as it takes to represent an N-bit value.
;; (defund wintn (b n v)
;;   (declare (type t n))
;;   (wintw b (1+ (max-offset n)) v))

;; make a fw-chaining rule?
;; (defthmd wintn-integerp
;;   (implies (wintn a b x)
;;            (integerp x))
;;   :hints (("goal" :in-theory (enable wintn wintw))))

;; (defthm wintn-wfixn
;;   (implies (wintn s n x)
;;            (equal (wfixn s n x)
;;                   x))
;;   :hints (("Goal" :in-theory (enable wintn wfixn))))

;; ;replace the other one?
;; (defthm unsigned-byte-p-wintn-eric
;;   (implies (acl2::unsigned-byte-p size x)
;;            (equal (wintn 8 size x)
;;                   (if (integerp size)
;;                       t
;;                     (wintn 8 8 x)  ;simplify this?
;;                     )))
;;   :hints (("Goal" :in-theory (enable wintn
;;                                      wintw
;;                                      WFIXW-REDUCTION
;;                                      MAX-OFFSET-REWRITES-TO-FLOOR))))


;; (defthm unsigned-byte-p-wintn
;;   (implies (and (or (equal size 8)
;;                     (equal size 16)
;;                     (equal size 32))
;;                 (acl2::unsigned-byte-p size x))
;;            (wintn 8 size x))
;;   :hints (("Goal" :in-theory (enable wintn wintw WFIXW-REDUCTION))))

;; ;Eric turned this rule around, to rewrite to unsigned-byte-p when possible

;; (defthm unsigned-byte-p-wintn-equality
;;   (implies (or (equal size 8)
;;                (equal size 16)
;;                (equal size 32))
;;            (equal (wintn 8 size x)
;;                   (acl2::unsigned-byte-p size x)))
;;   :hints (("Goal" :in-theory (disable wintn))))

;; (defthm unsigned-byte-p-wfixn
;;   (implies (and (acl2::unsigned-byte-p n x)
;;                 (multiple-of-8 n))
;;            (equal (wfixn 8 n x)
;;                   x))
;;   :hints (("Goal" :use (:instance wintn-wfixn (s 8))
;;            :in-theory (disable wfixn
;;                                wintn-wfixn
;;                                wintn))))

;; (defthm wintn-0
;;   (wintn b s 0)
;;   :hints (("goal" :in-theory (enable wintn wintw))))

;; (defthm wintn-wfixn-2
;;   (wintn b s (wfixn b s v))
;;   :hints (("goal" :in-theory (enable wintn wfixn wintw))))

;; can be expensive?
;; (defthmd wintn-+
;;   (implies (wintn b w y)
;;            (<= 0 y))
;;   :hints (("goal" :in-theory (enable wintn wintw))))

;; (defthm wfixn-does-nothing-rewrite
;;   (equal (equal (wfixn b n v) v)
;;          (wintn b n v))
;;   :hints (("Goal" :in-theory (enable wintn wfixn wfixw wintw))))

;; (defthm wfixn-wfixn
;;    (equal (wfixn b n (wfixn b m v))
;;           (wfixn b (min (nfix n) (nfix m)) v))
;;    :hints (("Goal" :in-theory (enable wfixn))))

;; (defthm wfixn-when-n-is-zero
;;   (equal (wfixn b 0 v)
;;          (wfixn b 8 v)))

;; ;I've seen this loop.
;; (defthmd unfixed-size-wintn
;;   (implies (syntaxp (syntax-unfixed-size s))
;;            (equal (wintn b s v)
;;                   (wintn b (fix-size s) v)))
;;   :hints (("goal" :in-theory (enable wintn))))

;; ;this one shouldn't loop
;; (defthm unfixed-size-wintn-constant-version
;;   (implies (syntaxp (and (quotep s)
;;                          (not (equal (fix-size (cadr s)) (cadr s)))))
;;            (equal (wintn b s v)
;;                   (wintn b (fix-size s) v)))
;;   :hints (("goal" :use unfixed-size-wintn)))


;; ;not quite right
;; (defthm max-offset-reduce
;;   (implies (and (integerp x)
;;                 (<= 0 8))
;;            (equal (max-offset (+ -8 x))
;;                   (+ -1 (max-offset x))))
;;   :hints (("Goal" :in-theory (enable max-offset))))



;bbzo
;; (defthm wintn-8-rewrite
;;   (equal (wintn 8 n v)
;;          (acl2::unsigned-byte-p (+ 8 (* 8 (MAX-OFFSET N))) v))
;;   :hints (("Goal" :in-theory (e/d (wintn MAX-OFFSET-FIX-SIZE) ( ;UNFIXED-SIZE-MAX-OFFSET
;;                                                                       )))))


;; ;generalized above
;; (defthm wintn-unsigned-byte-p
;;   (implies (and (or (equal size 8)
;;                     (equal size 16)
;;                     (equal size 32))
;;                 (wintn 8 size x))
;;            (acl2::unsigned-byte-p size x))
;;   :hints(("goal" :in-theory (e/d (wintn
;;                                   wintw
;;                                   wfixw-unsigned-byte-p)
;;                                  (wfixw)))))



;; adapt?
;; (defthm wx-rec-wfixw
;;   (implies
;;    (and
;;     (integerp size)
;;     (integerp off)
;;     (< off size)
;;     (<= 0 off))
;;    (equal (wx-rec ptr off size (wfixw 8 (- size off) value) ram)
;;           (wx-rec ptr off size value ram)))
;;   :hints (("goal"
;;            :in-theory (enable ifix wx-rec))))



;; (DEFTHM RD-OVER-WX-REC-eric
;;   (IMPLIES (AND (NOT (MEMBERP RPTR (BLK-REC WPTR WOFF WMAX)))
;; ;                (<= (IFIX WMAX) (IFIX BWMAX))
;;                 (<= 0 (IFIX WOFF))
;;                 (<= 0 (IFIX WMAX)))
;;            (EQUAL (RD RPTR (WX-REC WPTR WOFF WMAX VALUE RAM))
;;                   (RD RPTR RAM))))




;;adapt?
;; (defthm wintw-rx-rec
;;   (implies
;;    (and
;;     (integerp off)
;;     (integerp max)
;;     (<= 0 off)
;;     (<= off max)
;;     (equal words (- max off)))
;;    (wintw 8 words (rx-rec ptr off max ram)))
;;   :hints (("Goal" :in-theory (enable rx-rec))))

;; ;;adapt?
;; (defthm wfixw-rx-rec
;;   (implies
;;    (and
;;     (integerp off)
;;     (integerp max)
;;     (<= 0 off)
;;     (<= off max)
;;     (equal words (- max off)))
;;    (equal (wfixw 8 words (rx-rec ptr off max ram))
;;           (rx-rec ptr off max ram))))


;; (defthm wintn-rx
;;   (wintn 8 size (rx size ptr ram))
;;   :hints (("Goal" :in-theory (enable wintn rx))))

;; (defthm wfixn-rx
;;   (implies (equal fsize size) ;this is odd...
;;            (equal (wfixn 8 fsize (rx size ptr ram))
;;                   (rx size ptr ram)))
;;   :hints (("Goal" :in-theory (enable rx wfixn))))

;drop
(local (in-theory (enable (force)))) ;unfortunate that i had to do this

;;
;;
;; Word size specification
;;
;;


(defun word-size () (declare (xargs :verify-guards t)) 8)

(defun max-offset (size)
  (declare (type t size))
  (if (<= (nfix size) (word-size))
      0
    (1+ (max-offset (- (nfix size) (word-size))))))

;;    (defthm max-offset-nfix
;;      (equal (max-offset (nfix size))
;;             (max-offset size)))

;;    (defthm min-max-offset
;;      (equal (max-offset (min (nfix n) (nfix m)))
;;             (min (max-offset n)
;;                  (max-offset m)))
;;      :hints (("goal" :induct (dual-induct n m))))

(defthm max-offset-of-non-integer
  (implies (not (integerp x))
           (equal (max-offset x)
                  0))
  :hints (("Goal" :in-theory (enable max-offset))))

(defthmd max-offset-rewrites-to-floor
  (equal (max-offset size)
         (if (and (integerp size)
                  (< 0 size))
             (floor (+ -1 size) 8)
           0))
  :hints (("Goal" :in-theory (e/d (max-offset)
                                  ( ;UNFIXED-SIZE-MAX-OFFSET ;looped
                                   ))
           :do-not '(generalize eliminate-destructors))))

;rewrite as (INTEGERP (* 1/8 SIZE))?? no...
;replace with eric's divides function?

(defund multiple-of-8 (n)
   (integerp (* 1/8 n))
   ;(equal n (* 8 (floor n 8)))
   )

(defthm multiple-of-8-fw-to-integerp-of-*-1/8
  (implies (multiple-of-8 x)
           (integerp (* 1/8 x)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable multiple-of-8))))

;(local (in-theory (disable UNFIXED-SIZE-MAX-OFFSET)))

(defthm max-offset-when-multiple-of-8
  (implies (and (multiple-of-8 size)
                (< 0 SIZE)
                )
           (equal (max-offset size)
                  (+ -1 (/ size 8))))
  :hints (("Goal" :in-theory (enable MAX-OFFSET-REWRITES-TO-FLOOR
                                     multiple-of-8))))


;;
;; RX/WX specifications
;;

;;
;; RX-REC
;;


;Read data from RAM.  Return the bytes stored at addresses BASE+OFF through
;BASE+MAX-1, all concatenated together, with data from the lower addresses in
;the lower-order positions of the result.

;Changed this to use logapp instead of wcons. -ews
(defund rx-rec (base off max ram)
  (declare (type t base off max ram)
           (xargs :measure (nfix (- (ifix max) (ifix off)))))
  (let ((off (ifix off))
        (max (ifix max)))
    (if (<= max off) 0
      (let ((v (rd (+ off (ifix base)) ram)))
        (acl2::logapp 8 v (rx-rec (ifix base) (1+ off) max ram))))))

(defthm integerp-rx-rec
  (integerp (rx-rec base off max ram))
  :rule-classes (:rewrite :type-prescription))

(defthm rx-rec-non-negative
  (<= 0 (rx-rec base off max ram))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable rx-rec))))

(defthm rx-rec-non-integer-ptr
  (implies (not (integerp x))
           (equal (rx-rec x off max ram)
                  (rx-rec 0 off max ram)))
  :hints (("Goal" :in-theory (enable rx-rec))))

(defthm rx-rec-when-max-is-less-than-off
  (implies (and (< max off)
                (integerp off)
                (integerp max))
           (equal (rx-rec base off max ram)
                  0))
  :hints (("Goal" :in-theory (enable rx-rec))))

(defthm loghead8-of-rx-rec
  (equal (acl2::loghead 8 (rx-rec base off max ram))
         (if (<= (ifix MAX) (ifix OFF))
             0
           (rd (+ (ifix base) (ifix off)) ram)))
  :hints (("Goal" :expand (rx-rec base off max ram))))

(defthm rx-rec-non-integer-off
  (implies (not (integerp off))
           (equal (rx-rec ptr off max ram)
                  (rx-rec ptr 0 max ram)))
  :hints (("Goal" :in-theory (e/d (rx-rec) (;ACL2::EQUAL-LOGAPP-X-Y-Z ;bzo
                                            )))))

;;
;; RX
;;

;Read SIZE bits of data from RAM, starting at address A.  (RAM is byte-addressable.)
;If SIZE is not a multiple of 8, it gets rounded up to a multiple of 8.  Thus, we read whole bytes.
;If SIZE is 0, it gets treated as if it were 8.
;Data from the lower addresses goes into the lower-order positions of the result.
(defund rx (size a ram)
  (declare (type t size a ram))
  (rx-rec a 0 (1+ (max-offset size)) ram))

(defthm integerp-rx
  (integerp (rx size a ram))
  :rule-classes (:rewrite :type-prescription))

;was called positive-rx
(defthm rx-non-negative-rewrite
  (<= 0 (rx size a ram)))

(defthm rx-non-negative-type-prescription
  (<= 0 (rx size a ram))
  :rule-classes :type-prescription)

(defthm rx-non-negative-linear
  (<= 0 (rx size a ram))
  :rule-classes :linear)

(defthm rx-when-size-is-not-an-integerp
  (implies (and (syntaxp (not (equal size ''0))) ;drop?
; (syntaxp (not (quotep n)))
            (not (integerp size)))
           (equal (rx size ptr ram)
                  (rx 0 ptr ram)))
  :hints (("goal" :in-theory (enable rx max-offset))))

(defthm rx-when-size-is-not-positive
  (implies (and (syntaxp (not (equal size ''0))) ;drop?
; (syntaxp (not (quotep n)))
            (<= size 0) ;(not (equal n (nfix n)))
            )
           (equal (rx size ptr ram)
                  (rx 0 ptr ram)))
  :hints (("goal" :in-theory (enable rx max-offset))))

(defthm unsigned-byte-p-of-rx
  (implies (and (<= size size1)
                (multiple-of-8 size) ;drop this?
                (< 0 size) ;drop?
                )
           (equal (acl2::unsigned-byte-p size1 (rx size a ram))
                  (integerp size1)))
  :hints (("Goal" :in-theory (e/d (rx) (;MAX-OFFSET-WHEN-MULTIPLE-OF-8
                                        )))))

;;
;; WX-REC
;;

;I changed this to call logtail and loghead instead of wcar and wcdr. -ews

;bzo - I believe the calls to ifix on value below could be dropped if the
;guards on the following functions were changed to not include (integerp i):
;ifloor, imod, loghead, and logtail.  The guards of those 4 functions (and
;perhaps others) seem needlessly strong.  Why require (integerp i) when it's
;not necessary?  But for now I'm refraining from making changes to functions
;from IHS, since doing so would require either changing files in the books/
;directory (a bad idea) or making out own copy of ihs and using it instead of
;the one in books/ (something we want to do eventually but not yet). -ews

(defund wx-rec (base off max value ram)
  (declare (type t base off max value ram)
           (xargs :measure (nfix (- (ifix max) (ifix off)))))
  (let ((off (ifix off))
        (max (ifix max)))
    (if (<= max off) ram
      (let ((ram (wx-rec (ifix base) (1+ off) max (acl2::logtail 8 (ifix value)) ram)))
        (wr (+ off (ifix base)) (acl2::loghead 8 (ifix value)) ram)))))


(defthm wx-rec-when-base-is-not-an-integerp
  (implies (not (integerp base))
           (equal (wx-rec base off max value ram)
                  (wx-rec 0    off max value ram)))
  :hints (("Goal" :in-theory (enable wx-rec))))

(defthm wx-rec-when-off-is-not-an-integerp
  (implies (not (integerp off))
           (equal (wx-rec base off max value ram)
                  (wx-rec base 0   max value ram)))
  :hints (("Goal" :in-theory (e/d (wx-rec) (wr==r!)))))

(defthm wx-rec-when-max-is-not-an-integerp
  (implies (not (integerp max))
           (equal (wx-rec base off max value ram)
                  (wx-rec base off 0   value ram)))
  :hints (("Goal" :in-theory (e/d (wx-rec) (wr==r!)))))

(defthm wx-rec-when-value-is-not-an-integerp
  (implies (not (integerp value))
           (equal (wx-rec base off max value ram)
                  (wx-rec base off max 0 ram)))
  :hints (("Goal"  :expand ( (wx-rec base off 0 value ram)
                             (wx-rec base 0 max value ram))
           :in-theory (e/d (wx-rec) (wr==r!)))))

(defthm wx-rec-when-max-<=-off
  (implies (<= (ifix max) (ifix off))
           (equal (wx-rec base off max value ram)
                  ram))
  :hints (("Goal" :in-theory (enable wx-rec))))

;;
;; WX
;;

(defund wx (size a v ram)
  (declare (type t size a v ram))
  (wx-rec a 0 (1+ (max-offset size)) v ram))

;bzo rename
(defthm wx-when-size-is-not-an-integerp
  (implies (and (syntaxp (not (equal size ''0))) ;drop?
                (not (integerp size))
                )
           (equal (wx size a v ram)
                  (wx 0 a v ram)))
  :hints (("goal" :in-theory (enable wx max-offset))))

(defthm wx-when-size-is-not-positive
  (implies (and (syntaxp (not (equal size ''0))) ;drop?
                (<= size 0)
                )
           (equal (wx size a v ram)
                  (wx 0 a v ram)))
  :hints (("goal" :in-theory (enable wx max-offset))))

(local (in-theory (enable zp)))

;bzo move
(defthm nthcdr-of-1
  (equal (nthcdr 1 x)
         (cdr x)))

;bbzo dup
(defun aamp-ramp (ram)
  (declare (type t ram))
  (and (ramp ram)
       (equal (mem::size ram) (expt 2 32))))


;; For execution only.
;; We could reorder things to put the most common cases first..
;; Would the logapp nests be faster if they were expressed instead in terms of + and ash?
;; Add in type declarations (since the common cases fit in 32 bits).
;rename
;make tail recursive!
;does this wrap?
(defun rd-bytes-exec (numbytes ad ram)
  (declare (type (integer 0 *) numbytes)
           (type integer ad) ;weaken
           (xargs :guard (and (aamp-ramp ram)
                              ;(address-listp (addr-range ad numbytes) ram)
                              )
                  :guard-hints (("Goal" :in-theory (enable ADDR-RANGE-EXPAND-WHEN-K-IS-A-CONSTANT)))
                  )
           )
  (if (zp numbytes)
      0
    (if (equal 1 numbytes)
        (rd (loghead 32 ad) ram)
      (if (equal 2 numbytes)
          (acl2::logapp 8
                        (rd (loghead 32 ad) ;bzo i added these logheads...
                            ram)
                        (rd (loghead 32 (+ 1 ad)) ram)
                        ) ;bzo
        (if (equal 4 numbytes)
            ;bzo reassociate the logapp?
            (acl2::logapp 24
                          (acl2::logapp 16
                                        (acl2::logapp 8
                                                      (rd (loghead 32 ad) ram)
                                                      (rd (loghead 32 (+ 1 ad)) ram))
                                        (rd (loghead 32 (+ 2 ad)) ram))
                          (rd (loghead 32 (+ 3 ad)) ram))
          (acl2::logapp 8 (rd (loghead 32 ad) ram) (rd-bytes-exec (+ -1 numbytes) (+ 1 ad) ram)))))))


;; Read NUMBYTES bytes of data from RAM, starting at address AD.  (RAM is
;; byte-addressable.)  Data from the lower addresses goes into the lower-order
;; positions of the result.
;;

(defund rd-bytes (numbytes ad ram)
  (declare (type integer ad)
           (type (integer 0 *) numbytes)
           (xargs  :guard (and (aamp-ramp ram)
                               ;(address-listp (addr-range ad numbytes) ram)
                               )
                   :guard-hints (("Goal" :in-theory (enable OFFSET-RANGE-WRAP-CONST-OPENER
                                                            ADDR-RANGE-EXPAND-WHEN-K-IS-A-CONSTANT))))
           )
  (mbe :exec (rd-bytes-exec numbytes ad ram)
       :logic (wintlist (rd-list ;;(addr-range ad numbytes)
                         (offset-range-wrap 32 ad numbytes) ;Bbzo eric made these changes - are they ok?
                         ram))))

(defthm rd-bytes-when-ad-is-not-an-integerp
  (implies (not (integerp ad))
           (equal (rd-bytes numbytes ad ram)
                  (rd-bytes numbytes 0 ram)))
  :hints (("Goal" :in-theory (enable rd-bytes))))

(defthm rd-bytes-of-1
  (equal (rd-bytes 1 ad ram)
         ;;(rd (ifix ad) ram)
         (rd (loghead 32 ad) ram)
         )
  :hints (("Goal" :in-theory (enable rd-bytes))))

(defthmd rd-bytes-constant-opener
  (implies (syntaxp (quotep numbytes))
           (equal (rd-bytes numbytes ad ram)
                  (wintlist
                   (rd-list (offset-range-wrap 32 ad numbytes) ;;(addr-range ad numbytes)
                            ram))))
  :hints (("Goal" :in-theory (enable rd-bytes))))

(defthm unsigned-byte-p-of-rd-bytes
  (implies (and (integerp numbytes)
                (<= 0 numbytes)
                )
           (unsigned-byte-p (* 8 numbytes) (rd-bytes numbytes ad ram)))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ( (rd-bytes numbytes ad ram))))
  :hints (("Goal" ; :cases ((integerp numbytes))
           :in-theory (enable rd-bytes))))

(defthm unsigned-byte-p-if-rd-bytes-gen
  (implies (and (<= (* 8 numbytes) n)
                (integerp n)
                (<= 0 n)
                (integerp numbytes)
                (<= 0 numbytes)
                )
           (unsigned-byte-p n (rd-bytes numbytes ad ram))))

;bzo gen the 8
(defthm loghead8-of-rd-bytes
  (implies (integerp ad) ;bzo
           (equal (loghead 8 (rd-bytes numbytes ad ram))
                  (if (and (integerp numbytes)
                           (< 0 numbytes))
                      (rd (loghead 32 ad)
                          ram)
                    0)))
  :hints (("Goal" :in-theory (enable rd-bytes))))

(defthm logtail8-of-rd-bytes
  (implies (integerp ad) ;bzo use ifix!
           (equal (LOGtail 8 (RD-BYTES numbytes ad ram))
                  (if (and (integerp numbytes)
                           (< 0 numbytes))
                       (RD-BYTES (+ -1 numbytes) (+ 1 ad) ram)
                    0)))
  :hints (("Goal" :in-theory (enable RD-BYTES))))


;; (defthm rd-bytes-when-numbytes-is-non-negative
;;   (implies (<= numbytes 0)
;;            (equal (rd-bytes numbytes ad ram)
;;                   nil))
;;   :hints (("Goal" :in-theory (enable rd-bytes))))

(defun unsigned-byte-p-list (size vals)
  (if (endp vals)
      t
    (and (unsigned-byte-p size (car vals))
         (unsigned-byte-p-list size (cdr vals)))))

(defthm address-listp-rewrite
  (implies (and (mem::memory-p ram)
                (equal (mem::size ram) 4294967296))
           (equal (address-listp ad-list ram)
                  (unsigned-byte-p-list 32 ad-list))))

(defthm unsigned-byte-p-list-of-offset-range-wrap
  (implies (natp n)
           (unsigned-byte-p-list n (offset-range-wrap n ad numbytes)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-list offset-range-wrap))))


;;
;; WR-BYTES
;;
;;bzo add mbe

(defund wr-bytes (numbytes ad v ram)
  (declare (type t ad ram)
           (type integer v)
           (type (integer 0 *) numbytes)
           (xargs  :guard (and (aamp-ramp ram)
                               (integerp ad) ;bzo did i really need this?
                               ;(address-listp (addr-range ad numbytes) ram)
                               )
                   :guard-hints (("Goal" :in-theory (enable OFFSET-RANGE-WRAP-CONST-OPENER
                                                            ADDR-RANGE-EXPAND-WHEN-K-IS-A-CONSTANT)))))
  (wr-list (offset-range-wrap 32 ad numbytes) ;(addr-range ad numbytes)
           (enlistw numbytes v) ram))

(defthm wr-bytes-when-ad-is-not-an-integerp
  (implies (not (integerp ad))
           (equal (wr-bytes numbytes ad v ram)
                  (wr-bytes numbytes 0 v ram)))
  :hints (("Goal" :in-theory (enable wr-bytes))))

(defthm wr-bytes-of-wr-bytes-same
  (equal (wr-bytes numbytes ad v1 (wr-bytes numbytes ad v2 ram))
         (wr-bytes numbytes ad v1 ram))
  :hints (("Goal" :in-theory (enable wr-bytes))))

;is this the best way to phrase the hyp?
(defthm wr-bytes-of-wr-bytes-diff
  (implies (bag::disjoint (offset-range-wrap 32 ad1 numbytes1) ;;(addr-range ad1 numbytes1)
                          (offset-range-wrap 32 ad2 numbytes2) ;;(addr-range ad2 numbytes2)
                          )
           (equal (wr-bytes numbytes1 ad1 v1 (wr-bytes numbytes2 ad2 v2 ram))
                  (wr-bytes numbytes2 ad2 v2 (wr-bytes numbytes1 ad1 v1 ram))))
  :hints (("Goal" :in-theory (e/d (wr-bytes) (DISJOINT-OF-TWO-ADDR-RANGES)))))


;;
;; lemmas about RD-BYTES and WR-BYTES together
;;

;;  ;; variations on this...
;;  (defthm rd-bytes-of-wr-bytes-same
;;    (implies (force (< numbytes (expt 2 32))) ;bzo added this for convenience when changing to fast-memories (could possibly be dropped...)
;;             (equal (rd-bytes numbytes ad (wr-bytes numbytes ad v ram))
;;                    (acl2::loghead (* 8 (ifix numbytes)) v)))
;;    :hints (("Goal" :use (:instance rd-bytes-of-wr-bytes-same-helper (ad (ifix ad)))
;;             :in-theory (disable rd-bytes-of-wr-bytes-same-helper)))))


(defthm rd-bytes-of-wr-bytes-same
  (implies (force (< numbytes (expt 2 32))) ;bzo added this when changing to fast-memories
           (equal (rd-bytes numbytes ad (wr-bytes numbytes ad v ram))
                  (acl2::loghead (* 8 (ifix numbytes)) v)))
  :hints (("Goal" :in-theory (enable RD-BYTES wr-bytes))))

;; ;bzo generalize  to subbagp?
;; (defthm wr-bytes-of-wr-bytes-same
;;   (implies (bag::subbagp (addr-range ad2 numbytes2) (addr-range ad1 numbytes1))
;;            (equal (wr-bytes numbytes1 ad1 v1 (wr-bytes numbytes2 ad2 v2 ram))
;;                   (wr-bytes numbytes1 ad1 v1 ram)))
;;   :hints (("Goal" :in-theory (enable wr-bytes))))

(defthm wr-bytes-of-what-was-already-there
  (implies (and (equal (loghead (* 8 numbytes) v) (rd-bytes numbytes ad ram))
;                (integerp ad)
                (integerp numbytes)
                (<= 0 numbytes)
                )
           (equal (wr-bytes numbytes ad v ram)
                  ram))
  :hints (("Goal" :in-theory (enable wr-bytes rd-bytes))))

(defthm wr-bytes-of-what-was-already-there-cheap
  (implies (force (< numbytes (expt 2 32))) ;bzo added this when changing to fast-memories
           (equal (wr-bytes numbytes ad (rd-bytes numbytes ad ram) ram)
                  ram))
  :hints (("Goal" :in-theory (enable wr-bytes rd-bytes))))

(defthm rd-bytes-of-wr-bytes-diff
  (implies (bag::disjoint (offset-range-wrap 32 ad1 numbytes1) ;;(addr-range ad1 numbytes1)
                          (offset-range-wrap 32 ad2 numbytes2) ;;(addr-range ad2 numbytes2)
                          )
           ;; (bag::disjoint (addr-range ad1 numbytes1)
;;                           (addr-range ad2 numbytes2)
;;                           )
           (equal (rd-bytes numbytes1 ad1 (wr-bytes numbytes2 ad2 v2 ram))
                  (rd-bytes numbytes1 ad1 ram)))
  :hints (("Goal" :in-theory (e/d (wr-bytes rd-bytes) (DISJOINT-OF-TWO-ADDR-RANGES)))))

;;
;; CLR-BYTES
;;

;or should this call wr-bytes with 0?
(defund clr-bytes (numbytes ad ram)
  (clr-list ;;(addr-range ad numbytes)
   (offset-range-wrap 32 ad numbytes)
   ram))

(defthm clr-bytes-of-1
  (equal (clr-bytes 1 ad ram)
         (memory-clr ;(ifix ad)
          (loghead 32 ad)
          ram))
  :hints (("Goal" :in-theory (enable clr-bytes))))

(defthm wr-bytes-equal-rewrite
  (implies (force (< numbytes (expt 2 32))) ;bzo added this when changing to fast-memories
           (equal (equal (wr-bytes numbytes ad v ram1) ram2)
                  (if (integerp numbytes)
                      (and (equal (loghead (* 8 numbytes) v)
                                  (rd-bytes numbytes ad ram2))
                           (equal (clr-bytes numbytes ad ram1)
                                  (clr-bytes numbytes ad ram2)))
                    (equal ram1 ram2))))
  :hints (("Goal" :in-theory (enable wr-bytes rd-bytes clr-bytes))))

;kill?
;; (defthm clr-list-of-wr-cover
;;   (implies (list::memberp ad ads)
;;            (equal (clr-list ads (wr ad val ram))
;;                   (clr-list ads ram)))
;;   :hints (("Goal" :in-theory (enable clr-list))))

(defthm clr-bytes-of-wr-cover
  (implies (list::memberp ad (offset-range-wrap 32 ad2 numbytes) ;;(addr-range ad2 numbytes)
                          )
           (equal (clr-bytes numbytes ad2 (wr ad val ram))
                  (clr-bytes numbytes ad2 ram)))
  :hints (("Goal" :in-theory (enable clr-bytes))))


;; ;replacement for rx, except when numbytes is 0?
;; (defun rx2 (size a ram)
;;   (rd-bytes (* 1/8 (fix-size numbytes) ad ram)))


;; (defthm helper
;;   (implies (equal (wr-list ads vals ram1) ram2)
;;            (equal (clr-list ads ram1)
;;                   (clr-list ads ram2))))

;; (defthmd helper2
;;   (implies (equal (wr-list ads vals2 ram1) ram2)
;;            (equal (wr-list ads vals ram1)
;;                   (wr-list ads vals ram2))))

;; (defthmd helper3
;;   (implies (and (equal (wr-list ads0 vals2 ram1) ram2)
;;                 (subbagp ads0 ads))
;;            (equal (wr-list ads vals ram1)
;;                   (wr-list ads vals ram2))))

;; (defthmd helper-blah
;;   (implies (and (equal ram3 ram4)
;;                 (equal (rd ad ram1) (rd ad ram3))
;;                 (equal (rd ad ram2) (rd ad ram4))
;;                 )
;;            (equal (rd ad ram1) (rd ad ram2))))

;; (defthmd helper-blah2
;;   (implies (and (equal ram3 ram4)
;;                 (equal (rd ad ram1) (rd ad ram3))
;;                 (equal (rd ad ram2) (rd ad ram3))
;;                 )
;;            (equal (rd ad ram1) (rd ad ram2))))

;; (defthm memberp-hacl
;;   (IMPLIES (AND (CONSP ADS)
;;                 (NOT (MEMBERP AD ADS)))
;;            (not (equal ad (car ads)))
;;            ))

;; (defthm memberp-hacl2
;;   (IMPLIES (AND (CONSP ADS)
;;                 (NOT (MEMBERP AD ADS)))
;;            (not (memberp ad (cdr ads)))
;;            ))

;; (defthm fw2
;;   (implies t ;(unique ads)
;;            (implies (equal (wr-list ads vals ram1) ram2)
;;                     (equal (clr-list ads ram1)
;;                            (clr-list ads ram2))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :expand (CLR-LIST ADS RAM1)
;;            :in-theory (enable wfixlist WR==R!))))



;; ;not true if list of ads isn't unique!
;; (defthm fw1
;;  (implies (unique ads)
;;           (implies (equal (wr-list ads vals ram1) ram2)
;;                    (equal (my-wfixlist (len ads) vals) (rd-list ads ram2))))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;; ;          :expand (CLR-LIST ADS RAM1)
;;           :in-theory (enable wfixlist WR==R!))))


;; (defthm wr-list-when-ads-is-not-a-consp
;;   (implies (not (consp ads))
;;            (equal (wr-list ads vals ram)
;;                   ram)))


;; (defun ind (ads v1 v2 ram1 ram2)
;;   (if (endp ads)
;;       (list ads v1 v2 ram1 ram2)
;;     (ind (cdr ads) (cdr v1) (cdr v2) (wr (car ads) (car v1) ram1) (wr (car ads) (car v2) ram2))))


(local (in-theory (enable zp)))

;old:
;; For execution only.
;; We could reorder things to put the most common cases first..
;; Would the logapp nests be faster if they were expressed instead in terms of + and ash?
;; Add in type declarations (since the common cases fit in 32 bits).
;rename
;make tail recursive!
;; (defun rd-bytes-exec (numwords ad ram)
;;   (declare (type (integer 0 *) numwords)
;;            (type integer ad) ;weaken
;;            )
;;   (if (zp numwords)
;;       0
;;     (if (equal 1 numwords)
;;         (rd ad ram)
;;       (if (equal 2 numwords)
;;           (acl2::logapp 8 (rd ad ram) (rd (+ 1 ad) ram)) ;bzo
;;         (if (equal 4 numwords)
;;             (acl2::logapp 24
;;                           (acl2::logapp 16
;;                                         (acl2::logapp 8 (rd ad ram) (rd (+ 1 ad) ram))
;;                                         (rd (+ 2 ad) ram))
;;                           (rd (+ 3 ad) ram))
;;           (acl2::logapp 8 (rd ad ram) (rd-bytes-exec (+ -1 numwords) (+ 1 ad) ram)))))))


(defun addresses-of-data-word-univ (word-ad)
  (declare (type integer word-ad))
  (word-ad-to-byte-ads (loghead 31 word-ad) ;(logext 31 word-ad)
                       ))

(defthm CONSP-OF-CDR-OF-ADDRESSES-OF-DATA-WORD-univ
  (consp (cdr (ADDRESSES-OF-DATA-WORD-univ x))))

(defthm cddr-of-addresses-of-data-word-univ
  (equal (cddr (addresses-of-data-word-univ ad))
         nil))

(defthmd disjoint-of-addresses-of-data-word-univ-and-addresses-of-data-word-univ
  (equal (bag::disjoint (addresses-of-data-word-univ ad2)
                        (addresses-of-data-word-univ ad1))
         (not (equal (loghead 31 ad1) (loghead 31 ad2))))
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads))))

;word-ad is a usb31?
(defund read-data-word-univ (word-ad ram)
  (declare (type integer word-ad)
           (xargs :guard (aamp-ramp ram)
                  :guard-hints (("Goal" :in-theory (e/d (acl2::logext-logapp
                                                         read-data-word-exec
                                                         acl2::ash-as-logapp
                                                         word-ad-to-byte-ads
                                                         acl2::sum-with-shift-becomes-logapp-constant-version)
                                                        (acl2::logapp-0-part-2-better))))))
;  (mbe :exec (read-data-word-exec denvr offset ram)
;      :logic
  (wintlist (rd-list (addresses-of-data-word-univ word-ad)
                     ram))
;)
  )

(defthm unsigned-byte-p-of-read-data-word-univ
  (unsigned-byte-p 16 (read-data-word-univ ad ram))
  :rule-classes ((:forward-chaining :trigger-terms ((read-data-word-univ ad ram))))
  :hints (("Goal" :in-theory (enable read-data-word-univ))))

(defthm unsigned-byte-p-of-read-data-word-univ-gen
  (implies (and (integerp n)
                (<= 16 n))
           (unsigned-byte-p n (read-data-word-univ ad ram))))

(defthm address-listp-of-word-ad-to-byte-ads
  (implies (and (equal (mem::size ram) 4294967296)
                (unsigned-byte-p 31 ad))
           (address-listp (word-ad-to-byte-ads ad) ram))
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads))))

;bzo check this?
(defund write-data-word-univ (word-ad value ram)
  (declare (type integer word-ad value)
           (xargs :guard (aamp-ramp ram))
           ;;            (xargs :guard-hints (("Goal" :in-theory (e/d (acl2::logext-logapp
           ;;                                                          read-data-word-exec
           ;;                                                          acl2::ash-as-logapp
           ;;                                                          word-ad-to-byte-ads
           ;;                                                          acl2::sum-with-shift-becomes-logapp-constant-version)
           ;;                                                         (acl2::logapp-0-part-2-better)))))
           )
;  (mbe :exec (read-data-word-exec denvr offset ram)
;      :logic
  (wr-list (addresses-of-data-word-univ word-ad)
           (enlistw 2 value)
           ram)
;)
  )


;;
;; "read of write" lemmas
;;

(defthmd read-data-word-univ-of-write-data-word-univ-same
  (implies (equal (loghead 31 ad1) (loghead 31 ad2))
           (equal (read-data-word-univ ad1 (write-data-word-univ ad2 val ram))
                  (loghead 16 val)))
  :hints (("Goal" :in-theory
           (enable read-data-word-univ write-data-word-univ WORD-AD-TO-BYTE-ADS))))

(defthm read-data-word-univ-of-write-data-word-univ-same-cheap
  (equal (read-data-word-univ ad (write-data-word-univ ad val ram))
         (loghead 16 val))
  :hints (("Goal" :in-theory
           (enable read-data-word-univ write-data-word-univ WORD-AD-TO-BYTE-ADS))))

;rewrite the hyp to a claim about logheads?
(defthm read-data-word-univ-of-write-data-word-univ-diff
  (implies (bag::disjoint (addresses-of-data-word-univ ad2)
                          (addresses-of-data-word-univ ad1))
           (equal (read-data-word-univ ad1 (write-data-word-univ ad2 val ram))
                  (read-data-word-univ ad1 ram)))
  :hints (("Goal" :in-theory
           (enable read-data-word-univ write-data-word-univ WORD-AD-TO-BYTE-ADS))))

(in-theory (disable disjoint-of-word-ad-to-byte-ads)) ;bzo

(defthmd read-data-word-univ-of-write-data-word-univ-both
  (equal (read-data-word-univ ad1 (write-data-word-univ ad2 val ram))
         (if (equal (loghead 31 ad1) (loghead 31 ad2))
             (loghead 16 val)
           (read-data-word-univ ad1 ram)))
  :hints (("Goal" :in-theory (enable read-data-word-univ write-data-word-univ))))

;;
;; "write of write" lemmas
;;

(defthmd write-data-word-univ-of-write-data-word-same
  (implies (equal (loghead 31 ad1) (loghead 31 ad2))
           (equal (write-data-word-univ ad1 val1 (write-data-word-univ ad2 val2 ram))
                  (write-data-word-univ ad1 val1 ram)))
  :hints (("Goal" :in-theory (enable WRITE-DATA-WORD-UNIV))))

(defthm write-data-word-univ-of-write-data-word-same-cheap
  (equal (write-data-word-univ ad val1 (write-data-word-univ ad val2 ram))
         (write-data-word-univ ad val1 ram))
  :hints (("Goal" :in-theory (enable write-data-word-univ))))

;bzo How do we want to sort the writes?
(defthm write-data-word-univ-of-write-data-word-univ-diff
  (implies (bag::disjoint (addresses-of-data-word-univ ad2)
                          (addresses-of-data-word-univ ad1))
           (equal (write-data-word-univ ad1 val1 (write-data-word-univ ad2 val2 ram))
                  (write-data-word-univ ad2 val2 (write-data-word-univ ad1 val1 ram))))
  :rule-classes ((:rewrite :loop-stopper ((ad2 ad1))))
  :hints (("Goal" :in-theory (enable WRITE-DATA-WORD-UNIV))))

(defthmd write-data-word-univ-of-write-data-word-univ-both
  (equal (write-data-word-univ ad1 val1 (write-data-word-univ ad2 val2 ram))
         (if (equal (loghead 31 ad1) (loghead 31 ad2))
             (write-data-word-univ ad1 val1 ram)
           (write-data-word-univ ad2 val2 (write-data-word-univ ad1 val1 ram))))
  :rule-classes ((:rewrite :loop-stopper ((ad2 ad1))))
  :hints (("Goal" :in-theory (enable WRITE-DATA-WORD-UNIV))))

(defund clear-data-word-univ (word-ad ram)
  (declare (type integer word-ad)
           (xargs :guard (aamp-ramp ram))
           )
  (write-data-word-univ word-ad 0 ram))

(defthm write-data-word-univ-equal-rewrite
  (equal (equal (write-data-word-univ ad value ram1) ram2)
         (and (equal (loghead 16 value) (read-data-word-univ ad ram2))
              (equal (clear-data-word-univ ad ram1)
                     (clear-data-word-univ ad ram2))))
  :hints (("Goal" :in-theory (enable WRITE-DATA-WORD-UNIV
                                     READ-DATA-WORD-UNIV
                                     WORD-AD-TO-BYTE-ADS
                                     ACL2::EQUAL-LOGAPP-X-Y-Z
                                     WR==R!
                                     clear-data-word-univ
                                     ))))


;;
;; Multiple word ops
;;


(defun addresses-of-data-words-univ (numwords word-ad)
  (declare (type integer word-ad)
           (type (integer 0 *) numwords))
  (word-ads-to-byte-ads ;;(logext-list 31 (offset-range-wrap 31 word-ad numwords))
   (loghead-list 31 (offset-range-wrap 31 word-ad numwords)) ;bzo drop the loghead-list 31 call? and similar stuff elsewhere!
   )
  )

(defthm address-listp-of-append
  (equal (address-listp (append x y) ram)
         (and (address-listp x ram)
              (address-listp y ram))))

(defthm address-listp-of-word-ads-to-byte-ads
  (implies (and (equal (mem::size ram) 4294967296)
                (unsigned-byte-p-list 31 word-ads))
           (address-listp (WORD-ADS-TO-BYTE-ADS word-ads) ram))
  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads))))

;; Read NUMWORDS words of data from RAM, starting at word address AD.  (RAM is
;; byte-addressable, so we have to shift WORD-AD to the left one bit.)  Data
;; from the lower addresses goes into the lower-order positions of the result.
;; No wrapping is done.
;;

;word-ad is a usb31?
(defund read-data-words-univ (numwords word-ad ram)
  (declare (type (integer 0 *) numwords) ;trying...;(type (integer 0 *) numwords); (type (integer 0 *) numwords)
           (type integer word-ad)
           (xargs :guard (aamp-ramp ram))
;           (type (unsigned-byte 31) word-ad)
           ;;            (xargs :guard-hints (("Goal" :expand  ((offset-range-wrap offset 2)
           ;;                                                   (offset-range-wrap offset numwords))
           ;;                                  :induct t
           ;;                                  :do-not '(generalize eliminate-destructors)
           ;;                                  :in-theory (e/d (word-ad-to-byte-ads
           ;;                                                   ACL2::SUM-WITH-SHIFT-BECOMES-LOGAPP-CONSTANT-VERSION
           ;;                                                   read-data-word-exec
           ;;                                                   acl2::logext-logapp
           ;;                                                   acl2::ash-as-logapp
           ;;                                                   read-data-words-exec)
           ;;                                                  (acl2::logapp-0-part-2-better
           ;;                                                   acl2::loghead-sum-split-into-2-when-i-is-a-constant)))))
           )
;  (mbe :exec (read-data-words-exec numwords denvr offset ram)
;      :logic
  (wintlist (rd-list (addresses-of-data-words-univ numwords word-ad)
                     ram))
;)
  )

;bzo move
(defthm read-data-words-univ-when-numwords-is-non-positive
  (implies (<= numwords 0)
           (equal (read-data-words-univ numwords ad ram)
                  0))
  :hints (("Goal" :in-theory (enable read-data-words-univ))))

(defthm read-data-words-univ-when-numwords-is-not-an-integerp
  (implies (not (integerp numwords))
           (equal (read-data-words-univ numwords ad ram)
                  0))
  :hints (("Goal" :in-theory (enable read-data-words-univ))))

(defthm read-data-words-univ-when-ad-is-not-an-integerp
  (implies (not (integerp ad))
           (equal (read-data-words-univ numwords ad ram)
                  (read-data-words-univ numwords 0 ram)))
  :hints (("Goal" :in-theory (enable read-data-words-univ))))

;; (defthm read-data-words-univ-of-1
;;   (equal (read-data-words-univ 1 ad ram)
;;          (rd (ifix ad) ram))
;;   :hints (("Goal" :in-theory (enable read-data-words-univ))))

;bzo instead open to multiple calls of read-data-word-univ
(defthmd read-data-words-univ-constant-opener
  (implies (syntaxp (quotep numwords))
           (equal (read-data-words-univ numwords word-ad ram)
                  (wintlist (rd-list (addresses-of-data-words-univ numwords word-ad)
                                     ram))))
  :hints (("Goal" :in-theory (enable read-data-words-univ))))

(defthm unsigned-byte-p-of-read-data-words-univ
  (implies (and (integerp numwords)
                (<= 0 numwords)
                )
           (unsigned-byte-p (* 16 numwords) (read-data-words-univ numwords ad ram)))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ( (read-data-words-univ numwords ad ram))))
  :hints (("Goal" ; :cases ((integerp numwords))
           :in-theory (enable read-data-words-univ))))

(defthm unsigned-byte-p-of-read-data-words-univ-gen
  (implies (and (<= (* 16 numwords) n)
                (integerp n)
                (<= 0 n)
                (integerp numwords)
                (<= 0 numwords)
                )
           (unsigned-byte-p n (read-data-words-univ numwords ad ram))))

;bzo put these back!
;; ;bzo gen the 8
;; (defthm loghead8-of-read-data-words-univ
;;   (implies (integerp ad) ;bzo
;;            (equal (LOGHEAD 8 (READ-DATA-WORDS-UNIV numwords ad ram))
;;                   (if (and (integerp numwords)
;;                            (< 0 numwords))
;;                       (rd ad ram)
;;                     0)))
;;   :hints (("Goal" :in-theory (enable READ-DATA-WORDS-UNIV))))

;; (defthm logtail8-of-read-data-words-univ
;;   (implies (integerp ad) ;bzo use ifix!
;;            (equal (LOGtail 8 (READ-DATA-WORDS-UNIV numwords ad ram))
;;                   (if (and (integerp numwords)
;;                            (< 0 numwords))
;;                        (READ-DATA-WORDS-UNIV (+ -1 numwords) (+ 1 ad) ram)
;;                     0)))
;;   :hints (("Goal" :in-theory (enable READ-DATA-WORDS-UNIV))))


;; (defthm read-data-words-univ-when-numwords-is-non-negative
;;   (implies (<= numwords 0)
;;            (equal (read-data-words-univ numwords ad ram)
;;                   nil))
;;   :hints (("Goal" :in-theory (enable read-data-words-univ))))







;;
;; WR-BYTES
;;
;;bzo add mbe

(defund write-data-words-univ (numwords word-ad value ram)
  (declare (type integer word-ad value)
           (type (integer 0 *) numwords)
           (xargs :guard (aamp-ramp ram))
           )
  (wr-list (addresses-of-data-words-univ numwords word-ad)
           ;;(logext-list 32 (word-ads-to-byte-ads (addr-range word-ad numwords)))
;           (word-list-to-byte-list (split-into-words numwords value))
           (enlistw (* 2 numwords) value)
           ram))

(defthm write-data-words-univ-when-numwords-is-non-positive
  (implies (<= numwords 0)
           (equal (write-data-words-univ numwords ad value ram)
                  ram))
  :hints (("Goal" :in-theory (enable write-data-words-univ))))

(defthm write-data-words-univ-when-numwords-is-not-an-integerp
  (implies (not (integerp numwords))
           (equal (write-data-words-univ numwords ad v ram)
                  ram))
  :hints (("Goal" :in-theory (enable write-data-words-univ))))

(defthm write-data-words-univ-when-ad-is-not-an-integerp
  (implies (not (integerp ad))
           (equal (write-data-words-univ numwords ad v ram)
                  (write-data-words-univ numwords 0 v ram)))
  :hints (("Goal" :in-theory (enable write-data-words-univ))))

(defthm write-data-words-univ-of-write-data-words-univ-same
  (equal (write-data-words-univ numwords ad v1 (write-data-words-univ numwords ad v2 ram))
         (write-data-words-univ numwords ad v1 ram))
  :hints (("Goal" :in-theory (enable write-data-words-univ))))

;is this the best way to phrase the hyp?
;use offset-range-wrap with a size of 32?
;say that the 2 starting ads are usb 31s?
;bzo hyp
(defthm write-data-words-univ-of-write-data-words-univ-diff
  (implies (disjoint (offset-range-wrap 31 (ifix ad1) numwords1)
                     (offset-range-wrap 31 (ifix ad2) numwords2))
           (equal (write-data-words-univ numwords1 ad1 v1 (write-data-words-univ numwords2 ad2 v2 ram))
                  (write-data-words-univ numwords2 ad2 v2 (write-data-words-univ numwords1 ad1 v1 ram))))
  :hints (("Goal" :in-theory (e/d (write-data-words-univ)
                                  (DISJOINT-OF-TWO-OFFSET-RANGE-WRAPS
                                    disjoint-of-word-ads-to-byte-ads
                                    disjoint-of-two-addr-ranges)))))


;;
;; lemmas about READ-DATA-WORDS-UNIV and WRITE-DATA-WORDS-UNIV together
;;

(local (in-theory (disable ACL2::LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT)))

(DEFTHMd ACL2::ASH-LOGHEAD
  (IMPLIES (AND (< 0 ACL2::M)
                (INTEGERP ACL2::N)
                (INTEGERP ACL2::X)
                (INTEGERP ACL2::M)
                (< 0 ACL2::N)
                (< 0 (+ ACL2::N ACL2::M)))
           (EQUAL (ASH (LOGHEAD ACL2::N ACL2::X) ACL2::M)
                  (LOGhead (+ ACL2::N ACL2::M)
                          (ASH ACL2::X ACL2::M))))
  :HINTS (("goal" :IN-THEORY (ENABLE ACL2::LRDT))))

;; ;bzo generalize  to subbagp?
;; (defthm write-data-words-univ-of-write-data-words-univ-same
;;   (implies (bag::subbagp (addr-range ad2 numwords2) (addr-range ad1 numwords1))
;;            (equal (write-data-words-univ numwords1 ad1 v1 (write-data-words-univ numwords2 ad2 v2 ram))
;;                   (write-data-words-univ numwords1 ad1 v1 ram)))
;;   :hints (("Goal" :in-theory (enable write-data-words-univ))))

(defthm write-data-words-univ-of-what-was-already-there
  (implies (and (equal (loghead (* 16 numwords) v) (read-data-words-univ numwords ad ram))
;                (integerp ad)
                (integerp numwords)
                (<= 0 numwords)
                )
           (equal (write-data-words-univ numwords ad v ram)
                  ram))
  :hints (("Goal" :in-theory (enable write-data-words-univ read-data-words-univ))))

(defthm write-data-words-univ-of-what-was-already-there-cheap
  (implies (and (integerp numwords)
                (<= 0 numwords))
           (equal (write-data-words-univ numwords ad (read-data-words-univ numwords ad ram) ram)
                  ram))
  :otf-flg t
  :hints (("Goal" :use (:instance  write-data-words-univ-of-what-was-already-there (v  (read-data-words-univ numwords ad ram)))
           :in-theory (disable  write-data-words-univ-of-what-was-already-there))))

(defthm read-data-words-univ-of-write-data-words-univ-diff
  (implies (bag::disjoint (offset-range-wrap 31 ad1 numwords1)
                          (offset-range-wrap 31 ad2 numwords2))
           (equal (read-data-words-univ numwords1 ad1 (write-data-words-univ numwords2 ad2 v2 ram))
                  (read-data-words-univ numwords1 ad1 ram)))
  :hints (("Goal" :in-theory (e/d (write-data-words-univ read-data-words-univ)
                                  (disjoint-of-word-ads-to-byte-ads
                                   DISJOINT-OF-TWO-ADDR-RANGES)))))

;make a clear-data-word-univ
;;
;; CLEAR-DATA-WORDS-UNIV
;;

(defund clear-data-words-univ (numwords word-ad ram)
  (declare (type integer word-ad)
           (type (integer 0 *) numwords)
           (xargs :guard (aamp-ramp ram)))
  (write-data-words-univ numwords word-ad 0 ram))

;; (defthm clear-data-words-univ-of-1
;;   (equal (clear-data-words-univ 1 ad ram)
;;          (clr (ifix ad) ram))
;;   :hints (("Goal" :in-theory (enable clear-data-words-univ))))

(defthm write-data-words-univ-equal-rewrite
  (implies (<= NUMWORDS 2147483648)
           (equal (equal (write-data-words-univ numwords ad v ram1) ram2)
                  (if (integerp numwords)
                      (and (equal (loghead (* 16 numwords) v)
                                  (read-data-words-univ numwords ad ram2))
                           (equal (clear-data-words-univ numwords ad ram1)
                                  (clear-data-words-univ numwords ad ram2)))
                    (equal ram1 ram2))))
  :hints (("Goal" :in-theory (enable write-data-words-univ read-data-words-univ clear-data-words-univ))))

;; (defthm clear-data-words-univ-of-wr-cover
;;   (implies (list::memberp ad (addr-range ad2 numwords))
;;            (equal (clear-data-words-univ numwords ad2 (wr ad val ram))
;;                   (clear-data-words-univ numwords ad2 ram)))
;;   :hints (("Goal" :in-theory (enable clear-data-words-univ))))


;; ;replacement for rx, except when numwords is 0?
;; (defun rx2 (size a ram)
;;   (read-data-words-univ (* 1/8 (fix-size numwords) ad ram)))


;; (defthm helper
;;   (implies (equal (wr-list ads vals ram1) ram2)
;;            (equal (clr-list ads ram1)
;;                   (clr-list ads ram2))))

;; (defthmd helper2
;;   (implies (equal (wr-list ads vals2 ram1) ram2)
;;            (equal (wr-list ads vals ram1)
;;                   (wr-list ads vals ram2))))

;; (defthmd helper3
;;   (implies (and (equal (wr-list ads0 vals2 ram1) ram2)
;;                 (subbagp ads0 ads))
;;            (equal (wr-list ads vals ram1)
;;                   (wr-list ads vals ram2))))

;; (defthmd helper-blah
;;   (implies (and (equal ram3 ram4)
;;                 (equal (rd ad ram1) (rd ad ram3))
;;                 (equal (rd ad ram2) (rd ad ram4))
;;                 )
;;            (equal (rd ad ram1) (rd ad ram2))))

;; (defthmd helper-blah2
;;   (implies (and (equal ram3 ram4)
;;                 (equal (rd ad ram1) (rd ad ram3))
;;                 (equal (rd ad ram2) (rd ad ram3))
;;                 )
;;            (equal (rd ad ram1) (rd ad ram2))))

;; (defthm memberp-hacl
;;   (IMPLIES (AND (CONSP ADS)
;;                 (NOT (MEMBERP AD ADS)))
;;            (not (equal ad (car ads)))
;;            ))

;; (defthm memberp-hacl2
;;   (IMPLIES (AND (CONSP ADS)
;;                 (NOT (MEMBERP AD ADS)))
;;            (not (memberp ad (cdr ads)))
;;            ))

;; (defthm fw2
;;   (implies t ;(unique ads)
;;            (implies (equal (wr-list ads vals ram1) ram2)
;;                     (equal (clr-list ads ram1)
;;                            (clr-list ads ram2))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :expand (CLR-LIST ADS RAM1)
;;            :in-theory (enable wfixlist WR==R!))))



;; ;not true if list of ads isn't unique!
;; (defthm fw1
;;  (implies (unique ads)
;;           (implies (equal (wr-list ads vals ram1) ram2)
;;                    (equal (my-wfixlist (len ads) vals) (rd-list ads ram2))))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;; ;          :expand (CLR-LIST ADS RAM1)
;;           :in-theory (enable wfixlist WR==R!))))


;; (defthm wr-list-when-ads-is-not-a-consp
;;   (implies (not (consp ads))
;;            (equal (wr-list ads vals ram)
;;                   ram)))


;; (defun ind (ads v1 v2 ram1 ram2)
;;   (if (endp ads)
;;       (list ads v1 v2 ram1 ram2)
;;     (ind (cdr ads) (cdr v1) (cdr v2) (wr (car ads) (car v1) ram1) (wr (car ads) (car v2) ram2))))


(defthmd write-data-words-univ-opener
  (implies (and (syntaxp (quotep numwords))
                (not (zp numwords)))
           (equal (write-data-words-univ numwords ad value ram)
                  (write-data-word-univ ad (loghead 16 value)
                                   (write-data-words-univ (+ -1 numwords) (+ 1 (ifix ad)) (logtail 16 value)
                                                          ram))))
  :hints (("Goal" :expand ((OFFSET-RANGE-WRAP 31 ad NUMWORDS)
                           (OFFSET-RANGE-WRAP 31 0 NUMWORDS))
           :in-theory (e/d (write-data-words-univ write-data-word-univ
                                             WORD-AD-TO-BYTE-ADS)
                           ( ;makeaddr-of-+-loghead
                            )))))

(defthmd read-data-words-univ-opener
  (implies (and (syntaxp (quotep numwords))
                (not (zp numwords)))
           (equal (read-data-words-univ numwords ad ram)
                  (logapp 16
                          (read-data-word-univ ad ram)
                          (read-data-words-univ (+ -1 numwords)
                                                (+ 1 (ifix ad))
                                           ram))))
  :hints
  (("Goal" :expand ((OFFSET-RANGE-WRAP 31 ad NUMWORDS)
                    (OFFSET-RANGE-WRAP 31 0 NUMWORDS))
    :in-theory
    (e/d (READ-DATA-WORD-univ
          read-data-words-univ
          WORD-AD-TO-BYTE-ADS
          OFFSET-RANGE-WRAP-CONST-OPENER
          ACL2::ASH-AS-LOGAPP
          ACL2::LOGEXT-LOGAPP)
         ( ;makeaddr-of-+-loghead
          ACL2::LOGAPP-0-PART-2-BETTER
          ACL2::LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT
          )))))


;; Lemmas mixing the ram3 primitives and the ram2 primitives (where should these go?):

;; Primitives (assuming we split all multi-word operations into repeated calls to single word operations):

;; "reads":
;; read-data-word
;; read-data-word-univ
;; fetch-code-byte

;; "writes":
;; write-data-word
;; write-data-word-univ

;; "clears":
;; clear-data-word
;; clear-data-word-univ


;rephrase hyp?
(defthm fetch-code-byte-of-write-data-word-univ
  (implies (not (memberp (make-code-addr cenvr offset) (addresses-of-data-word-univ ad)))
           ;;(not (equal (acl2::logcdr (loghead 16 cenvr)) (logtail 16 (loghead 31 ad))))
           (equal (fetch-code-byte cenvr offset (write-data-word-univ ad val ram))
                  (fetch-code-byte cenvr offset ram)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (write-data-word
                            acl2::loghead-logcdr
                            write-data-word-univ
                            make-code-addr
                            word-ad-to-byte-ads
                            fetch-code-byte no-code-data-clash)
                           (addresses-of-data-word-univ
                            make-code-addr
                            acl2::logcdr-loghead)))))

;rephrase hyp?
(defthm read-data-word-of-write-data-word-univ
  (implies (bag::disjoint (addresses-of-data-word denvr offset)
                          (addresses-of-data-word-univ ad))
           (equal (read-data-word denvr offset (write-data-word-univ ad val ram))
                  (read-data-word denvr offset ram)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (write-data-word
                            read-data-word
                            acl2::loghead-logcdr
                            write-data-word-univ
                            make-code-addr
                            word-ad-to-byte-ads
                            fetch-code-byte no-code-data-clash)
                           (addresses-of-data-word-univ
                            addresses-of-data-word
                            make-code-addr
                            acl2::logcdr-loghead)))))

;rephrase hyp?
(defthm read-data-word-univ-of-write-data-word
  (implies (bag::disjoint (addresses-of-data-word denvr offset)
                          (addresses-of-data-word-univ ad))
           (equal (read-data-word-univ ad (write-data-word denvr offset val ram))
                  (read-data-word-univ ad ram)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (write-data-word
                            read-data-word-univ
                            acl2::loghead-logcdr
                            write-data-word-univ
                            make-code-addr
                            word-ad-to-byte-ads
                            fetch-code-byte no-code-data-clash)
                           (addresses-of-data-word-univ
                            addresses-of-data-word
                            make-code-addr
                            acl2::logcdr-loghead)))))


;; We move the universal writes inside the regular writes (since regular
;; writes include writes to the stack and locals, we expect them to be more
;; common than universal writes, so we want to make the more "exposed" by
;; brining them to the outside of the nest of writes.
;;
;;rephrase hyp?
(defthm write-data-word-univ-of-write-data-word
  (implies (bag::disjoint (addresses-of-data-word denvr offset)
                          (addresses-of-data-word-univ ad))
           (equal (write-data-word-univ ad val1 (write-data-word denvr offset val2 ram))
                  (write-data-word denvr offset val2 (write-data-word-univ ad val1 ram))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (write-data-word
                            read-data-word-univ
                            acl2::loghead-logcdr
                            write-data-word-univ
                            make-code-addr
                            word-ad-to-byte-ads
                            fetch-code-byte no-code-data-clash)
                           (addresses-of-data-word-univ
                            addresses-of-data-word
                            make-code-addr
                            acl2::logcdr-loghead)))))

;; We leave this disabled, in favor of write-data-word-univ-of-write-data-word.
;;
;;rephrase hyp?
(defthmd write-data-word-of-write-data-word-univ
  (implies (bag::disjoint (addresses-of-data-word denvr offset)
                          (addresses-of-data-word-univ ad))
           (equal (write-data-word denvr offset val2 (write-data-word-univ ad val1 ram))
                  (write-data-word-univ ad val1 (write-data-word denvr offset val2 ram))))
  :hints (("Goal" :use (:instance write-data-word-univ-of-write-data-word)
           :in-theory (disable write-data-word-univ-of-write-data-word))))

;; "read of clear" lemmas

(defthmd read-data-word-univ-of-clear-data-word-univ-same
  (implies (equal (loghead 31 ad1) (loghead 31 ad2))
           (equal (read-data-word-univ ad1 (clear-data-word-univ ad2 ram))
                  0))
  :hints (("Goal" :in-theory (enable clear-data-word-univ
                                     READ-DATA-WORD-UNIV-OF-WRITE-DATA-WORD-UNIV-SAME ;bzo
                                     ))))

(defthm read-data-word-univ-of-clear-data-word-univ-same-cheap
  (equal (read-data-word-univ ad (clear-data-word-univ ad ram))
         0)
  :hints (("Goal" :in-theory (enable clear-data-word-univ
                                     READ-DATA-WORD-UNIV-OF-WRITE-DATA-WORD-UNIV-SAME ;bzo
                                     ))))

;rewrite the hyp to a claim about logheads?
(defthm read-data-word-univ-of-clear-data-word-univ-diff
  (implies (bag::disjoint (addresses-of-data-word-univ ad2)
                          (addresses-of-data-word-univ ad1))
           (equal (read-data-word-univ ad1 (clear-data-word-univ ad2 ram))
                  (read-data-word-univ ad1 ram)))
  :hints (("Goal" :in-theory (enable clear-data-word-univ))))

(defthmd read-data-word-univ-of-clear-data-word-univ-both
  (equal (read-data-word-univ ad1 (clear-data-word-univ ad2 ram))
         (if (equal (loghead 31 ad1) (loghead 31 ad2))
             0
           (read-data-word-univ ad1 ram)))
  :hints (("Goal" :in-theory (enable clear-data-word-univ
                                     read-data-word-univ-of-write-data-word-univ-both))))



;;lemmas about clear-data-word-univ

(defthm fetch-code-byte-of-clear-data-word-univ
  (implies (not (memberp (make-code-addr cenvr offset) (addresses-of-data-word-univ ad)))
           ;;(not (equal (acl2::logcdr (loghead 16 cenvr)) (logtail 16 (loghead 31 ad))))
           (equal (fetch-code-byte cenvr offset (clear-data-word-univ ad ram))
                  (fetch-code-byte cenvr offset ram)))
  :hints (("Goal" :in-theory (enable clear-data-word-univ))))

;rephrase hyp?
(defthm read-data-word-of-clear-data-word-univ
  (implies (bag::disjoint (addresses-of-data-word denvr offset)
                          (addresses-of-data-word-univ ad))
           (equal (read-data-word denvr offset (clear-data-word-univ ad ram))
                  (read-data-word denvr offset ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-word-univ)
                                  (DISJOINT-OF-TWO-WORD-AD-TO-BYTE-ADS ;bzo
                                   )))))

(defthm read-data-word-univ-of-clear-data-word
  (implies (bag::disjoint (addresses-of-data-word denvr offset)
                          (addresses-of-data-word-univ ad))
           (equal (read-data-word-univ ad (clear-data-word denvr offset ram))
                  (read-data-word-univ ad ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-word)
                                  (DISJOINT-OF-TWO-WORD-AD-TO-BYTE-ADS ;bzo
                                   WRITE-DATA-WORD-EQUAL-REWRITE)
                                   ))))

(defthm read-data-words-univ-of-logext-special-case
  (equal (gacc::read-data-words-univ 2 (logext 32 x) ram)
         (gacc::read-data-words-univ 2 x ram))
  :hints (("Goal" :in-theory (enable gacc::read-data-words-univ))))

(defthm read-data-word-univ-of-logext
  (equal (gacc::read-data-word-univ (logext 32 word-ad) ram)
         (gacc::read-data-word-univ word-ad ram))
  :hints (("Goal" :in-theory (enable gacc::read-data-word-univ))))

(defthm write-data-word-univ-of-logext
  (equal (gacc::write-data-word-univ (logext 32 word-ad) val ram)
         (gacc::write-data-word-univ word-ad val ram))
  :hints (("Goal" :in-theory (enable gacc::write-data-word-univ))))

(defthmd addresses-of-data-words-univ-constant-opener
  (implies (and (syntaxp (quotep numwords))
                (integerp numwords)
                (< 0 numwords)
                (integerp word-ad))
           (equal (gacc::addresses-of-data-words-univ numwords word-ad)
                  (append (gacc::addresses-of-data-word-univ word-ad)
                          (gacc::addresses-of-data-words-univ (+ -1 numwords) (+ 1 word-ad)))))
  :hints (("Goal" :expand (gacc::word-ads-to-byte-ads (gacc::offset-range-wrap 31 word-ad numwords))
           :in-theory (enable gacc::word-ads-to-byte-ads))))

;bzo gen
(defthm write-data-words-univ-2-of-logext
 (equal (gacc::write-data-words-univ 2 (logext 32 ad) val ram)
        (gacc::write-data-words-univ 2 ad val ram))
 :hints (("Goal" :in-theory (enable gacc::write-data-words-univ))))

;bzo gen
(defthm write-data-words-univ-2-of-logext-around-vale
 (equal (gacc::write-data-words-univ 2 ad (logext 32 val) ram)
        (gacc::write-data-words-univ 2 ad val ram))
 :hints (("Goal" :in-theory (enable gacc::write-data-words-univ))))

(defthm addresses-of-data-words-univ-of-0
  (equal (gacc::addresses-of-data-words-univ 0 word-ad)
         nil))

(defthm read-data-words-univ-of-1
  (equal (gacc::read-data-words-univ 1 gacc::word-ad gacc::ram)
         (gacc::read-data-word-univ gacc::word-ad gacc::ram))
  :hints (("Goal" :in-theory (enable gacc::read-data-words-univ-opener))))

;bzo add guards to these...
(defun gather-constant-factors (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (not (consp term)) ;e.g., a variable
      (list 1)
    (if (and (equal 'quote (car term))
             (integerp (cadr term)))
        (list (cadr term))
      (if (equal 'binary-+ (car term))
          (append (gather-constant-factors (cadr term))
                  (gather-constant-factors (caddr term)))
        (if (equal 'unary-- (car term))
            (gather-constant-factors (cadr term))
          (if (equal 'binary-* (car term)) ;assumes the constant (if any) has been brought to the front of the product
              (if (and (quotep (cadr term))
                       (integerp (cadadr term)))
                  (list (cadr (cadr term)))
                (list 1))
            (list 1)))))))

;only works for positive numbers?
(defun gcd-aux (i j)
  (declare (xargs :measure (nfix j)
                  :guard (and (integerp i) (integerp j) (<= 0 j))))
  (if (zp j)
      1
    (let ((r (mod i j)))
      (if (zp r)
          j
        (gcd-aux j r)))))

;what should this do for negative numbers?
(defun greatest-common-divisor (i j)
  (declare (xargs :guard (and (integerp i) (integerp j))))
  (gcd-aux (max (abs i) (abs j)) (min (abs i) (abs j))))

(defun gcd-many (lst)
  (declare (xargs :guard (integer-listp lst) :verify-guards nil))
  (if (endp lst)
      1
    (if (endp (cdr lst))
        (car lst)
      (greatest-common-divisor (car lst)
                               (gcd-many (cdr lst))))))

(defthm integerp-of-gcd-many
  (implies (integer-listp lst)
           (integerp (gcd-many lst))))

(defthm integer-listp-of-gather-constant-factors
  (integer-listp (gather-constant-factors term)))

(defun greatest-common-constant-factor (term1 term2)
  (declare (xargs :guard (and (pseudo-termp term1)
                              (pseudo-termp term2))))
  (greatest-common-divisor (gcd-many (gather-constant-factors term1))
                           (gcd-many (gather-constant-factors term2))))

(defun bind-x-to-greatest-common-constant-factor (term1 term2)
  (declare (xargs :guard (and (pseudo-termp term1)
                              (pseudo-termp term2))))
  (acons 'x `(quote ,(greatest-common-constant-factor term1 term2)) nil))


;what about multiplying by constant factor in denominator?
(defthm cancel-common-constant-factor-from-<
  (implies (and (BIND-FREE (bind-x-to-greatest-common-constant-factor LHS RHS) (X))
                (< 1 x) ;otherwise, this rule might loop
                (integerp x)
                (rationalp lhs)
                (rationalp rhs))
           (equal (< lhs rhs)
                  (< (/ lhs x) (/ rhs x)))))

(defthm cancel-common-constant-factor-from-=
  (implies (and (BIND-FREE (bind-x-to-greatest-common-constant-factor LHS RHS) (X))
                (< 1 x) ;otherwise, this rule might loop
                (integerp x)
                (rationalp lhs)
                (rationalp rhs))
           (equal (equal lhs rhs)
                  (equal (/ lhs x) (/ rhs x)))))

;bzo allow denvrs to differ everywhere appropriate?

(local (in-theory (enable zp)))


(defthm wr-same-rd-non-cheap
  (implies (equal val (rd ad ram))
           (equal (wr ad val ram)
                  ram)))

;bzo can loop
(defthm wr-of-0-becomes-clr
  (equal (wr ad 0 ram)
         (memory-clr ad ram))
  :hints (("Goal" :in-theory (enable))))

#+joe
(defthm clr-of-wr-diff
  (implies (not (equal ad1 ad2))
           (equal (memory-CLR ad1 (WR ad2 value ram))
                  (wr ad2 value (memory-CLR ad1 ram))))
  :hints (("Goal" :in-theory (e/d (CLR) (wr-of-0-becomes-clr)))))

#+joe
(defthm clr-of-wr-same
  (equal (clr ad (wr ad value ram))
         (clr ad ram))
  :hints (("Goal" :in-theory (e/d (clr) (wr-of-0-becomes-clr)))))


;add loop-stopper?
#+joe
(defthm clr-of-clr-diff
  (implies (not (equal ad1 ad2))
           (equal (clr ad1 (clr ad2 ram))
                  (clr ad2 (clr ad1 ram))))
  :hints (("Goal" :in-theory (e/d (clr) (wr-of-0-becomes-clr)))))

#+joe
(DEFTHM RD-OF-clr-both
  (EQUAL (RD ACL2::A (clr ACL2::B ACL2::R))
         (IF (EQUAL ACL2::B ACL2::A)
             0
             (RD ACL2::A ACL2::R)))
  :hints (("Goal" :in-theory (e/d (clr) (wr-of-0-becomes-clr)))))


;bzo dup
;move
(defthm unsigned-byte-p-list-of-offset-range-wrap
  (implies (natp n)
           (unsigned-byte-p-list n (offset-range-wrap n ad numbytes)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-list offset-range-wrap))))

;; (defthm unsigned-byte-p-list-of-offset-range-wrap
;;   (unsigned-byte-p-list 31 (offset-range-wrap 31 base ads))
;;   :hints (("Goal" :in-theory (enable offset-range-wrap unsigned-byte-p-list))))



;;
;; Converting word addresses to byte addresses.
;;



;; Convert the word address WORD-AD to a list of its two corresponding byte
;; addresses.
;;
(defun word-ad-to-byte-ads (word-ad)
  (declare (type integer word-ad))
  (list (logapp 1 0 word-ad)
        (logapp 1 1 word-ad)))

(defthm consp-of-word-ad-to-byte-ads
  (consp (word-ad-to-byte-ads word-ad)))

(defthm len-of-word-ad-to-byte-ads
  (equal (len (word-ad-to-byte-ads word-ad))
         2)
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads))))

(defthm consp-cdr-word-ad-to-byte-ads
  (equal (consp (cdr (word-ad-to-byte-ads word-ad)))
         t)
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads))))


(defthm integer-listp-of-word-ad-to-byte-ads
  (implies (integerp word-ad)
           (integer-listp (word-ad-to-byte-ads word-ad)))
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads))))

(defthm memberp-of-word-ad-to-byte-ads
  (equal (memberp b (word-ad-to-byte-ads a))
         (and (integerp b)
              (equal (ifix a) (acl2::logcdr b))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable word-ad-to-byte-ads))))

(defthm integerp-of-cadr-of-word-ad-to-byte-ads
  (integerp (car (cdr (word-ad-to-byte-ads word-ad))))
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads))))

(defthm integerp-of-car-of-word-ad-to-byte-ads
  (integerp (car (word-ad-to-byte-ads word-ad)))
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads))))

(defthm disjoint-of-two-word-ad-to-byte-ads
  (equal (disjoint (word-ad-to-byte-ads ad1)
                   (word-ad-to-byte-ads ad2))
         (not (equal (ifix ad1) (ifix ad2))))
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads))))

(defthm logext-list-32-of-word-ad-to-byte-ads
  (equal (logext-list 32 (word-ad-to-byte-ads word-ad))
         (word-ad-to-byte-ads (logext 31 word-ad)))
  :hints (("Goal" :in-theory (enable logext-list word-ad-to-byte-ads))))

(defthm disjoint-of-WORD-AD-TO-BYTE-ADS
  (implies (integer-listp x)
           (equal (DISJOINT X (WORD-AD-TO-BYTE-ADS a))
                  (not (memberp (ifix a) (logcdr-list x)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable WORD-AD-TO-BYTE-ADS))))

(defthm cdr-cdr-word-ad-to-byte-ads
  (equal (cdr (cdr (word-ad-to-byte-ads word-ad)))
         nil)
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads))))

(defthm unique-of-word-ad-to-byte-ads
  (bag::unique (word-ad-to-byte-ads word-ad))
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads
                                     acl2::equal-to-ash-1-rewrite))))
;misc:


(defthm loghead-list-of-offset-range-wrap
  (equal (loghead-list '16 (offset-range-wrap 16 base size))
         (offset-range-wrap 16 base size))
  :hints (("Goal" :in-theory (enable loghead-list offset-range-wrap))))

;;
;; syntactic stuff
;;



;Offsets look like this:
; (BINARY-+ '1 (NTH '4 ST))
; (BINARY-+ '2 (NTH '3 ST))
(defun offset-has-expected-form (term)
  (declare (type t term))
  (and (equal 3 (len term))
       (SYMBOLP (CAR TERM))
       (equal (symbol-name (car term)) "BINARY-+")
       (quotep (cadr term))
       (let ((nth-call (caddr term)))
         (and (equal 3 (len nth-call))
              (symbolp (car nth-call))
              (equal "NTH" (symbol-name (car nth-call)))
              (symbolp (caddr nth-call))
              (equal "ST" (symbol-name (caddr nth-call)))
              (or (equal (cadr nth-call) ''4)
                  (equal (cadr nth-call) ''3))))))


(defun smaller-offset-term-aux (term1 term2)
  (declare (type t term1 term2)
           (xargs :mode :program))
  (if (and (offset-has-expected-form term1)
           (offset-has-expected-form term2))
      (let ((nth-call1 (caddr term1))
            (nth-call2 (caddr term2)))
        ;stack ones come befores locals ones
        (if (and (equal ''3 (cadr nth-call1))
                 (equal ''4 (cadr nth-call2)))
            t
          (if (and (equal ''3 (cadr nth-call2))
                   (equal ''4 (cadr nth-call1)))
              nil
            ;;we must be dealing with two locals ones or two stack ones,
            ;;so we just compare the offsets numerically
            ;; lexorder is like <=, but what we want is like <, so we use
            ;; the not of the lexorder of the arguments in reverse order
            (not (lexorder (cadr term2) (cadr term1))))))
    (acl2::smaller-term term1 term2)))

;Terms like (NTH '3 ST) don't match the '(BINARY-+ <constant> (NTH '3 ST)) pattern,
;so we forge an equivalent term that matches the pattern.
(defun convert-term-to-plus-form (term)
  (declare (type t term)
           (xargs :mode :program))
  (if (and (equal 3 (len term))
           (symbolp (car term))
           (equal "NTH" (symbol-name (car term)))
           (symbolp (caddr term))
           (equal "ST" (symbol-name (caddr term)))
           (or (equal (cadr term) ''4)
               (equal (cadr term) ''3)))
      `(binary-+ '0 ,term)
    term))

;;(smaller-offset-term '(BINARY-+ '2 (NTH '3 ST)) '(BINARY-+ '2 (NTH '4 ST)))
(defun smaller-offset-term (term1 term2)
  (declare (xargs :mode :program))
  (smaller-offset-term-aux (convert-term-to-plus-form term1) (convert-term-to-plus-form term2)))

;The arguments to this function are terms
(defun smaller-params (denvr1 offset1 denvr2 offset2)
  (declare (xargs :mode :program))
  (if (acl2::smaller-term denvr1 denvr2)
      t
    (if (acl2::smaller-term denvr2 denvr1)
        nil
      (smaller-offset-term offset1 offset2))))


;;
;; NTHWORD (where should this go?)
;;

(defund nthword (n value)
  (if (zp n)
      (loghead 16 value)
    (nthword (+ -1 n) (logtail 16 value))))

(defthm nthword-of-0
  (equal (nthword 0 value)
         (loghead 16 value))
  :hints (("Goal" :in-theory (enable nthword))))

(defthmd nthword-rewrite
  (implies (natp n)
           (equal (nthword n x)
                  (loghead 16 (logtail (* 16 n) x))))
  :hints (("Goal" :in-theory (enable nthword))))

;loops with LOGTAIL-16-LOGHEAD-32
(defthmd nthword-constant-opener
  (equal (nthword n value)
         (if (zp n)
             (loghead 16 value)
             (nthword (+ -1 n)
                            (logtail 16 value))))
  :hints (("Goal" :in-theory (enable nthword))))

;gen to any size >= 16
(defthm usb16-nthword
  (unsigned-byte-p 16 (nthword n value))
  :hints (("Goal" :in-theory (enable nthword))) )

;gen
(defthm nthword-1-of-logapp
  (equal (nthword 1 (logapp 16 x y))
         (nthword 0 y))
  :hints (("Goal" :in-theory (e/d (nthword-constant-opener) (;logtail-16-loghead-32
                                                             )))))

(defthm logapp-nthword-self-hack
  (equal (logapp 16 x (nthword 1 x))
         (loghead 32 x))
  :hints (("Goal" :in-theory (e/d (nthword-constant-opener) (;logtail-16-loghead-32
                                                             )))))


;;
;; READ-DATA-WORD
;;

;bzo don't mention aamp?
(defun aamp-ramp (ram)
  (declare (type t ram))
  (and (ramp ram)
       (equal (mem::size ram) (expt 2 32))))

;; For execution only.
;; bzo still makes fixnums to pass into RD.
;; Inline the call to acl2::logext-31-exec?
;bzo denv is now a 15 bit quantity in the stobj...
(defund read-data-word-exec (denvr offset ram)
  (declare (type (unsigned-byte 15) denvr)
           (type (unsigned-byte 16) offset)
           (xargs :guard (aamp-ramp ram)
                  :guard-hints (("Goal" :in-theory (enable unsigned-byte-p (:executable-counterpart expt) ;yuck?
                                                           ))))
           )
  (the-usb 16 (let ((word-ad (the (unsigned-byte 31) (+ offset (the-usb 31 (* 65536 denvr)))))) ;Bbzo loghead 15 okay?
                (declare (type (unsigned-byte 31) word-ad))
                (let ;((ad0 (the-sb 32 (ash (the-sb 31 (acl2::logext-31-exec word-ad)) 1))))
                    ((ad0 (the-usb 32 (ash word-ad 1))))
;                  (declare (type (signed-byte 32) ad0)) ;ad0 is a byte address
                  (declare (type (unsigned-byte 32) ad0)) ;ad0 is a byte address
                  (let ;((ad1 (the-sb 32 (+ 1 ad0)))) ;ad1 is a byte address
                      ((ad1 (the-usb 32 (+ 1 ad0)))) ;ad1 is a byte address
                    ;(declare (type (signed-byte 32) ad1))
                    (declare (type (unsigned-byte 32) ad1))
                    (the-usb 16
                             (+ (the-usb 8 (rd ad0 ram))
                                (the-usb 16 (* 256 (the-usb 8 (rd ad1 ram)))))))))))

;I'm intending to leave this open in this file
;logext 15 of denv?
(defun addresses-of-data-word (denvr offset)
  (word-ad-to-byte-ads (logapp 16
                               offset
                               (loghead 15 denvr) ;;(logext 15 denvr) ;bzo drop this?
                               )))

;; Read the 2-byte word of data at offset OFFSET in data environment DENVR in
;; RAM.  The byte at the lower address goes into the least significant bits of
;; the result.
;;
(defund read-data-word (denvr offset ram)
  (declare (type (unsigned-byte 15) denvr)
           (type (unsigned-byte 16) offset)
           (xargs :guard (aamp-ramp ram)
                  :guard-hints (("Goal" :in-theory (e/d (acl2::logext-logapp
                                                         read-data-word-exec
                                                         acl2::ash-as-logapp
                                                         word-ad-to-byte-ads
                                                         acl2::sum-with-shift-becomes-logapp-constant-version)
                                                        (acl2::logapp-0-part-2-better))))))
  (mbe :exec (read-data-word-exec denvr offset ram)
       :logic (wintlist (rd-list (addresses-of-data-word denvr offset)
                                 ram))))

;bzo rewrite and/or linear rules too?
(defthm read-data-word-non-negative-integerp-type
  (and (<= 0 (read-data-word denvr offset ram))
       (integerp (read-data-word denvr offset ram)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable read-data-word))))

;our rule is better:
(in-theory (disable (:type-prescription read-data-word)))

(defthmd usb16-of-read-data-word
  (unsigned-byte-p 16 (read-data-word denvr offset ram))
  :hints (("Goal" :in-theory (enable read-data-word))))

(defthm unsigned-byte-p-of-read-data-word
  (implies (<= 16 n)
           (equal (unsigned-byte-p n (read-data-word denvr offset ram))
                  (integerp n)))
  :hints (("Goal" :use (:instance usb16-of-read-data-word)
           :in-theory (disable usb16-of-read-data-word))))

(defthm usb16-of-read-data-word-fw
  (unsigned-byte-p 16 (read-data-word denvr offset ram))
  :rule-classes ((:forward-chaining :trigger-terms ((read-data-word denvr offset ram)))))

(defthm read-data-word-of-loghead15
  (equal (read-data-word (loghead 15 denvr) offset ram)
         (read-data-word denvr offset ram))
  :hints (("Goal" :in-theory (enable read-data-word
                                     ACL2::LOGEXT-LOGAPP
                                     WORD-AD-TO-BYTE-ADS))))

(defthm read-data-word-when-offset-is-not-an-integerp
  (implies (not (integerp offset))
           (equal (read-data-word denvr offset ram)
                  (read-data-word denvr 0 ram)))
  :hints (("Goal" :in-theory (enable read-data-word))))

(defthm read-data-word-of-loghead16-2
  (equal (read-data-word denvr (loghead 16 offset) ram)
         (read-data-word denvr offset ram))
  :hints (("Goal" :in-theory (enable read-data-word))))

(defthm read-data-word-subst-alt
  (implies (and (equal (loghead 16 offset1) offset2)
                (syntaxp (and (term-order offset2 offset1)
                              (not (equal offset1 offset2))))
                )
           (equal (read-data-word denvr offset1 ram)
                  (read-data-word denvr offset2 ram))))

(defthm read-data-word-subst
  (implies (and (equal (loghead 16 offset1) (loghead 16 offset2))
                (syntaxp (and (term-order offset2 offset1)
                              (not (equal offset1 offset2))))
                )
           (equal (read-data-word denvr offset1 ram)
                  (read-data-word denvr offset2 ram)))
  :hints (("Goal" :use ((:instance read-data-word-of-loghead16-2 (offset offset1))
                        (:instance read-data-word-of-loghead16-2 (offset offset2)))
           :in-theory (disable read-data-word-of-loghead16-2))))

;bzo bad name
(defthm read-data-word-of-sum-normalize-constant
  (implies (and (syntaxp (quotep k))
                (not (acl2::unsigned-byte-p 16 k))
                )
           (equal (read-data-word denvr k ram)
                  (read-data-word denvr (acl2::loghead 16 k) ram)))
  :hints (("Goal" :in-theory (disable read-data-word-of-loghead16-2)
           :use ((:instance read-data-word-of-loghead16-2 (offset (acl2::loghead 16 k)))
                 (:instance read-data-word-of-loghead16-2 (offset k))))))

(defthm read-data-word-subst-denv
  (implies (and (equal (loghead 15 denvr1)
                       (loghead 15 denvr2))
                (syntaxp (and (term-order denvr2 denvr1)
                              (not (equal denvr1 denvr2)))))
           (equal (read-data-word denvr1 offset ram)
                  (read-data-word denvr2 offset ram)))
  :hints
  (("Goal" :use ((:instance read-data-word-of-loghead15
                            (denvr denvr1))
                 (:instance read-data-word-of-loghead15
                            (denvr denvr2)))
    :in-theory (disable read-data-word-of-loghead15))))


(defthm read-data-word-of-sum-of-loghead
  (implies (integerp offset2)
           (equal (read-data-word denvr (+ offset1 (loghead 16 offset2)) ram)
                  (read-data-word denvr (+ offset1 offset2) ram)))
  :hints (("Goal" :use ((:instance read-data-word-of-loghead16-2 (offset  (+ offset1 (loghead 16 offset2))))
                        (:instance read-data-word-of-loghead16-2 (offset  (+ offset1 offset2))))
           :in-theory (disable read-data-word-of-loghead16-2))))

(defthm read-data-word-of-sum-of-loghead-alt
  (implies (integerp offset2)
           (equal (read-data-word denvr (+ (loghead 16 offset2) offset1) ram)
                  (read-data-word denvr (+ offset1 offset2) ram)))
  :hints (("Goal" :use (:instance read-data-word-of-sum-of-loghead)
           :in-theory (disable read-data-word-of-sum-of-loghead))))

;;
;; WRITE-DATA-WORD
;;


;; For execution only.
;bzo speed this up?

(defund write-data-word-exec (denvr offset value ram)
  (declare; (type t ram)
           (type integer denvr offset value)
           (xargs :guard (aamp-ramp ram)
                  :guard-hints (("Goal" :in-theory (enable ash)))
                  )
           )
  (let* ((word-ad (logapp 16 offset denvr))
;;         (ad0 (acl2::logext 32 (ash word-ad 1))) ;ad0 is a byte address
         (ad0 (acl2::loghead 32 (ash word-ad 1))) ;ad0 is a byte address
         (ad1 (+ 1 ad0)) ;ad1 is a byte address
         (byte0 (loghead 8 value))
         (byte1 (loghead 8 (logtail 8 value)))
         )
    (wr ad0 byte0
        (wr ad1 byte1 ram))))


;; Write the 2-byte word VALUE into RAM at offset OFFSET in data environment
;; DENVR in RAM.  The byte at the lower address comes from the least
;; significant bits of VALUE.
;;
(defund write-data-word (denvr offset value ram)
  (declare (type integer denvr offset value)
           (xargs :guard (aamp-ramp ram)
                  :guard-hints (("Goal" :in-theory (enable write-data-word-exec
                                                           ACL2::LOGEXT-LOGAPP)))))
  ;;  (wx 16 (ash (makeaddr denvr offset) 1) value ram)
  (mbe :exec (write-data-word-exec denvr offset value ram)
       :logic (wr-list (addresses-of-data-word denvr offset)
                       (enlistw 2 value)
                       ram)))

(defthm write-data-word-of-write-data-word-same-simple
  (equal (write-data-word denvr offset val1 (write-data-word denvr offset val2 ram))
         (write-data-word denvr offset val1 ram))
  :hints (("Goal" :in-theory (enable write-data-word))))

;trying disabled, since the offsets should get normalized...
(defthmd write-data-word-of-write-data-word-same-offs
  (implies (equal (loghead 16 offset1) (loghead 16 offset2))
           (equal (write-data-word denvr offset1 val1 (write-data-word denvr offset2 val2 ram))
                  (write-data-word denvr offset1 val1 ram)))
  :hints (("Goal" :in-theory (enable write-data-word))))

;; (defthm write-data-word-of-write-data-word-diff-offs
;;   (implies (and (syntaxp (smaller-params denvr2 offset2 denvr1 offset1))
;;                 (not (equal (loghead 16 offset1) (loghead 16 offset2))))
;;            (equal (write-data-word denvr1 offset1 val1 (write-data-word denvr2 offset2 val2 ram))
;;                   (write-data-word denvr2 offset2 val2 (write-data-word denvr1 offset1 val1 ram))))
;;   :rule-classes ((:rewrite :loop-stopper nil))
;;   :hints (("Goal" :in-theory (enable write-data-word))))

;; (defthm write-data-word-of-write-data-word-same-denv-both
;;   (implies (syntaxp (smaller-offset-term offset2 offset1))
;;            (equal (write-data-word denvr offset1 val1 (write-data-word denvr offset2 val2 ram))
;;                   (if (equal (loghead 16 offset1) (loghead 16 offset2))
;;                       (write-data-word denvr offset1 val1 ram)
;;                     (write-data-word denvr offset2 val2 (write-data-word denvr offset1 val1 ram)))))
;;   :rule-classes ((:rewrite :loop-stopper nil))
;;     :hints (("Goal" :in-theory (enable write-data-word))))

;; (defthm write-data-word-of-write-data-word-diff-denvrs
;;   (implies (not (equal (loghead 15 denvr1) (loghead 15 denvr2)))
;;            (equal (write-data-word denvr1 offset1 val1 (write-data-word denvr2 offset2 val2 ram))
;;                   (write-data-word denvr2 offset2 val2 (write-data-word denvr1 offset1 val1 ram))))
;;   :rule-classes ((:rewrite :loop-stopper ((denvr1 denvr2))))
;;   :hints (("Goal" :in-theory (enable write-data-word))))

(defthm write-data-word-of-write-data-word-both
  (implies (syntaxp (smaller-params denvr2 offset2
                                    denvr1 offset1))
           (equal (write-data-word denvr1 offset1 val1 (write-data-word denvr2 offset2 val2 ram))
                  (if (and (equal (loghead 15 denvr1)
                                  (loghead 15 denvr2))
                           (equal (loghead 16 offset1)
                                  (loghead 16 offset2)))
                      (write-data-word denvr1 offset1 val1 ram)
                    (write-data-word denvr2 offset2 val2 (write-data-word denvr1 offset1 val1 ram)))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (e/d (write-data-word) (disjoint-of-two-word-ad-to-byte-ads)))))

;improve?
(defthm write-data-word-of-write-data-word-diff-bag-phrasing
  (implies (and (syntaxp (smaller-params denvr2 offset2 denvr1 offset1)) ;we sort using a complicated scheme.
                (bag::disjoint (addresses-of-data-word denvr1 offset1)
                               (addresses-of-data-word denvr2 offset2)))
           (equal (write-data-word denvr1 offset1 val1 (write-data-word denvr2 offset2 val2 ram))
                  (write-data-word denvr2 offset2 val2 (write-data-word denvr1 offset1 val1 ram))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (e/d (write-data-word) (disjoint-of-two-word-ad-to-byte-ads)))))

(defthm write-data-word-replace-denv
  (implies (and (equal (loghead 15 denvr1)
                       (loghead 15 denvr2))
                (syntaxp (acl2::smaller-term denvr2 denvr1)))
           (equal (write-data-word denvr1 offset value ram)
                  (write-data-word denvr2 offset value ram)))
  :hints (("Goal" :in-theory (enable write-data-word))))

(defthm write-data-word-of-loghead
  (equal (write-data-word denvr offset (loghead 16 value) ram)
         (write-data-word denvr offset value ram))
  :hints (("Goal" :in-theory (enable write-data-word))))

(defthm write-data-word-of-loghead-16
  (equal (write-data-word denvr (loghead 16 offset) value ram)
         (write-data-word denvr offset value ram))
  :hints (("Goal" :in-theory (enable write-data-word))))


(defthm write-data-word-of-logext-16
  (equal (write-data-word denvr (acl2::logext 16 offset) value ram)
         (write-data-word denvr offset value ram))
  :hints (("Goal" :in-theory (enable write-data-word WORD-AD-TO-BYTE-ADS))))

(defthm write-data-word-subst-in-offset-alt
  (implies (and (equal (loghead 16 free) (loghead 16 offset))
                (syntaxp (acl2::smaller-term free offset))
                )
           (equal (write-data-word denvr offset value ram)
                  (write-data-word denvr free value ram)))
  :hints (("Goal" :in-theory (e/d (write-data-word) ()))))

(defthm write-data-word-of-write-data-word-same-val
  (implies (syntaxp (smaller-params denvr2 offset2
                                    denvr1 offset1))
           (equal (write-data-word denvr1 offset1 val (write-data-word denvr2 offset2 val ram))
                  (write-data-word denvr2 offset2 val (write-data-word denvr1 offset1 val ram))))
  :rule-classes ((:rewrite :loop-stopper nil)))


;; ;bzo gen
;; (defthm write-data-word-of-sum-of-loghead
;;   (implies (integerp offset)
;;            (equal (write-data-word denvr (+ 1 (loghead 16 offset)) val ram)
;;                   (write-data-word denvr (+ 1 offset) val ram)))
;;   :hints (("Goal" :in-theory (enable write-data-word))))


(defthm write-data-word-of-sum-of-loghead
  (implies (and (integerp x)
                (integerp a)
                )
           (equal (write-data-word denvr (+ a (loghead 16 x)) val ram)
                  (write-data-word denvr (+ a x) val ram)
                  ))
  :hints (("Goal" :in-theory (enable write-data-word))))

(defthm write-data-word-of-sum-normalize-constant
  (implies (and (syntaxp (quotep k))
                (not (unsigned-byte-p 16 k))
                (integerp k)
                (integerp offset)
                )
           (equal (write-data-word denvr (+ k offset) value ram)
                  (write-data-word denvr (+ (loghead 16 k) offset) value ram)))
  :hints (("Goal" :use ((:instance write-data-word-of-loghead-16 (offset (+ k offset)))
                        (:instance write-data-word-of-loghead-16 (offset (+ (loghead 16 k) offset))))
           :in-theory (e/d () (write-data-word-of-loghead-16
                               ;write-data-word-equal-rewrite
                               )))))

;bzo prove WRITE-DATA-WORD-WITH-VALUE-OUT-OF-BOUNDS from WRITE-DATA-WORD-OF-LOGHEAD?
;analogue for write-data-words?
(defthm write-data-word-of-sum-normalize-constant-addend-in-value
  (implies (and (syntaxp (quotep k))
                (not (unsigned-byte-p 16 k))
                (integerp k)
                (integerp offset)
                )
           (equal (write-data-word denvr offset (+ k value) ram)
                  (write-data-word denvr offset (+ (loghead 16 k) value) ram)))
  :hints (("Goal" :use ((:instance WRITE-DATA-WORD-of-loghead
                                   (denvr denvr)
                                   (offset offset)
                                   (ram ram)
                                   (value (+ (loghead 16 k) value)))
                        (:instance WRITE-DATA-WORD-of-loghead
                                   (denvr denvr)
                                   (offset offset)
                                   (ram ram)
                                   (value (+ k value))))
           :in-theory (e/d () (WRITE-DATA-WORD-of-loghead
                               ;write-data-word-equal-rewrite
                               )))))

;zzz


;move?
(defthm helper-for-subst-denv
  (implies (and (equal (loghead 15 denvr1)
                       (loghead 15 denvr2))
                (syntaxp (acl2::smaller-term denvr2 denvr1)))
           (equal (logext-list 32 (word-ad-to-byte-ads (logapp 16 offset denvr1)))
                  (logext-list 32 (word-ad-to-byte-ads (logapp 16 offset denvr2)))))
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads))))



(defthm write-data-word-with-offset-out-of-bounds
  (implies (and (syntaxp (quotep offset))
                (not (acl2::unsigned-byte-p 16 offset)))
           (equal (write-data-word denvr offset value ram)
                  (write-data-word denvr (acl2::loghead 16 offset) value ram))))

;make a non syntaxp version
(defthm write-data-word-with-value-out-of-bounds
  (implies (and (syntaxp (quotep value))
                (not (acl2::unsigned-byte-p 16 value)))
           (equal (write-data-word denvr offset value ram)
                  (write-data-word denvr offset (acl2::loghead 16 value) ram)))
  :hints (("Goal" :in-theory (enable write-data-word word-ad-to-byte-ads))))

(defthm write-data-word-when-offset-is-not-an-integerp
  (implies (not (integerp offset))
           (equal (write-data-word denvr offset value ram)
                  (write-data-word denvr 0 value ram)))
  :hints (("Goal" :in-theory (enable write-data-word))))

(defthm write-data-word-subst-in-sum-offset
  (implies (and (equal (loghead 16 off2) free)
                (syntaxp (acl2::smaller-term free off2))
                (integerp off2)
                (integerp off1)
                )
           (equal (write-data-word denvr (+ off1 off2) value ram)
                  (write-data-word denvr (+ off1 free) value ram))))




;;
;; Theorems about the single word ops.
;;

;Can these "already" there rules cause problems?  (I've seen a case with two
;nests of clear that were hard to normalize to the same thing, and I think the
;problem arose because of an "already-there" rule).  Maybe the "write equal
;rewrite" rules should be sufficient?

(defthm write-data-word-of-what-was-already-there-weak
  (equal (write-data-word denvr offset (read-data-word denvr offset ram) ram)
         ram)
  :hints (("Goal" :in-theory (enable acl2::logext-logapp write-data-word read-data-word))))

;too expensive?
(defthm write-data-word-of-what-was-already-there-strong
  (implies (equal val (read-data-word denvr offset ram))
           (equal (write-data-word denvr offset val ram)
                  ram)))

;; Can cause case splits; perhaps keep it turned off until the simulation is done?
;; If so, maybe non-case splitting versions of the -diff rules are needed?
(defthm read-data-word-of-write-data-word-all-cases
  (equal (read-data-word denvr1 offset1 (write-data-word denvr2 offset2 val ram))
         (if (and (equal (loghead 16 offset1) (loghead 16 offset2))
                  (equal (loghead 15 denvr1) (loghead 15 denvr2)))
             (loghead 16 val)
           (read-data-word denvr1 offset1 ram)))
  :hints (("Goal" :in-theory
           (enable read-data-word write-data-word))))

;Subsumed by read-data-word-of-write-data-word-all-cases, but this should be a "simple" rule.
(defthm read-data-word-of-write-data-word-same-simple
  (equal (read-data-word denvr offset (write-data-word denvr offset val ram))
         (loghead 16 val)))

(defthmd read-data-word-of-write-data-word-diff-bag-phrasing
  (implies (bag::disjoint (addresses-of-data-word denvr1 offset1)
                          (addresses-of-data-word denvr2 offset2))
           (equal (read-data-word denvr1 offset1 (write-data-word denvr2 offset2 val ram))
                  (read-data-word denvr1 offset1 ram)))
  :hints (("Goal" :in-theory (enable read-data-word write-data-word))))

;;
;; CLEAR-DATA-WORD
;;

;bzo add guard?
(defund clear-data-word (denvr offset ram1)
  (write-data-word denvr offset 0 ram1))

;see theorems about wr-bytes and copy them?

(defthm write-data-word-equal-rewrite
  (equal (equal (write-data-word denvr offset value ram1) ram2)
         (and (equal (loghead 16 value) (read-data-word denvr offset ram2))
              (equal (clear-data-word denvr offset ram1)
                     (clear-data-word denvr offset ram2))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (WRITE-DATA-WORD READ-DATA-WORD
                                                   WORD-AD-TO-BYTE-ADS
                                                   ACL2::EQUAL-LOGAPP-X-Y-Z
                                                   WR==R!
                                                   clear-data-word
                                                   )
                                  ()))))

(defthm read-data-word-of-clear-data-word-both
  (equal (read-data-word denvr1 offset1 (clear-data-word denvr2 offset2 ram))
         (if (and (equal (loghead 16 offset1) (loghead 16 offset2))
                  (equal (loghead 15 denvr1) (loghead 15 denvr2)))
             0
           (read-data-word denvr1 offset1 ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-word) (write-data-word-equal-rewrite)))))

;Subsumed by read-data-word-of-clear-data-word-both, but this should be a "simple" rule.
(defthm read-data-word-of-clear-data-word-same-simple
  (equal (read-data-word denvr offset (clear-data-word denvr offset ram))
         0))

;use the bag phrasing on the -both lemmas?
(defthmd read-data-word-of-clear-data-word-diff-bag-phrasing
  (implies (bag::disjoint (addresses-of-data-word denvr1 offset1)
                          (addresses-of-data-word denvr2 offset2))
           (equal (read-data-word denvr1 offset1 (clear-data-word denvr2 offset2 ram))
                  (read-data-word denvr1 offset1 ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-word) (write-data-word-equal-rewrite)))))

(defthm clear-data-word-of-clear-data-word-same-simple
  (equal (clear-data-word denvr offset (clear-data-word denvr offset ram))
         (clear-data-word denvr offset ram))
  :hints (("Goal" :in-theory (e/d (clear-data-word) (write-data-word-equal-rewrite)))))

; ===




;; (defthm clear-data-word-of-write-data-word-diff-denvrs
;;   (implies (not (equal (loghead 15 denvr1) (loghead 15 denvr2)))
;;            (equal (clear-data-word denvr1 offset1 (write-data-word denvr2 offset2 value ram))
;;                   (write-data-word denvr2 offset2 value (clear-data-word denvr1 offset1 ram))))
;;   :hints (("Goal" :in-theory (e/d (clear-data-word
;;                                    acl2::logext-logapp)
;;                                   (write-data-word-equal-rewrite)))))


;; (defthm clear-data-word-of-write-data-word-diff-offsets
;;   (implies (not (equal (loghead 16 offset1)
;;                        (loghead 16 offset2)))
;;            (equal (clear-data-word denvr1 offset1 (write-data-word denvr2 offset2 value ram))
;;                   (write-data-word denvr2 offset2 value (clear-data-word denvr1 offset1 ram))))
;;   :hints (("Goal" :in-theory (e/d (
;;                                    clear-data-word
;;                                    acl2::logext-logapp)
;;                                   (write-data-word-equal-rewrite)))))

(defthm clear-data-word-subst-in-offset
  (implies (and (equal (loghead 16 offset) free)
                (syntaxp (acl2::smaller-term free offset))
                )
           (equal (clear-data-word denvr offset ram)
                  (clear-data-word denvr free ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-word) (WRITE-DATA-WORD-EQUAL-REWRITE)))))

(defthm clear-data-word-of-write-data-word-same-simple
  (equal (clear-data-word denvr offset (write-data-word denvr offset value ram))
         (clear-data-word denvr offset ram))
  :hints (("Goal" :in-theory (e/d (clear-data-word) (write-data-word-equal-rewrite)))))

(defthm clear-data-word-of-write-data-word-all-cases
  (equal (clear-data-word denvr1 offset1 (write-data-word denvr2 offset2 val ram))
         (if (and (equal (loghead 15 denvr1) (loghead 15 denvr2))
                  (equal (loghead 16 offset1) (loghead 16 offset2)))
             (clear-data-word denvr1 offset1 ram)
           (write-data-word denvr2 offset2 val (clear-data-word denvr1 offset1 ram))))
  :hints (("Goal" :in-theory (e/d (clear-data-word
                                   acl2::logext-logapp)
                                  (write-data-word-equal-rewrite)))))

(defthm write-data-word-subst-in-offset
  (implies (and (equal free (loghead 16 offset))
                (syntaxp (acl2::smaller-term free offset))
                )
           (equal (write-data-word denvr offset value ram)
                  (write-data-word denvr free value ram)))
  :hints (("Goal" :in-theory (e/d (write-data-word) (WRITE-DATA-WORD-EQUAL-REWRITE)))))

(defthm clear-data-word-of-sum-of-loghead
  (implies (and (integerp x)
                (integerp a)
                )
           (equal (clear-data-word denvr (+ a (loghead 16 x)) ram)
                  (clear-data-word denvr (+ a x) ram)
                  ))
  :hints (("Goal" :in-theory (e/d (clear-data-word) (WRITE-DATA-WORD-EQUAL-REWRITE)))))

(defthm clear-data-word-of-loghead-16
  (equal (clear-data-word denvr (loghead 16 offset) ram)
         (clear-data-word denvr offset ram))
  :hints (("Goal" :in-theory (e/d (clear-data-word) (WRITE-DATA-WORD-EQUAL-REWRITE)))))

(defthm clear-data-word-of-sum-normalize-constant
  (implies (and (syntaxp (quotep k))
                (integerp k)
                (integerp offset)
                (not (unsigned-byte-p 16 k)))
           (equal (clear-data-word denvr (+ k offset) ram)
                  (clear-data-word denvr (+ (loghead 16 k) offset) ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-word) (WRITE-DATA-WORD-EQUAL-REWRITE)))))

(defthm clear-data-word-when-already-zero
  (implies (equal (read-data-word denvr offset ram) 0)
           (equal (clear-data-word denvr offset ram)
                  ram))
  :hints (("Goal" :in-theory (e/d (clear-data-word
                                   write-data-word-of-what-was-already-there-strong)
                                  (write-data-word-equal-rewrite)))))

(defthm clear-data-word-when-already-zero-cheap
  (implies (equal (read-data-word denvr offset ram) 0)
           (equal (clear-data-word denvr offset ram)
                  ram))
  :rule-classes ((:rewrite :backchain-limit-lst (1)))
  :hints (("Goal" :in-theory (enable clear-data-word-when-already-zero))))

(defthm clear-data-word-normalize-constant-offset
  (implies (and (syntaxp (quotep offset))
                (not (unsigned-byte-p 16 offset)))
           (equal (clear-data-word denvr offset ram)
                  (clear-data-word denvr (loghead 16 offset) ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-word) (write-data-word-equal-rewrite)))))

(defthm clear-data-word-of-clear-data-word-diff
  (implies (syntaxp (smaller-params denvr2 offset2
                                    denvr1 offset1))
           (equal (clear-data-word denvr1 offset1 (clear-data-word denvr2 offset2 ram))
                  (clear-data-word denvr2 offset2 (clear-data-word denvr1 offset1 ram))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (e/d (clear-data-word) (write-data-word-equal-rewrite)))))

;dup with unforced?
;analogue for write?
(defthm clear-data-word-loghead
  (implies (and (force (integerp n))
                (force (integerp a))
                (force (integerp b)))
           (equal (clear-data-word denvr (+ a (loghead 16 (+ b n))) ram)
                  (clear-data-word denvr (+ a b n) ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-word) (write-data-word-equal-rewrite)))))




;;
;;
;; Multi-word operations
;;
;;



;;
;; WORD-ADS-TO-BYTE-ADS
;;

;;word-ads-to-byte-ads implicitly takes word-aligned input...
;; Convert a list of word addresses to a list of twice the length, containing
;; their corresponding byte addresses
;;

(defun word-ads-to-byte-ads (word-ads)
  (declare (xargs :guard (integer-listp word-ads)))
  (if (consp word-ads)
      (append (word-ad-to-byte-ads (car word-ads)) (word-ads-to-byte-ads (cdr word-ads)))
    nil))

(defthm integer-listp-of-word-ads-to-byte-ads
  (implies (integer-listp word-ads)
           (integer-listp (word-ads-to-byte-ads word-ads)))
  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads))))

(defthm word-ads-to-byte-ads-of-cons
  (equal (word-ads-to-byte-ads (cons ad word-ads))
         (append (word-ad-to-byte-ads ad) (word-ads-to-byte-ads word-ads)))
  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads))))

(defthm word-ads-to-byte-ads-of-append
  (equal (gacc::word-ads-to-byte-ads (append x y))
         (append (gacc::word-ads-to-byte-ads x)
                 (gacc::word-ads-to-byte-ads y))))

(defthm consp-of-word-ads-to-byte-ads
  (equal (consp (word-ads-to-byte-ads word-ads))
         (consp word-ads))
  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads))))

(defthm word-ads-to-byte-ads-iff
  (iff (gacc::word-ads-to-byte-ads gacc::word-ads)
       (consp gacc::word-ads))
  :hints (("Goal" :in-theory (enable gacc::word-ads-to-byte-ads))))

(defthm car-of-word-ads-to-byte-ads
  (equal (car (word-ads-to-byte-ads word-ads))
         (if (consp word-ads)
             (car (word-ad-to-byte-ads (car word-ads)))
           nil))
  :hints (("Goal" :expand (word-ads-to-byte-ads word-ads)
           :in-theory (enable word-ads-to-byte-ads))))

(defthm cdr-of-word-ads-to-byte-ads
  (equal (cdr (word-ads-to-byte-ads word-ads))
         (if (consp word-ads)
             (cons (cadr (word-ad-to-byte-ads (car word-ads)))
                   (word-ads-to-byte-ads (cdr word-ads)))
           nil))
  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads
                                     word-ad-to-byte-ads))))

(defthm len-of-word-ads-to-byte-ads
  (equal (len (word-ads-to-byte-ads word-ads))
         (* 2 (len word-ads)))
  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads))))

(defthm word-ads-to-byte-ads-when-word-ads-is-not-a-consp
  (implies (not (consp word-ads))
           (equal (word-ads-to-byte-ads word-ads)
                  nil))
  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads))))

(defthmd loghead-list-of-word-ads-to-byte-ads-hack
  (equal (loghead-list 32 (word-ads-to-byte-ads word-ads))
         (word-ads-to-byte-ads (loghead-list 31 word-ads)))
  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads word-ad-to-byte-ads))))

(defthm memberp-of-logapp-and-word-ads-to-byte-ads
  (implies (integer-listp word-ads)
           (equal (list::memberp (logapp 17 (logapp 1 b offset) denvr) (word-ads-to-byte-ads word-ads))
                  (list::memberp (logapp 16 offset denvr) word-ads)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable word-ads-to-byte-ads WORD-AD-TO-BYTE-ADS ACL2::EQUAL-LOGAPP-X-Y-Z))))

(defthm memberp-of-word-ads-to-byte-ads
  (equal (memberp ad (word-ads-to-byte-ads ads))
         (and (integerp ad)
              (memberp (acl2::logcdr ad) (ifix-list ads))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (word-ads-to-byte-ads) ()))))

(defthm word-ads-to-byte-ads-of-loghead-list
  (implies (and (integerp size)
                (<= 0 size))
           (equal (word-ads-to-byte-ads (loghead-list size ads))
                  (loghead-list (+ 1 size) (word-ads-to-byte-ads ads))))
  :hints (("Goal" :in-theory (enable word-ad-to-byte-ads
                                     word-ads-to-byte-ads))))

(theory-invariant (incompatible (:rewrite loghead-list-of-word-ads-to-byte-ads-hack)
                                (:rewrite word-ads-to-byte-ads-of-loghead-list)))

(defthm logext-list-32-of-word-ads-to-byte-ads
  (equal (logext-list 32 (word-ads-to-byte-ads word-ads))
         (word-ads-to-byte-ads (logext-list 31 word-ads)))
  :hints (("Goal" :in-theory (enable logext-list word-ads-to-byte-ads))))

(defthm disjoint-of-word-ad-to-byte-ads-and-word-ads-to-byte-ads
  (equal (disjoint (word-ad-to-byte-ads ad)
                   (word-ads-to-byte-ads word-ads))
         (not (bag::memberp (ifix ad) (ifix-list word-ads))))
  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads))))

(defthm disjoint-of-two-calls-to-word-ads-to-byte-ads
  (equal (disjoint (word-ads-to-byte-ads word-ads1) (word-ads-to-byte-ads word-ads2))
         (or (endp word-ads1)
             (endp word-ads2)
             (disjoint (ifix-list word-ads1) (ifix-list word-ads2))
             ))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable word-ads-to-byte-ads))))

(defthm count-in-word-ads-to-byte-ads
  (implies (integer-listp ads) ;bzo
           (equal (bag::count bag::arbitrary-element (word-ads-to-byte-ads ads))
                  (if (integerp bag::arbitrary-element)
                      (bag::count (acl2::logcdr bag::arbitrary-element) ads)
                    0)))
  :hints (("Goal" :in-theory (e/d (word-ads-to-byte-ads
                                   acl2::equal-logapp-x-y-z
                                   acl2::ash-as-logapp
                                   word-ad-to-byte-ads)
                                  (acl2::logapp-0-part-2-better)))))



(defthm subbagp-of-word-ads-to-byte-ads-and-word-ads-to-byte-ads
  (implies (and (bag::subbagp ads1 ads2)
                (integer-listp ads1)
                (integer-listp ads2))
           (bag::subbagp (word-ads-to-byte-ads ads1)
                         (word-ads-to-byte-ads ads2)))
  :hints (("Goal" ; :induct (double-cdr-induct ads1 ads2)
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable len word-ads-to-byte-ads))))

;; (implies (bag::unique (loghead-list 16 word-ads))
;;          (bag::unique word-ads))

;drop?
(defthm unique-of-word-ads-to-byte-ads
  (implies (and (bag::unique (loghead-list 16 word-ads))
                (integer-listp word-ads) ;bzo
                )
           (bag::unique (word-ads-to-byte-ads word-ads))))


(defthm unique-of-word-ads-to-byte-ads-better
  (implies (integer-listp word-ads)
           (equal (unique (word-ads-to-byte-ads word-ads))
                  (unique word-ads)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (disable)
           :expand ((unique word-ads)
                    (word-ads-to-byte-ads word-ads)))))

(defthm firstn-of-word-ads-to-byte-ads-helper
  (implies (integerp n)
           (equal (firstn (* 2 n) (word-ads-to-byte-ads word-ads))
                  (word-ads-to-byte-ads (firstn n word-ads))))
  :hints (("Goal" :expand (WORD-ADS-TO-BYTE-ADS (FIRSTN N WORD-ADS))
           :in-theory (enable word-ads-to-byte-ads (:induction firstn)))))

(defthm firstn-of-word-ads-to-byte-ads
  (implies (evenp n)
           (equal (firstn n (word-ads-to-byte-ads word-ads))
                  (word-ads-to-byte-ads (firstn (/ n 2) word-ads))))
  :hints (("Goal" :use (:instance firstn-of-word-ads-to-byte-ads-helper (n (/ n 2)))
           :in-theory (disable firstn-of-word-ads-to-byte-ads-helper))))

(defthm nthcdr-of-word-ads-to-byte-ads-helper
  (implies (integerp n)
           (equal (nthcdr (* 2 n) (word-ads-to-byte-ads word-ads))
                  (word-ads-to-byte-ads (nthcdr n word-ads))))
  :hints (("Goal" :expand (WORD-ADS-TO-BYTE-ADS (NTHCDR N WORD-ADS))
           :in-theory (enable word-ads-to-byte-ads (:induction nthcdr)))))

(defthm nthcdr-of-word-ads-to-byte-ads
  (implies (evenp n)
           (equal (nthcdr n (word-ads-to-byte-ads word-ads))
                  (word-ads-to-byte-ads (nthcdr (/ n 2) word-ads))))
  :hints (("Goal" :use (:instance nthcdr-of-word-ads-to-byte-ads-helper (n (/ n 2)))
           :in-theory (disable nthcdr-of-word-ads-to-byte-ads-helper))))

;;
;; READ-DATA-WORDS
;;

;; For execution only:
;; bzo think more about how to make this fast
;; drop the loghead in (loghead 16 value)?
;put in a case for 1?
;bzo should we restrict numwords to be a fixnum? ask hardin? will mean read-data-words has the same restriction...
(defund read-data-words-exec (numwords denvr offset ram)
  (declare (type (unsigned-byte 15) denvr)
           (type (unsigned-byte 16) offset)
           (type (unsigned-byte 31) numwords) ;trying...;(type (integer 0 *) numwords)
           (xargs :guard (aamp-ramp ram))
           )
  (if (equal 2 numwords) ;any other special cases?
      (let ((word-ad0 (logapp 16 offset denvr)))
        (declare (type (unsigned-byte 31) word-ad0))
        (let ((word-ad1 (logapp 16 (+ 1 offset) denvr)))
          (declare (type (unsigned-byte 31) word-ad1))
          (let ;;((ad0 (the-sb 32 (ash (the-sb 31 (acl2::logext 31 word-ad0)) 1)))) ;ad0 is a byte address
              ((ad0 (the-usb 32 (ash (the-usb 31 (acl2::loghead 31 word-ad0)) 1)))) ;ad0 is a byte address
            ;;(declare (type (signed-byte 32) ad0))
            (declare (type (unsigned-byte 32) ad0))
            (let ((ad1 (+ 1 ad0))) ;;ad1 is a byte address
              (let ;((ad2 (acl2::logext 32 (ash word-ad1 1)))) ;ad2 is a byte address
                  ((ad2 (acl2::loghead 32 (ash word-ad1 1)))) ;ad2 is a byte address
                (let ((ad3 (+ 1 ad2))) ;ad3 is a byte address
                  (logapp 24 (logapp 16 (logapp 8 (rd ad0 ram) (rd ad1 ram)) (rd ad2 ram)) (rd ad3 ram))))))))
    (if (equal 1 numwords)
        (read-data-word-exec denvr offset ram)
      (if (zp numwords)
          0
        (logapp 16
                (read-data-word-exec denvr offset ram)
                (read-data-words-exec (+ -1 numwords) denvr (loghead 16 (+ 1 offset)) ram))))))

;;
;; ADDRESSES-OF-DATA-WORDS
;;

(defun addresses-of-data-words (numwords denvr offset)
  (word-ads-to-byte-ads (logapp-list 16
                                     (offset-range-wrap 16 offset numwords)
                                     (loghead 15 denvr) ;(logext 15 denvr)
                                     )))


(defthm consp-of-addresses-of-data-words
  (equal (consp (gacc::addresses-of-data-words numwords denvr offset))
         (not (zp numwords)))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-words))))


(defund read-data-words (numwords denvr offset ram)
  (declare (type (unsigned-byte 31) numwords) ;trying...;(type (integer 0 *) numwords); (type (integer 0 *) numwords)
           (type (unsigned-byte 15) denvr)
           (type (unsigned-byte 16) offset)
           (xargs  :guard (aamp-ramp ram)
                   :guard-hints (("Goal" :expand  ((offset-range-wrap 16 offset 2)
                                                   (offset-range-wrap 16 offset numwords))
                                  :induct t
                                  :do-not '(generalize eliminate-destructors)
                                  :in-theory (e/d (word-ad-to-byte-ads
                                                   ACL2::SUM-WITH-SHIFT-BECOMES-LOGAPP-CONSTANT-VERSION
                                                   read-data-word-exec
                                                   acl2::logext-logapp
                                                   acl2::ash-as-logapp
                                                   read-data-words-exec)
                                                  (acl2::logapp-0-part-2-better
                                                   acl2::loghead-sum-split-into-2-when-i-is-a-constant))))))
  (mbe :exec (read-data-words-exec numwords denvr offset ram)
       :logic (wintlist (rd-list (addresses-of-data-words numwords denvr offset)
                                 ram))))

;bzo rewrite and/or linear rules too?
(defthm read-data-words-non-negative-integerp-type
  (and (<= 0 (read-data-words numwords denvr offset ram))
       (integerp (read-data-words numwords denvr offset ram)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable read-data-words))))

;our rule is better:
(in-theory (disable (:type-prescription read-data-words)))


(defthm read-data-words-when-numwords-is-non-positive
  (implies (<= numwords 0)
           (equal (read-data-words numwords denvr offset ram)
                  0))
  :hints (("Goal" :in-theory (enable read-data-words))))

(defthm read-data-words-when-numwords-is-not-an-integerp
  (implies (not (integerp numwords))
           (equal (read-data-words numwords denvr offset ram)
                  0))
  :hints (("Goal" :in-theory (enable read-data-words))))

(defthm read-data-words-when-offset-is-not-an-integerp
  (implies (not (integerp offset))
           (equal (read-data-words numwords denvr offset ram)
                  (read-data-words numwords denvr 0 ram)))
  :hints (("Goal" :in-theory (enable read-data-words))))

(defthm read-data-words-when-numwords-is-zp
  (implies (zp numwords)
           (equal (read-data-words numwords denvr offset ram)
                  0))
  :hints (("Goal" :in-theory (enable read-data-words))))

(defthmd read-data-words-opener
  (implies (and (syntaxp (and (quotep numwords)
                              (<= (cadr numwords) 8) ;arbitrary cut-off to prevent acl2 going out to lunch expanding large operations
                              ))
                (not (zp numwords)))
           (equal (read-data-words numwords denvr offset ram)
                  (logapp 16
                          (read-data-word denvr offset ram)
                          (read-data-words (+ -1 numwords)
                                           denvr (+ 1 (ifix offset))
                                           ram))))
  :hints
  (("Goal" :expand ((OFFSET-RANGE-WRAP 16 OFFSET NUMWORDS)
                    (OFFSET-RANGE-WRAP 16 0 NUMWORDS))
    :in-theory
    (e/d (READ-DATA-WORD
          read-data-words
          WORD-AD-TO-BYTE-ADS
          OFFSET-RANGE-WRAP-CONST-OPENER
          ACL2::ASH-AS-LOGAPP
          ACL2::LOGEXT-LOGAPP)
         ( ;makeaddr-of-+-loghead
          ACL2::LOGAPP-0-PART-2-BETTER
          ACL2::LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT
          )))))

(defthmd read-data-words-alt-def
  (equal (read-data-words numwords denvr offset ram)
         (if (zp numwords)
             0
           (logapp 16
                   (read-data-word denvr offset ram)
                   (read-data-words (+ -1 numwords) denvr (+ 1 (ifix offset)) ram))))
  :rule-classes :definition
  :hints (("Goal" :use (:instance read-data-words-opener)
           :in-theory (disable read-data-words-opener))))

(defthm read-data-words-of-1
  (equal (read-data-words 1 denvr offset ram)
         (read-data-word denvr offset ram))
  :hints (("Goal" :in-theory (enable read-data-words-opener))))

(defthm read-data-words-of-loghead-around-denvr
  (equal (read-data-words numwords (loghead 16 denvr) offset ram)
         (read-data-words numwords denvr offset ram))
  :hints (("Goal" :in-theory (enable read-data-words))))

(defthm read-data-words-of-loghead-around-offset
  (equal (read-data-words numwords denvr (loghead 16 offset) ram)
         (read-data-words numwords denvr offset ram))
  :hints (("Goal" :in-theory (enable read-data-words))))

(defthm read-data-words-subst
  (implies (and (equal (loghead 16 offset) (loghead 16 free))
                (syntaxp (acl2::smaller-term free offset))
                (integerp offset)
                (integerp free))
           (equal (read-data-words numwords denvr offset ram)
                  (read-data-words numwords denvr free ram)))
  :hints (("Goal" :in-theory (enable read-data-words))))

(DEFTHM LEN-OF-LOGHEAD-LIST
  (EQUAL (LEN (LOGHEAD-LIST SIZE I-LIST))
         (LEN I-LIST))
  :HINTS (("Goal" :IN-THEORY (ENABLE LOGHEAD-LIST))))

;rewrite too?
(defthm unsigned-byte-p-of-read-data-words
  (implies (acl2::natp numwords)
           (unsigned-byte-p (* 16 numwords) (read-data-words numwords denvr offset ram)))
  :rule-classes ((:forward-chaining :trigger-terms ((read-data-words numwords denvr offset ram))))
  :hints (("Goal" :in-theory (enable read-data-words))))


(defthm unsigned-byte-p-of-read-data-words-gen
  (implies (<= (* 16 numwords) n)
           (equal (unsigned-byte-p n (read-data-words numwords denvr offset ram))
                  (and (integerp n)
                       (<= 0 n))))
  :hints (("Goal" :in-theory (disable unsigned-byte-p-of-read-data-words)
           :use (:instance  unsigned-byte-p-of-read-data-words))))



;;
;;
;; WRITE-DATA-WORDS
;;
;;

;bzo think more about how to make this fast
;drop the loghead in (loghead 16 value)?
(defund write-data-words-exec (numwords denvr offset value ram)
  (declare (type integer denvr offset value)
           (type (integer 0 *) numwords)
           (xargs :guard (aamp-ramp ram)
                  :verify-guards nil ;we do it below
                  )
           )
  (if (zp numwords)
      ram
    (if (equal 2 numwords) ;any other special cases?
        (let* ((word-ad0 (logapp 16 offset denvr))
               (word-ad1 (logapp 16 (+ 1 offset) denvr))
;;               (ad0 (acl2::logext 32 (ash word-ad0 1))) ;ad0 is a byte address
               (ad0 (acl2::loghead 32 (ash word-ad0 1))) ;ad0 is a byte address
               (ad1 (+ 1 ad0)) ;;ad1 is a byte address
;;               (ad2 (acl2::logext 32 (ash word-ad1 1))) ;ad2 is a byte address
               (ad2 (acl2::loghead 32 (ash word-ad1 1))) ;ad2 is a byte address
               (ad3 (+ 1 ad2)) ;ad3 is a byte address
;bzo use masks here?
               (byte0 (loghead 8 value))
               (byte1 (loghead 8 (logtail 8 value)))
               (byte2 (loghead 8 (logtail 16 value)))
               (byte3 (loghead 8 (logtail 24 value)))
               )
          (wr ad0 byte0 (wr ad1 byte1 (wr ad2 byte2 (wr ad3 byte3 ram)))))
      (write-data-word-exec
       denvr offset value ;(loghead 16 value)
       (write-data-words-exec (+ -1 numwords) denvr (+ 1 offset) (logtail 16 value) ram)))))

(defthm memory-p-of-write-data-word-exec
  (implies (mem::memory-p ram)
           (mem::memory-p (write-data-word-exec denvr offset value ram)))
  :hints (("Goal" :in-theory (enable write-data-word-exec))))

(defthm memory-p-of-write-data-words-exec
  (implies (MEM::MEMORY-P ram)
           (MEM::MEMORY-P (write-data-words-exec numwords denvr offset value ram)))
  :hints (("Goal" :in-theory (enable write-data-words-exec))))

(defthm size-of-write-data-word-exec
  (implies (mem::memory-p ram)
           (equal (mem::size (write-data-word-exec denvr offset value ram))
                  (mem::size ram)))
  :hints (("Goal" :in-theory (enable write-data-word-exec))))

(defthm size-of-write-data-words-exec
  (implies (mem::memory-p ram)
           (equal (mem::size (write-data-words-exec numwords denvr offset value ram))
                  (mem::size ram)))
  :hints (("Goal" :in-theory (enable write-data-words-exec))))

(in-theory (disable WORD-AD-TO-BYTE-ADS
                    WORD-ADs-TO-BYTE-ADS
                    write-data-word-exec))

;handle wr-list of append?

;; Write (the low NUMWORDS words of) VALUE at offset OFFSET in data environment DENV in ram RAM.
;order of word-ads-to-byte-ads and append-denv-list?
;we intend to keep this closed up, but we can open it if we have to...
;maybe we don't even need the call to offset-range-wrap, since logapp-list chops its args?
;16 or 15???
;; Wraps around if we reach the end of DENVR.
;; The low-order bits of VALUE go into the lower addresses in DENV (unless wrapping occurs).

(defund write-data-words (numwords denvr offset value ram)
  (declare (type (integer 0 *) numwords)
           (type integer offset value denvr)
           (xargs :guard (aamp-ramp ram)
                  :guard-hints (("Goal" :expand  (offset-range-wrap 16 offset numwords)
                                 :induct t
                                 :do-not '(generalize eliminate-destructors)
                                 :in-theory (e/d (WORD-AD-TO-BYTE-ADS
                                                  OFFSET-RANGE-WRAP-CONST-OPENER
                                                  WRITE-DATA-WORD-EXEC
                                                  ACL2::LOGEXT-LOGAPP
                                                  write-data-words-exec)
                                                 (ACL2::LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT))))))
  (mbe :exec (write-data-words-exec numwords denvr offset value ram)
       :logic (wr-list (addresses-of-data-words numwords denvr offset)
;           (word-list-to-byte-list (split-into-words numwords value))
                       (enlistw (* 2 numwords) value)
                       ram)))

(defthm write-data-words-when-numwords-is-non-positive
  (implies (<= numwords 0)
           (equal (write-data-words numwords denvr offset value ram)
                  ram))
  :hints (("Goal" :in-theory (enable write-data-words))))

(defthm write-data-words-when-numwords-is-not-an-integerp
  (implies (not (integerp numwords))
           (equal (write-data-words numwords denvr offset value ram)
                  ram))
  :hints (("Goal" :in-theory (enable write-data-words))))

(defthm write-data-words-when-numwords-is-zp
  (implies (zp numwords)
           (equal (write-data-words numwords
                                    denvr offset value ram)
                  ram))
  :hints (("Goal" :in-theory (enable write-data-words))))

(defthmd write-data-words-opener
  (implies (and (syntaxp (and (quotep numwords)
                              (<= (cadr numwords) 8) ;arbitrary cut-off to prevent acl2 going out to lunch expanding large operations
                              ))
                (not (zp numwords)))
           (equal (write-data-words numwords denvr offset value ram)
                  (write-data-word denvr offset (loghead 16 value)
                                   (write-data-words (+ -1 numwords) denvr (+ 1 (ifix offset)) (logtail 16 value)
                                                     ram))))
  :hints (("Goal" :expand ((OFFSET-RANGE-WRAP 16 OFFSET NUMWORDS))
           :in-theory (e/d (write-data-words write-data-word
                                             acl2::logext-logapp
                                             WORD-AD-TO-BYTE-ADS)
                           ()))))

(defthmd write-data-words-alt-def
  (equal (write-data-words numwords denvr offset value ram)
         (if (zp numwords)
             ram
           (write-data-word denvr offset
                            (loghead 16 value)
                            (write-data-words (+ -1 numwords)
                                              denvr
                                              (+ 1 (ifix offset))
                                              (logtail 16 value)
                                              ram))))
  :rule-classes :definition
  :hints (("Goal" :use (:instance write-data-words-opener)
           :in-theory (e/d ()
                           (write-data-word-equal-rewrite
                            write-data-words-opener
                            )))))

(defthm write-data-words-of-sum-of-loghead
  (equal (write-data-words numwords denvr (+ i (loghead 16 j)) val ram)
         (write-data-words numwords denvr (+ i (ifix j)) val ram))
  :hints (("Goal" :in-theory (enable write-data-words))))

;; ex: (write-data-words 3 #x0001 #x0001 #xffffffffffff nil)


;; zzz
;; (defthm read-data-words-of-write-data-word-diff-offsets
;;   (implies (and (not (bag::memberp (loghead 16 offset2) (offset-range-wrap offset1 numwords))) ;rephrase?
;;                 (integerp offset1)
;;                 (integerp offset2)
;;                 )
;;            (equal (read-data-words numwords denvr1 offset1 (write-data-word denvr2 offset2 value ram))
;;                   (read-data-words numwords denvr1 offset1 ram)))
;; )

;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :induct t
;;            :in-theory (enable read-data-words write-data-words ACL2::LOGHEAD-OF-ONE-LESS-THAN-X))))


(defthm write-data-words-of-1
  (equal (write-data-words 1 denvr offset value ram)
         (write-data-word denvr offset value ram))
  :hints (("Goal" :expand (write-data-words 1 denvr offset value ram)
           :in-theory (enable write-data-words write-data-word acl2::logext-logapp))))

;rename
(defthm write-data-words-replace-offset
  (implies (and (equal (loghead 16 offset1)
                       (loghead 16 offset2))
                (syntaxp (acl2::smaller-term offset2 offset1))
                (integerp offset1)
                (integerp offset2)
                )
           (equal (write-data-words numwords denvr offset1 value ram)
                  (write-data-words numwords denvr offset2 value ram)))
  :hints (("Goal" :in-theory (enable write-data-words))))

(defthm write-data-words-of-loghead-16
  (implies (integerp offset)
           (equal (write-data-words numwords denvr (loghead 16 offset) value ram)
                  (write-data-words numwords denvr offset value ram)))
  :hints (("Goal" :use (:instance write-data-words-replace-offset
                                  (offset1 offset) (offset2  (loghead 16 offset)))
           :in-theory (disable write-data-words-replace-offset))))


(defun write-data-words-induct (numwords offset value)
  (if (zp numwords)
      (list numwords offset value)
    (write-data-words-induct (+ -1 numwords) (+ 1 offset) (logtail 16 value))))

(defthm write-data-words-when-offset-is-not-an-integerp
  (implies (not (integerp offset))
           (equal (write-data-words numwords denvr offset value ram)
                  (write-data-words numwords denvr 0 value ram)))
  :hints (("subgoal *1/2" :in-theory (disable write-data-word-equal-rewrite
                                              write-data-words-opener)
           :use ((:instance write-data-words-opener
                            (numwords numwords)
                            (denvr denvr)
                            (offset offset)
                            (ram ram)
                            )
                 (:instance write-data-words-opener
                            (numwords numwords)
                            (denvr denvr)
                            (offset 0)
                            (ram ram)
                            )))
          ("Goal" :in-theory (e/d (zp) ())
           :do-not '(generalize eliminate-destructors)
           :induct (write-data-words-induct numwords offset value))))

(defthm write-data-words-simplify-constant-offset
  (implies (and (syntaxp (quotep offset))
                (not (acl2::unsigned-byte-p 16 offset))
                (integerp offset)
                )
           (equal (write-data-words numwords denvr offset value ram)
                  (write-data-words numwords denvr (acl2::loghead 16 offset) value ram)))
  :hints (("Goal" :use (:instance write-data-words-replace-offset (offset1 (ifix offset)) (offset2 (acl2::loghead 16 offset)))
           :in-theory (disable write-data-words-replace-offset))))

;rename
(defthm write-data-words-of-sum-hack
  (implies (and (syntaxp (quotep a))
                (not (acl2::unsigned-byte-p 16 a))
                (integerp a)
                (integerp b))
           (equal (write-data-words numwords denvr (+ a b) value ram)
                  (write-data-words numwords denvr (+ (acl2::loghead 16 a) b) value ram)))
  :hints (("Goal" :use ((:instance write-data-words-of-loghead-16 (offset (+ a b)))
                        (:instance write-data-words-of-loghead-16 (offset (+ (acl2::loghead 16 a) b)))
                        )
           :in-theory (disable))))



;; ;bzo gen the 2
;; (defthm read-data-word-of-write-data-words2-same
;;   (equal (read-data-word denvr offset (write-data-words 2 denvr offset val ram))
;;          (loghead 16 val))
;;   :hints (("Goal" :in-theory (enable write-data-words-opener ;bzo
;; ;write-data-words read-data-word
;; ;offset-range-wrap-const-opener ;bzo
;;                                      ))))

(defthm write-data-words-replace-denv
  (implies (and (equal (loghead 15 denvr1)
                       (loghead 15 denvr2))
                (syntaxp (acl2::smaller-term denvr2 denvr1)))
           (equal (write-data-words numwords denvr1 offset value ram)
                  (write-data-words numwords denvr2 offset value ram)))
  :hints (("Goal" :in-theory (enable write-data-words))))

(defthmd loghead-list-32-of-word-ads-to-byte-ads
  (equal (loghead-list 32 (word-ads-to-byte-ads word-ads))
         (word-ads-to-byte-ads (loghead-list 31 word-ads)))
  :hints
  (("Goal"
    :in-theory (enable loghead-list word-ads-to-byte-ads))))

(local
 (defthm read-data-word-of-write-data-words-diff-denvrs
   (implies (not (equal (loghead 15 denvr1) (loghead 15 denvr2)))
            (equal (read-data-word denvr1 offset1 (write-data-words numwords denvr2 offset2 value ram))
                   (read-data-word denvr1 offset1 ram)))
   :hints (("Goal" :in-theory (e/d (read-data-word write-data-words
                                      loghead-list-32-of-word-ads-to-byte-ads
                                      LOGHEAD-LIST-OF-LOGAPP-LIST
                                      acl2::logext-logapp)
                                   (WORD-ADS-TO-BYTE-ADS-OF-LOGHEAD-LIST
                                    LOGAPP-LIST-OF-LOGHEAD))))))

;; (defthm read-data-word-of-write-data-words-hack
;;   (implies (integerp offset)
;;            (equal (read-data-word denvr offset (write-data-words 2 denvr (+ -1 offset) value ram))
;;                   (loghead 16 (logtail 16 value))))
;;   :hints (("Goal" :in-theory (enable write-data-words-opener))))




;; (defthm read-data-word-of-write-data-words-special-case
;;   (implies (and (equal offset1 (+ 1 offset2))
;;                 (integerp offset2))
;;            (equal (read-data-word denvr offset1 (write-data-words 2 denvr offset2 value ram))
;;                   (loghead 16 (logtail 16 value))))
;;   :hints (("Goal" :in-theory (enable write-data-words-opener))))

;bzo is there a non-2 version?
(DEFUN WRITE-DATA-WORDS-INDUCT-wrap2
  (NUMWORDS OFFSET VALUE)
  (IF (ZP NUMWORDS)
      (LIST NUMWORDS OFFSET VALUE)
      (WRITE-DATA-WORDS-INDUCT-wrap2 (+ -1 NUMWORDS)
                                     (loghead 16 (+ 1 OFFSET))
                                     (LOGTAIL 16 VALUE))))

;bzo allow the denvrs to differ here and elsewhere
(defthm read-data-words-of-write-data-word-diff
  (implies (not (list::memberp (loghead 16 offset2) (offset-range-wrap 16 offset1 size)))
           (equal (read-data-words size denvr offset1 (write-data-word denvr offset2 val ram))
                  (read-data-words size denvr offset1 ram)))
  :otf-flg t
  :hints (("Goal" :expand ((OFFSET-RANGE-WRAP 16 0 SIZE))
           :cases ((EQUAL (LOGHEAD '16 (ifix OFFSET2)) (LOGHEAD '16 (ifix OFFSET1)))
;                          (and (not (integerp offset1)) (integerp offset2))
;                          (and (not (integerp offset1)) (integerp offset2))
 ;                         (not (integerp offset2))
                          )
           :in-theory (e/d (read-data-words
                            loghead-list-of-logapp-list
                            WORD-AD-TO-BYTE-ADS
                            write-data-word
                            acl2::logext-logapp
                            ACL2::ASH-AS-LOGAPP
                            )
                           (LOGAPP-LIST-OF-LOGHEAD
                            ;ACL2::EQUAL-LOGAPP-X-Y-Z-CONSTANTS
                            ACL2::LOGAPP-0-PART-2-BETTER
                            MEMBERP-OF-OFFSET-RANGE)))))

(defthm read-data-word-gets-the-second-word
  (implies (integerp x)
           (equal (read-data-word denvr (+ -1 x) (write-data-words 2 denvr (+ -2 x) val ram))
                  (loghead 16 (logtail 16 val))))
  :hints (("Goal" :in-theory (enable WRITE-DATA-WORDS-OPENER))))


;gen or drop?
(defthm read-data-words-of-write-data-words2
  (equal (read-data-words 2 denvr offset (write-data-words 2 denvr offset val ram))
         (loghead 32 val))
  :hints (("Goal" :in-theory (enable READ-DATA-WORDS-OPENER
                                     write-DATA-WORDS-OPENER))))

(defthm read-data-words-of-write-data-words
  (implies (bag::disjoint (offset-range-wrap 16 offset1 numwords1)
                          (offset-range-wrap 16 offset2 numwords2))
           (equal (read-data-words numwords1 denvr1 offset1 (write-data-words numwords2 denvr2 offset2 val ram))
                  (read-data-words numwords1 denvr1 offset1 ram)))
  :hints (("Goal" :in-theory (e/d (read-data-words
                                   ACL2::LOGEXT-LOGAPP ;possible loops?

                                   ACL2::LOGHEAD-LOGAPP
                                   LOGHEAD-LIST-OF-LOGAPP-LIST

                                   ACL2::ASH-AS-LOGAPP
                                   write-data-words)
                                  (LOGAPP-LIST-OF-LOGHEAD

                                   READ-DATA-WORDS-OPENER
                                   MEMBERP-OF-OFFSET-RANGE
                                   WRITE-DATA-WORDS-OPENER
                                   ACL2::LOGAPP-0-PART-2-BETTER
                                   DISJOINT-OF-TWO-OFFSET-RANGE-WRAPS)))))

(defthm write-data-words-of-write-data-words-diff
  (implies (bag::disjoint (offset-range-wrap 16 offset1 numwords1)
                          (offset-range-wrap 16 offset2 numwords2))
           (equal (write-data-words numwords2 denvr2 offset2 val2 (write-data-words numwords1 denvr1 offset1 val1 ram))
                  (write-data-words numwords1 denvr1 offset1 val1 (write-data-words numwords2 denvr2 offset2 val2 ram))))
  :hints (("Goal" :in-theory (e/d (write-data-words
                                   LOGHEAD-LIST-OF-LOGAPP-LIST)
                                  (LOGAPP-LIST-OF-LOGHEAD
                                   READ-DATA-WORDS-OPENER
                                   MEMBERP-OF-OFFSET-RANGE
                                   WRITE-DATA-WORDS-OPENER
                                   DISJOINT-OF-TWO-OFFSET-RANGE-WRAPS
                                   ACL2::PLUS-OF-LOGAPP-SUCK-IN)))))

(defthm write-data-words-of-write-data-words-same
  (implies (and (equal denvr1 denvr2) ;bzo gen
                (equal offset1 offset2)
                (equal numwords1 numwords2)
                )
           (equal (write-data-words numwords2 denvr2 offset2 val2 (write-data-words numwords1 denvr1 offset1 val1 ram))
                  (write-data-words numwords2 denvr2 offset2 val2 ram)))
  :hints (("Goal" :in-theory (e/d (write-data-words)
                                  (READ-DATA-WORDS-OPENER
                                   MEMBERP-OF-OFFSET-RANGE
                                   WRITE-DATA-WORDS-OPENER
                                   DISJOINT-OF-TWO-OFFSET-RANGE-WRAPS
                                   ACL2::PLUS-OF-LOGAPP-SUCK-IN)))))

;move
(defthm disjoint-of-word-ads-to-byte-ads
  (implies (and (integer-listp x)
                (integer-listp y))
           (equal (disjoint x (word-ads-to-byte-ads y))
                  (disjoint (logcdr-list x) y)))
  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads))))

(defthm subbagp-of-word-ad-to-byte-ads-and-word-ads-to-byte-ads
  (implies (list::memberp ad ads)
           (bag::subbagp (word-ad-to-byte-ads ad)
                         (word-ads-to-byte-ads ads)))
  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads))))

(local (in-theory (disable MEMBERP-OF-OFFSET-RANGE)))

(defthmd write-data-words-of-write-data-words-cover
  (implies (bag::subbagp (offset-range-wrap 16 offset2 numwords2)
                         (offset-range-wrap 16 offset1 numwords1) )
           (equal (write-data-words numwords1 denvr offset1 val1 (write-data-words numwords2 denvr offset2 val2 ram))
                  (write-data-words numwords1 denvr offset1 val1 ram)))
  :hints (("Goal" :cases (zp numwords)
           :in-theory (e/d (LOGHEAD-LIST-OF-LOGAPP-LIST
                              zp write-data-word write-data-words acl2::logext-logapp)
                           (LOGAPP-LIST-OF-LOGHEAD)))))


;; (thm
;;  (equal (logcdr-list (word-ads-to-byte-ads ads))
;;         need a way to state this...)
;;  :hints (("Goal" :in-theory (enable word-ads-to-byte-ads))))

(defthm write-data-word-of-write-data-words-diff-denvrs
  (implies (not (equal (loghead 15 denvr1) (loghead 15 denvr2)))
           (equal (write-data-word denvr1 offset1 val1 (write-data-words numwords denvr2 offset2 val2 ram))
                  (write-data-words numwords denvr2 offset2 val2 (write-data-word denvr1 offset1 val1 ram))))
  :rule-classes ((:rewrite :loop-stopper ((denvr1 denvr2))))
  :hints (("Goal" ;:cases ((equal (loghead 15 denvr1) (loghead 15 denvr2)))
           :in-theory (e/d (write-data-words
                            write-data-word
                            acl2::logext-logapp
                            LOGHEAD-LIST-OF-LOGAPP-LIST
                            )
                           (
                            disjoint-of-WORD-AD-TO-BYTE-ADS
                            LOGAPP-LIST-OF-LOGHEAD
                            disjoint-of-word-ads-to-byte-ads)))))



(local (in-theory (disable disjoint-of-WORD-AD-TO-BYTE-ADS
                           disjoint-of-word-ads-to-byte-ads)))

;;
;; CLEAR-DATA-WORDS
;;

;bzo add guard?
(defund clear-data-words (numwords denvr offset ram1)
  (write-data-words numwords denvr offset 0 ram1))

(defthm clear-data-words-when-numwords-is-zp
  (implies (zp numwords)
           (equal (clear-data-words numwords denvr offset ram)
                  ram))
  :hints (("Goal" :in-theory (e/d (clear-data-words clear-data-word)
                                  (write-data-word-equal-rewrite  write-data-words-opener)))))

;;
;; theorems about write-data-words, etc.
;;

(defthm write-data-words-equal-rewrite
  (implies (<= numwords 65536)
           (equal (equal (write-data-words numwords denvr offset value ram1) ram2)
                  (and (equal (loghead (* 16 (ifix numwords)) value) (read-data-words numwords denvr offset ram2))
                       (equal (clear-data-words numwords denvr offset ram1)
                              (clear-data-words numwords denvr offset ram2)))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (WRITE-DATA-WORD READ-DATA-WORD
                                                   WORD-AD-TO-BYTE-ADS
                                                   ACL2::EQUAL-LOGAPP-X-Y-Z
                                                   WR==R!
                                                   CLEAR-DATA-WORDS
                                                   READ-DATA-WORDS
                                                   WRITE-DATA-WORDS
                                                   LOGHEAD-LIST-OF-LOGAPP-LIST
                                                   )
                                  (LOGAPP-LIST-OF-LOGHEAD
                                   UNIQUE-OF-WORD-ADS-TO-BYTE-ADS-better)))))

(defthm write-data-words-of-write-data-word-diff-denvrs
  (implies (not (equal (loghead 15 denvr1) (loghead 15 denvr2)))
           (equal (write-data-words numwords denvr1 offset1 val1 (write-data-word denvr2 offset2 val2 ram))
                  (write-data-word denvr2 offset2 val2 (write-data-words numwords denvr1 offset1 val1 ram))))
  :rule-classes ((:rewrite :loop-stopper ((denvr1 denvr2))))
  :hints (("Goal" :in-theory (e/d (write-data-words
                                     write-data-word
                                     acl2::logext-logapp
                                     LOGHEAD-LIST-OF-LOGAPP-LIST
                                     )
                                  (LOGAPP-LIST-OF-LOGHEAD)))))

;(local (in-theory (disable LOGAPP-LIST-OF-LOGHEAD)))
(local (in-theory (enable LOGHEAD-LIST-OF-LOGAPP-LIST)))

(defthm clear-data-words-of-write-data-word
  (implies (not (list::memberp (loghead 16 offset2) (offset-range-wrap 16 offset1 numwords)))
           (equal (clear-data-words numwords denvr1 offset1 (write-data-word denvr2 offset2 value ram))
                  (write-data-word denvr2 offset2 value (clear-data-words numwords denvr1 offset1 ram))))
  :hints (("Goal" :in-theory (enable clear-data-words))))

(defthm clear-data-words-of-write-data-words-diff
  (implies (bag::disjoint (offset-range-wrap 16 offset1 numwords1)
                          (offset-range-wrap 16 offset2 numwords2))
           (equal (clear-data-words numwords1 denvr1 offset1 (write-data-words numwords2 denvr2 offset2 value ram))
                  (write-data-words numwords2 denvr2 offset2 value (clear-data-words numwords1 denvr1 offset1 ram))))
  :hints (("Goal" :in-theory (enable clear-data-words write-data-words))))




(defthm clear-data-word-of-write-data-words-diff-denvrs
  (implies (not (list::memberp (loghead 16 offset1) (offset-range-wrap 16 offset2 numwords)))
           (equal (CLEAR-DATA-WORD denvr1 offset1 (WRITE-DATA-WORDS numwords denvr2 offset2 value ram))
                  (WRITE-DATA-WORDS numwords denvr2 offset2 value (CLEAR-DATA-WORD denvr1 offset1 ram))))
  :hints (("Goal" :in-theory (e/d (
                                   clear-data-word
                                   acl2::logext-logapp)
                                  (WRITE-DATA-WORD-EQUAL-REWRITE)))))

(defthm clear-data-word-of-write-data-words-diff-offsets
  (implies (not (list::memberp (loghead 16 offset1) (offset-range-wrap 16 offset2 numwords)))
           (equal (clear-data-word denvr1 offset1 (write-data-words numwords denvr2 offset2 value ram))
                  (write-data-words numwords denvr2 offset2 value (clear-data-word denvr1 offset1 ram))))
  :hints (("Goal" :in-theory (e/d (
                                   clear-data-word
                                   acl2::logext-logapp)
                                  (write-data-word-equal-rewrite)))))

;gen!
(defthm loghead-16-of-read-data-words
  (equal (loghead 16 (read-data-words numwords denvr offset ram))
         (if (zp numwords)
             0
           (read-data-word denvr offset ram)))
  :hints (("Goal" :in-theory (enable read-data-words read-data-word acl2::logext-logapp))))

;move
;gen!
(defthm logtail-16-of-read-data-words
  (equal (logtail 16 (read-data-words numwords denvr offset ram))
         (read-data-words (+ -1 numwords) denvr (+ 1 (ifix offset)) ram))
  :hints (("Goal" :expand ((OFFSET-RANGE-WRAP 16 OFFSET NUMWORDS)
                           (OFFSET-RANGE-WRAP 16 0 NUMWORDS))
           :in-theory (enable read-data-words))))




;drop?
(defthm clear-data-word-of-write-data-words-special-case
  (implies (and (equal (loghead 16 offset1) (loghead 16 (+ -1 numwords offset2)))
                (equal numwords 2) ;bbzo get rid of this and remove -special case from the theorem name
                (integerp offset2)
                (<= numwords 65536))
           (equal (clear-data-word denvr offset1 (write-data-words numwords denvr offset2 value ram))
                  (write-data-words (+ -1 numwords) denvr offset2 value (clear-data-word denvr offset1 ram))))
  :hints (("Goal" :in-theory (e/d (;offset-range-wrap-const-opener
;                                  clear-data-word write-data-word
;write-data-words
                                   write-data-words-opener
                                   )
                                  (ACL2::LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT
                                   write-data-word-equal-rewrite)))))

(defthm clear-data-words-of-write-data-words-same
  (equal (clear-data-words numwords denvr offset (write-data-words numwords denvr offset value ram))
         (clear-data-words numwords denvr offset ram))
  :hints (("Goal" :in-theory (enable clear-data-words))))

;bzo
(defthm write-data-words-of-what-was-already-there
  (implies (equal val (read-data-words numwords denvr offset ram))
           (equal (write-data-words numwords denvr offset val ram)
                  ram))
  :hints (("Goal" :cases ((and (integerp numwords)
                               (<= 0 numwords)))
           :in-theory (enable write-data-words read-data-words))))

;bzo
(defthm write-data-words-of-what-was-already-there-cheap
  (equal (write-data-words numwords denvr offset (read-data-words numwords denvr offset ram) ram)
         ram)
  :hints (("Goal" :in-theory (enable write-data-words read-data-words))))

(defthm clear-data-word-of-write-data-words-special-case-2
  (implies (and (equal numwords 2) ;bbzo get rid of this and remove -special case from the theorem name
;                (integerp offset)
                (<= numwords 65536))
           (equal (clear-data-word denvr offset (write-data-words numwords denvr offset value ram))
                  (write-data-words (+ -1 numwords) denvr (+ 1 (ifix offset)) (logtail 16 value) (clear-data-word denvr offset ram))))
  :hints (("Goal" :in-theory (e/d (;offset-range-wrap-const-opener
;                                  clear-data-word write-data-word
;write-data-words
                                   write-data-words-opener
                                   )
                                  (ACL2::LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT
                                   write-data-word-equal-rewrite)))))

(defthm read-data-words-sum-loghead-hack
  (equal (read-data-words numwords denvr (+ i (loghead 16 j)) ram)
         (read-data-words numwords denvr (+ i (ifix j)) ram))
  :hints (("Goal" :in-theory (enable read-data-words))))

(defthm write-data-words-of-loghead-hack
  (equal (write-data-words 2 denvr offset (loghead 32 val) ram)
         (write-data-words 2 denvr offset val ram))
  :hints (("Goal" :in-theory (enable write-data-words))))

;bzo gen!
(defthm write-data-words2-of-logext
  (equal (write-data-words 2 denvr offset (logext 32 x) ram)
         (write-data-words 2 denvr offset x ram))
  :hints (("Goal" :in-theory (enable write-data-words))))


;bzo allow denvrs to differ
(defthm read-data-words-of-clear-data-word-diff
  (implies (not (list::memberp (loghead 16 offset2) (offset-range-wrap 16 offset1 size)))
           (equal (read-data-words size denvr offset1 (clear-data-word denvr offset2 ram))
                  (read-data-words size denvr offset1 ram)))
  :hints (("Goal" :cases ((EQUAL (LOGHEAD '16 OFFSET2) (LOGHEAD '16 OFFSET1)))
           :in-theory (e/d (clear-data-word)
                           (WRITE-DATA-WORD-EQUAL-REWRITE)))))

(defthm read-data-words-of-clear-data-words-diff
  (implies (bag::disjoint (offset-range-wrap 16 offset1 numwords1)
                          (offset-range-wrap 16 offset2 numwords2))
           (equal (read-data-words numwords1 denvr1 offset1 (clear-data-words numwords2 denvr2 offset2 ram))
                  (read-data-words numwords1 denvr1 offset1 ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-words)
                                  ()))))

(defthm clear-data-words-of-write-data-word-cover
   (implies (list::memberp (loghead 16 offset2) (offset-range-wrap 16 offset1 numwords))
            (equal (clear-data-words numwords denvr offset1 (write-data-word denvr offset2 value ram))
                   (clear-data-words numwords denvr offset1 ram)))
   :hints (("Goal" :in-theory (enable clear-data-words))))



(defthm clear-data-words-of-sum-of-loghead
  (equal (clear-data-words numwords denvr (+ i (loghead 16 j)) ram)
         (clear-data-words numwords denvr (+ i (ifix j)) ram))
  :hints (("Goal" :in-theory (enable clear-data-words
                                     ))))


(defthm CLEAR-DATA-WORDS-of-WRITE-DATA-WORDS-partial-overlap-2
  (implies (and (equal (loghead 16 offset1) (loghead 16 (+ 1 (ifix offset2))))
                (integerp offset2)
                (integerp offset1))
           (equal (CLEAR-DATA-WORDS 2 denvr offset2 (WRITE-DATA-WORDS 2 denvr offset1 value ram))
                  (WRITE-DATA-WORD denvr (+ 1 offset1) (logtail 16 value) (CLEAR-DATA-WORDS 2 denvr offset2 ram))))
  :hints (("Goal" :in-theory (e/d (CLEAR-DATA-WORDS
;DISJOINT-OF-TWO-OFFSET-RANGE-WRAPS
                                   READ-DATA-WORDS-OPENER
                                   WRITE-DATA-WORDS-OPENER

                                   )
                                  (;READ-DATA-WORDS-RECOLLAPSE
                                   acl2::LOGHEAD-SUM-SUBST-ALT ;bzo looped
                                   WRITE-DATA-WORDS-EQUAL-REWRITE ;bzo loops!
                                   )))))




;; (defthm
;; (WRITE-DATA-WORD DENVR2 OFFSET1 VALUE
;;                               (WRITE-DATA-WORD DENVR1 OFFSET1 VALUE RAM))


;; (thm
;;  (equal (CLEAR-DATA-WORD DENVR1 OFFSET1 (WRITE-DATA-WORD DENVR2 OFFSET1 VALUE RAM))

;; (defthm write-data-word-of-write-data-word-same-value
;;   (equal (write-data-word denvr1 offset1 value (write-data-word denvr2 offset2 value ram))
;;          (write-data-word denvr2 offset2 value (write-data-word denvr1 offset1 value ram)))
;;   :hints (("Goal" :cases ((equal (loghead 16 offset1) (loghead 16 offset2))))))

;; (defthmd clear-data-words-constant-opener2
;;   (equal (clear-data-words 2 denvr offset ram1)
;;          (clear-data-word denvr offset (clear-data-word denvr (+ 1 (ifix offset)) ram1))
;;          )
;;   :hints (("Goal" :in-theory (e/d (clear-data-words
;;                                    WRITE-DATA-WORDS-OPENER)
;;                                   (WRITE-DATA-WORDS-EQUAL-REWRITE ;bzo
;;                                    )))))




;(in-theory (disable READ-DATA-WORDS-OPENER))

(defthm read-data-words-of-write-data-word-hack
  (implies (integerp offset)
           (equal (read-data-words 2 denvr (+ -1 offset) (write-data-word denvr offset value ram))
                  (logapp 16
                          (read-data-word denvr (+ -1 offset) ram)
                          (loghead 16 value))))
  :hints (("Goal" :in-theory (enable read-data-words-opener))))


;this loops with the splitting up rules?
;move
(defthmd read-data-words-recollapse
  (implies (equal (loghead 16 offset2) (loghead 16 (+ 1 (ifix offset1))))
           (equal (logapp 16
                          (read-data-word denvr offset1 ram)
                          (read-data-word denvr offset2 ram))
                  (read-data-words 2 denvr offset1 ram)))
  :hints (("Goal" :in-theory (e/d (read-data-words-opener)
                                  (ACL2::LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT)))))

(defthm write-data-words-of-write-data-words-diff-new
  (implies (and (syntaxp (smaller-params denvr2 offset2 denvr1 offset1))
                (bag::disjoint (offset-range-wrap 16 offset1 numwords1)
                               (offset-range-wrap 16 offset2 numwords2)))
           (equal (write-data-words numwords1 denvr1 offset1 val1 (write-data-words numwords2 denvr2 offset2 val2 ram))
                  (write-data-words numwords2 denvr2 offset2 val2 (write-data-words numwords1 denvr1 offset1 val1 ram))))
  :rule-classes ((:rewrite :loop-stopper nil)))


;more like this?
;bzo bad name?
(defthm clear-data-words-of-write-data-words-partial-overlap-1
  (implies (and (equal (loghead 16 offset2) (loghead 16 (+ 1 (ifix offset1))))
                (integerp offset2)
                (integerp offset1))
           (equal (clear-data-words 2 denvr offset2 (write-data-words 2 denvr offset1 value ram))
                  (write-data-word denvr offset1 value (clear-data-words 2 denvr offset2 ram))))
  :hints (("Goal" :in-theory (e/d (clear-data-words
;disjoint-of-two-offset-range-wraps
                                   read-data-words-opener
                                   write-data-words-opener
                                   )
                                  (read-data-words-recollapse
                                   acl2::loghead-sum-split-into-2-when-i-is-a-constant
                                   write-data-words-equal-rewrite ;bzo loops!
                                   )))))

;;
;; These use the bag phrasing...
;;

;move this up?
(defthm read-data-words-of-write-data-word-diff-denvrs
  (implies (not (equal (loghead 15 denvr1)
                       (loghead 15 denvr2)))
           (equal (read-data-words numwords denvr1 offset1 (write-data-word denvr2 offset2 value ram))
                  (read-data-words numwords denvr1 offset1 ram)))
  :hints (("Goal" :in-theory (enable write-data-word
                                     word-ad-to-byte-ads
                                     read-data-words
                                     acl2::logext-logapp))))


(defthm read-data-words-of-write-data-word-diff-better
  (implies (not (list::memberp (loghead 16 offset2) (offset-range-wrap 16 offset1 size)))
           (equal (read-data-words size denvr offset1 (write-data-word denvr2 offset2 val ram))
                  (read-data-words size denvr offset1 ram)))
  :otf-flg t
  :hints (("Goal" :cases ((equal (loghead 15 denvr) (loghead 15 denvr2)))))
  )

(in-theory (disable READ-DATA-WORDS-OF-WRITE-DATA-WORD-DIFF))

(DEFTHM READ-DATA-WORD-OF-SUM-NORMALIZE-CONSTANT-addend
  (IMPLIES (AND (SYNTAXP (QUOTEP K))
                (NOT (UNSIGNED-BYTE-P 16 K))
                (integerp x)
                (integerp k)
                )
           (EQUAL (READ-DATA-WORD DENVR (+ K x) RAM)
                  (READ-DATA-WORD DENVR (+ (LOGHEAD 16 K) x)
                                  RAM)))
  :HINTS
  (("Goal"
    :IN-THEORY (DISABLE READ-DATA-WORD-OF-LOGHEAD16-2
                        )
    :USE ((:INSTANCE READ-DATA-WORD-OF-LOGHEAD16-2
                     (OFFSET (+ x (LOGHEAD 16 K))))
          (:INSTANCE READ-DATA-WORD-OF-LOGHEAD16-2
                     (OFFSET (+ x K)))))))

;bzo make a -better version?
(defthm clear-data-words-of-write-data-words-cover
  (implies (bag::subbagp (offset-range-wrap 16 offset2 numwords2)
                         (offset-range-wrap 16 offset1 numwords1))
           (equal (clear-data-words
                   numwords1
                   denvr offset1
                   (write-data-words
                    numwords2 denvr
                    offset2 val2 ram))
                  (clear-data-words
                   numwords1 denvr
                   offset1 ram)))
  :hints (("Goal" :in-theory (enable clear-data-words
                                     write-data-words-of-write-data-words-cover
                                     ))))



(defthm clear-data-words-of-clear-data-word-cover
  (implies (list::memberp (loghead 16 offset2) (offset-range-wrap 16 offset1 numwords))
           (equal (clear-data-words numwords denvr offset1 (clear-data-word denvr offset2 ram))
                  (clear-data-words numwords denvr offset1 ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-words
                                     clear-data-word)
                                  (WRITE-DATA-WORD-EQUAL-REWRITE)))))

(defthm clear-data-words-of-clear-data-word-cover-hack
  (implies (and (< (loghead 16 offset2) numwords)
                (integerp numwords))
           (equal (clear-data-words numwords denvr 0 (clear-data-word denvr offset2 ram))
                  (clear-data-words numwords denvr 0 ram)))
  :hints (("Goal" :in-theory (enable memberp-of-offset-range
                                     acl2::loghead-sum-split-into-2-cases
                                     acl2::loghead-of-minus))))


;prove from the multi-word version?
(defthm write-data-words-of-write-data-word-cover-better
  (implies (and (< (loghead 16 (- offset2 offset1)) numwords)
                (integerp offset1)
                (integerp offset2)
                (integerp numwords)
                )
           (equal (write-data-words numwords denvr offset1 val1 (write-data-word denvr offset2 val2 ram))
                  (write-data-words numwords denvr offset1 val1 ram)))
  :hints (("Goal" :in-theory (enable memberp-of-offset-range))))

;what about the non-better lemma?
(defthm clear-data-words-of-write-data-word-cover-better
  (implies (and (< (loghead 16 (- offset2 offset1)) numwords)
                (integerp offset1)
                (integerp offset2)
                (integerp numwords)
                )
           (equal (clear-data-words numwords denvr offset1 (write-data-word denvr offset2 value ram))
                  (clear-data-words numwords denvr offset1 ram)))
  :hints (("Goal" :in-theory (enable clear-data-words))))

;every theorem about clear-data-words should be proved easily from an analogous theorem about write-data-words!
;make sure analogues exist for each theorem about either function.
;likewise for the single-word ops

(defthm write-data-words-of-write-data-word-diff-better
  (implies (and (syntaxp (smaller-params denvr2 offset2 denvr1 offset1))
                (<= numwords (loghead 16 (- offset2 offset1)))
                (integerp offset1)
                (integerp offset2)
                (integerp numwords)
                )
           (equal (write-data-words numwords denvr1 offset1 val1 (write-data-word denvr2 offset2 val2 ram))
                  (write-data-word denvr2 offset2 val2 (write-data-words numwords denvr1 offset1 val1 ram))))
   :rule-classes ((:rewrite :loop-stopper nil))
   :hints (("Goal" :in-theory (e/d (memberp-of-offset-range)
                                  (write-data-word-equal-rewrite
                                   write-data-words-equal-rewrite)))))

;three "clear" variations of write-data-words-of-write-data-word-diff
(defthm clear-data-words-of-write-data-word-diff
  (implies (and (<= numwords (loghead 16 (- offset2 offset1)))
                (integerp offset1)
                (integerp offset2)
                (integerp numwords)
                )
           (equal (clear-data-words numwords denvr1 offset1 (write-data-word denvr2 offset2 val ram))
                  (write-data-word denvr2 offset2 val (clear-data-words numwords denvr1 offset1 ram))))
  :hints (("Goal" :use (:instance write-data-words-of-write-data-word-diff-better (val2 val) (val1 0))
           :in-theory (e/d (clear-data-words) (write-data-words-of-write-data-word-diff
                                                     write-data-word-equal-rewrite
                                                     write-data-words-equal-rewrite)))))

(defthm clear-data-words-of-clear-data-word-diff
  (implies (and (<= numwords (loghead 16 (- offset2 offset1)))
                (integerp offset1)
                (integerp offset2)
                (integerp numwords)
                )
           (equal (clear-data-words numwords denvr1 offset1 (clear-data-word denvr2 offset2 ram))
                  (clear-data-word denvr2 offset2 (clear-data-words numwords denvr1 offset1 ram))))
  :hints (("Goal" :use (:instance write-data-words-of-write-data-word-diff-better (val2 0) (val1 0))
           :in-theory (e/d (clear-data-words
                            clear-data-word)
                           (write-data-words-of-write-data-word-diff
                            write-data-word-equal-rewrite
                            write-data-words-equal-rewrite)))))

;Disabled because it goes against our convention of pushing clears inside of writes.
(defthmd write-data-words-of-clear-data-word-diff
  (implies (and (<= numwords (loghead 16 (- offset2 offset1)))
                (integerp offset1)
                (integerp offset2)
                (integerp numwords)
                )
           (equal (write-data-words numwords denvr1 offset1 val (clear-data-word denvr2 offset2 ram))
                  (clear-data-word denvr2 offset2 (write-data-words numwords denvr1 offset1 val ram))))
  :hints (("Goal" :use (:instance write-data-words-of-write-data-word-diff-better (val2 0) (val1 val))
           :in-theory (e/d (clear-data-word) (write-data-words-of-write-data-word-diff
                                                    write-data-word-equal-rewrite
                                                    write-data-words-equal-rewrite)))))



(defthm read-data-word-of-clear-data-words-diff-better-better
  (implies(and (<= numwords (loghead 16 (- offset1 offset2)))
               (integerp offset1)
               (integerp offset2)
               (integerp numwords)
               )
          (equal (read-data-word denvr offset1 (clear-data-words numwords denvr2 offset2 ram))
                 (read-data-word denvr offset1 ram)))
  :hints (("Goal" :in-theory (enable clear-data-words))))

(defthm write-data-words-of-write-data-words-cover-better
  (implies (and (<= (+ numwords2 (loghead 16 (+ offset2 (- offset1)))) numwords1)
                (<= numwords2 (expt 2 16)) ;bzo can probably drop stuff like this?
                (integerp numwords1)
                (integerp numwords2)
                (integerp offset1)
                (integerp offset2))
           (equal (write-data-words numwords1 denvr offset1 val1 (write-data-words numwords2 denvr offset2 val2 ram))
                  (write-data-words numwords1 denvr offset1 val1 ram)))
  :hints (("Goal" :cases ((<= 0 numwords2))
           :in-theory (enable write-data-words-of-write-data-words-cover))))

;analogue with clear of clear?
(defthm clear-data-words-of-write-data-words-cover-better
  (implies (and (<= (+ numwords2 (loghead 16 (+ offset2 (- offset1)))) numwords1)
                (<= numwords2 (expt 2 16))
                (integerp numwords1)
                (integerp numwords2)
                (integerp offset1)
                (integerp offset2))
           (equal (clear-data-words numwords1 denvr offset1 (write-data-words numwords2 denvr offset2 val2 ram))
                  (clear-data-words numwords1 denvr offset1 ram)))
  :hints (("Goal" :cases ((<= 0 numwords2))
           :in-theory (enable write-data-words-of-write-data-words-cover))))


(defthm write-data-words-of-write-data-words-diff-new-better
  (implies (and (syntaxp (smaller-params denvr2 offset2 denvr1 offset1))
                (and (<= numwords1 (loghead 16 (+ (ifix offset2) (- (ifix offset1)))))
                     (<= numwords2 (loghead 16 (+ (ifix offset1) (- (ifix offset2))))))
                )
           (equal (write-data-words numwords1 denvr1 offset1 val1 (write-data-words numwords2 denvr2 offset2 val2 ram))
                  (write-data-words numwords2 denvr2 offset2 val2 (write-data-words numwords1 denvr1 offset1 val1 ram))))
  :rule-classes ((:rewrite :loop-stopper nil)))

(defthm clear-data-words-of-write-data-words-diff-better
  (implies (and (<= numwords1 (loghead 16 (+ (ifix offset2) (- (ifix offset1)))))
                (<= numwords2 (loghead 16 (+ (ifix offset1) (- (ifix offset2))))))
           (equal (clear-data-words numwords1 denvr1 offset1 (write-data-words numwords2 denvr2 offset2 val ram))
                  (write-data-words numwords2 denvr2 offset2 val (clear-data-words numwords1 denvr1 offset1 ram))))
  :hints (("Goal" :in-theory (disable write-data-words-equal-rewrite)))) ;why the disable?

;clear-data-words of clear-data-words doesn't need any same or diff hyps since writing same values.
;same for single word and single/multi word cases.

;prove the single word lemmas from the multi-word lemmas?
;kill READ-DATA-WORDS-OF-WRITE-DATA-WORDS?
(defthm read-data-words-of-write-data-words-diff-better
  (implies (and (<= numwords1 (loghead 16 (+ (ifix offset2) (- (ifix offset1)))))
                (<= numwords2 (loghead 16 (+ (ifix offset1) (- (ifix offset2))))))
           (equal (read-data-words numwords1 denvr1 offset1 (write-data-words numwords2 denvr2 offset2 val ram))
                  (read-data-words numwords1 denvr1 offset1 ram))))

(defthm read-data-words-of-clear-data-words-diff-better
  (implies (and (<= numwords1 (loghead 16 (+ (ifix offset2) (- (ifix offset1)))))
                (<= numwords2 (loghead 16 (+ (ifix offset1) (- (ifix offset2))))))
           (equal (read-data-words numwords1 denvr1 offset1 (clear-data-words numwords2 denvr2 offset2 ram))
                  (read-data-words numwords1 denvr1 offset1 ram)))
  :hints (("Goal" :in-theory (enable clear-data-words))))

(defthm read-data-words-of-write-data-word-diff-better-better
  (implies (and (<= numwords (loghead 16 (- offset2 offset1)))
                (integerp offset1)
                (integerp offset2)
                (integerp numwords)
                )
           (equal (read-data-words numwords denvr offset1 (write-data-word denvr2 offset2 val ram))
                  (read-data-words numwords denvr offset1 ram)))
  :hints (("Goal" :in-theory (e/d (memberp-of-offset-range)
                                  ())))  )

(defthm read-data-words-of-clear-data-word-diff-better-better
  (implies (and (<= numwords (loghead 16 (- offset2 offset1)))
                (integerp offset1)
                (integerp offset2)
                (integerp numwords)
                )
           (equal (read-data-words numwords denvr offset1 (clear-data-word denvr2 offset2 ram))
                  (read-data-words numwords denvr offset1 ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-word)
                                  (WRITE-DATA-WORD-EQUAL-REWRITE)))))






(defthmd clear-data-words-opener
  (implies (and (syntaxp (quotep numwords))
                (<= numwords 8) ;arbitrary cut-off to prevent acl2 going out to lunch expanding large operations
                (not (zp numwords)))
           (equal (clear-data-words numwords denvr offset ram)
                  (clear-data-word denvr offset (clear-data-words (+ -1 numwords) denvr (+ 1 (ifix offset)) ram))))
  :hints (("Goal" :use (:instance  write-data-words-opener (value 0))
           :in-theory (e/d (clear-data-words clear-data-word)
                                  (write-data-word-equal-rewrite  write-data-words-opener)))))



(defthm read-data-words-of-sum-normalize-constant
  (implies (and (syntaxp (quotep k))
                (not (acl2::unsigned-byte-p 16 k))
                )
           (equal (read-data-words numwords denvr k ram)
                  (read-data-words numwords denvr (acl2::loghead 16 k) ram)))
  :hints (("Goal" :in-theory (disable READ-DATA-WORDS-OF-LOGHEAD-AROUND-OFFSET)
           :use ((:instance READ-DATA-WORDS-OF-LOGHEAD-AROUND-OFFSET (offset (acl2::loghead 16 k)))
                 (:instance READ-DATA-WORDS-OF-LOGHEAD-AROUND-OFFSET (offset k))))))

(defthm read-data-words-of-sum-normalize-constant-addend
  (implies (and (syntaxp (quotep k))
                (not (unsigned-byte-p 16 k))
                (integerp x)
                (integerp k)
                )
           (equal (read-data-words numwords denvr (+ k x) ram)
                  (read-data-words numwords denvr (+ (loghead 16 k) x)
                                  ram)))
  :hints (("Goal" :in-theory (disable read-data-words-of-loghead-around-offset)
           :use ((:instance read-data-words-of-loghead-around-offset (offset (+ x (loghead 16 k))))
                 (:instance read-data-words-of-loghead-around-offset (offset (+ x k)))))))


;oo





;;
;;
;; MAKE-CODE-ADDR
;;
;;

;; Create a byte-address by concatenating a 16-bit code environment, CENVR,
;; onto a 16 bit offset, OFFSET.  CENVR forms the more signficiant
;; bits of the result.  See "Section 2.1 MEMORY ADDRESSING" in the AAMP
;; manual.
;;
;; Note that after logapp computes a 32-bit unsigned result, we sign-extend
;; that result to a signed 32-bit number.  This is because addresses in the
;; AAMP RAM are signed numbers (though perhaps we'll change that fact
;; later?). -ews
;;
;; bzo add a guard and give this a fast body?
(defund make-code-addr (cenvr offset)
  (declare (type integer cenvr offset))
;;  (logext 32 (logapp 16 offset cenvr))
    (loghead 32 (logapp 16 offset cenvr))
    )

;; (defthm signed-byte-p-of-make-code-addr
;;   (signed-byte-p 32 (make-code-addr env offset))
;;   :hints (("Goal" :in-theory (enable make-code-addr))))


(defthm unsigned-byte-p-of-make-code-addr
  (unsigned-byte-p 32 (make-code-addr env offset))
  :hints (("Goal" :in-theory (enable make-code-addr))))


(defthm make-code-addr-when-offset-is-not-an-integerp
  (implies (not (integerp offset))
           (equal (make-code-addr cenvr offset)
                  (make-code-addr cenvr 0)))
  :hints (("Goal" :in-theory (enable make-code-addr))))

(defthm make-code-addr-when-cenvr-is-not-an-integerp
  (implies (not (integerp cenvr))
           (equal (make-code-addr cenvr offset)
                  (make-code-addr 0 offset)))
  :hints (("Goal" :in-theory (enable make-code-addr))))

;generalize the 16?
(defthm make-code-addr-of-loghead-1
  (equal (make-code-addr (loghead 16 cenvr) offset)
         (make-code-addr cenvr offset))
  :hints (("Goal" :in-theory (enable make-code-addr acl2::logext-logapp))))

;generalize the 16?
(defthm make-code-addr-of-loghead-2
  (equal (make-code-addr cenvr (loghead 16 offset))
         (make-code-addr cenvr offset))
  :hints (("Goal" :in-theory (enable make-code-addr))))


;linear rule for makeaddr?

(defthm make-code-addr-of-logext-gen
  (implies (and (integerp n)
                (<= 16 n))
           (equal (make-code-addr cenvr (logext n offset))
                  (make-code-addr cenvr offset)))
  :hints (("Goal" :use ((:instance make-code-addr-of-loghead-2)
                        (:instance make-code-addr-of-loghead-2 (offset (logext n offset))))
           :in-theory (disable make-code-addr-of-loghead-2))))

(defthm make-code-addr-of-sum-hack
  (implies (and (syntaxp (quotep a))
                (not (unsigned-byte-p 16 a))
                (integerp a)
                (integerp b)
                )
           (equal (make-code-addr cenvr (+ a b))
                  (make-code-addr cenvr (+ (loghead 16 a) b))))
  :hints (("Goal" :use ((:instance make-code-addr-of-loghead-2 (offset (+ a b)))
                        (:instance make-code-addr-of-loghead-2 (offset (+ (loghead 16 a) b)))
                        )
           :in-theory (disable make-code-addr-of-loghead-2))))

;;;;;

;do we want this?
;this may have looped...
(defthm make-code-addr-of-+-loghead
  (implies (and (integerp y1)
                (integerp y2))
           (equal (make-code-addr x (+ y1 (loghead 16 y2)))
                  (make-code-addr x (loghead 16 (+ y1 y2))) ;further simplify this?
                  ))
  :hints (("Goal" :in-theory (enable make-code-addr logapp))))

;bzo
;weird.  do we still need this?
(defthm make-code-addr-of-make-code-addr
  (implies (and (integerp x) (integerp x2) (integerp y)  (integerp k))
           (equal (make-code-addr x (make-code-addr x2 y))
                  (make-code-addr x y)))
  :hints (("Goal" :in-theory (enable make-code-addr))))

;weird.  do we still need this?
(defthm make-code-addr-plus-hack
  (implies (and (integerp x) (integerp x2) (integerp y)  (integerp k))
           (equal (make-code-addr x (+ k (make-code-addr x2 y)))
                  (make-code-addr x (+ k y))))
  :hints (("Goal" :in-theory (enable make-code-addr))))

(defthm make-code-addr-cong16
  (implies (and (equal (loghead 16 offset1)
                       (loghead 16 offset2))
                (syntaxp (acl2::smaller-term offset2 offset1))
                )
           (equal (make-code-addr cenvr offset1)
                  (make-code-addr cenvr offset2)))
  :hints (("Goal" :in-theory (enable make-code-addr
                                     logapp ;bzo
                                     ))))

(defthm make-code-addr-cong16-lemma
  (implies (and (equal (loghead 16 offset1)
                       offset2)
                (syntaxp (acl2::smaller-term offset2 offset1))
                )
           (equal (make-code-addr cenvr offset1)
                  (make-code-addr cenvr offset2)))
  :hints (("Goal" :in-theory (enable make-code-addr
                                     logapp ;bzo
                                     ))))

;kill the other
(defthm make-code-addr-of-+-loghead-better
  (implies (and (integerp y1) (integerp y2))
           (equal (make-code-addr x (+ y1 (loghead 16 y2)))
                  (make-code-addr x (+ y1 y2))))
  :hints
  (("Goal" :in-theory (enable make-code-addr logapp))))

(defthm make-code-addr-subst-in-for-offset
  (implies (and (equal (loghead 16 y) z)
                (syntaxp (acl2::smaller-term z y))
                (integerp x)
                (integerp y)
                )
           (equal (MAKE-CODE-ADDR cenvr (+ x y))
                  (MAKE-CODE-ADDR cenvr (+ x z)))))

;bzo even if we prove this by closing things up, opening things may reveal good lemmas
(defthmd plus-make-code-addr
  (implies (and (unsigned-byte-p 16 (+ x pc))
                (unsigned-byte-p 16 pc)
                (unsigned-byte-p 16 ccenvr))
           (equal (+ x (make-code-addr ccenvr pc))
                  (make-code-addr ccenvr (+ x pc))))
  :hints (("Goal" :cases ((acl2-numberp x)) ;why suddenly needed?
           :in-theory (e/d (make-code-addr
                            acl2::logext-logapp
;         ACL2::LOGAPP-0-PART-2-BETTER
                            acl2::ASH-AS-LOGAPP ;think about this
                            )
                           (ACL2::LOGAPP-0-PART-2-BETTER)))))

;enable?
(defthmd ash-plus-make-code-addr2
  (implies (and (unsigned-byte-p 16 base)
                (unsigned-byte-p 16 offset)
                (integerp k)
                (unsigned-byte-p 16 (+ k offset)))
           (equal (+ (* 2 k) (ash (make-code-addr base offset) 1))
                  (ash (make-code-addr base (+ k offset)) 1)))
  :hints (("Goal" :use (:instance acl2::ash-plus-addr2 (acl2::k k) (acl2::addr (make-code-addr base offset)))
           :in-theory (enable plus-make-code-addr))))

(defthm logtail-16-of-make-code-addr
  (equal (logtail 16 (make-code-addr x y))
         (loghead 16 x) ;;(logext 16 x)
         )
  :hints (("Goal" :in-theory (e/d (acl2::logext-logapp
                                   make-code-addr)
                                  (
                                   acl2::logtail-logapp)))))

(defthm loghead-16-of-make-code-addr
  (equal (loghead 16 (make-code-addr x y))
         (loghead 16 y))
  :hints (("Goal" :in-theory (enable make-code-addr))))

(defthm equal-of-two-make-code-addrs-rewrite
  (equal (equal (make-code-addr cenvr2 offset2)
                (make-code-addr cenvr1 offset1))
         (and (equal (loghead 16 cenvr1) ;we could also talk about logexts here?
                     (loghead 16 cenvr2))
              (equal (loghead 16 offset1)
                     (loghead 16 offset2))))
  :hints (("Goal" :in-theory (enable make-code-addr-equal-rewrite))))

(defthm logtail-of-make-code-addr-hack
  (equal (logtail 17 (make-code-addr ccenvr offset1))
         ;;(logext 15 (acl2::logcdr ccenvr))
         (loghead 15 (acl2::logcdr ccenvr))
         )
  :hints (("Goal" :in-theory (enable make-code-addr ACL2::LOGEXT-LOGAPP))))

(defthm logtail15-of-make-code-addr
  (equal (logtail 15 (make-code-addr cenvr offset))
         ;; (logapp 1 (acl2::logbit 15 offset) (logext 16 cenvr))
         (logapp 1 (acl2::logbit 15 offset) (loghead 16 cenvr))
         )
  :hints (("Goal" :in-theory (e/d (make-code-addr ifix ACL2::LOGEXT-LOGAPP)
                                  (acl2::logext-logtail)))))

;; (defthm <-of-make-code-addr
;;   (implies (and (integerp x)
;;                 (integerp offset) ;drop?
;;                 )
;;            (equal (< (make-code-addr cenvr offset) x)
;;                   (if (logbitp 15 cenvr)
;;                       (or (< -1 (logtail 31 x))
;;                           (and (equal -1 (logtail 31 x))
;;                                (< (logapp 16 offset (loghead 15 cenvr))
;;                                   (loghead 31 x))))
;;                     (< (loghead 31 (logapp 16 offset cenvr)) x))))
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (e/d (make-code-addr logext acl2::logtail-loghead-better
;;                                             )
;;                                   (;equal-of-if
;;                                    acl2::loghead-logtail
;;                                    acl2::logext-logapp ;why?
;;                                    )))))

(defthm <-of-make-code-addr
  (implies (and (integerp x)
                (integerp offset) ;drop?
                )
           (equal (< (make-code-addr cenvr offset) x)
                  (< (loghead 32 (logapp 16 offset cenvr)) x)))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (make-code-addr logext acl2::logtail-loghead-better
                                            )
                                  (;equal-of-if
                                   acl2::loghead-logtail
                                   acl2::logext-logapp ;why?
                                   )))))


(defthm make-code-addr-chop-second-arg-when-constant
  (implies (and (syntaxp (quotep offset))
                (not (unsigned-byte-p 16 offset)))
           (equal (make-code-addr cenvr offset)
                  (make-code-addr cenvr (loghead 16 offset)))))

(defthm loghead-15-make-code-addr
  (implies (and (integerp y)
                (integerp x))
           (equal (loghead 15 (make-code-addr x y))
                  (loghead 15 y)))
  :hints (("Goal" :in-theory (enable make-code-addr))))


(defthm make-code-addr-plus-mult-16
  (implies  (and (syntaxp (not (quotep offset))) ;prevents loops
                 (integerp offset)
                 (integerp cenvr))
            (equal (MAKE-CODE-ADDR cenvr (+ 65536 offset))
                   (MAKE-CODE-ADDR cenvr offset)))
  :hints (("Goal" :in-theory (enable make-code-addr))))

(in-theory (disable MAKE-code-ADDR-OF-+-LOGHEAD)) ;looped!

(defthm make-code-addr-equal-same-env-rewrite
  (implies (and (integerp cenvr)
                (integerp offset1)
                (integerp offset2))
           (equal (EQUAL (MAKE-CODE-ADDR CENVR OFFSET2)
                         (MAKE-CODE-ADDR CENVR OFFSET1))
                  (EQUAL (LOGHEAD 16 OFFSET1)
                         (LOGHEAD 16 OFFSET2))))
  :hints (("Goal" :in-theory (enable make-code-addr))))

(defthm logcar-of-make-code-addr
  (equal (acl2::logcar (make-code-addr cenvr offset))
         (acl2::logcar offset))
  :hints (("Goal" :in-theory (enable make-code-addr))))

;; (defthm signed-byte-p-of-make-code-addr-fw
;;   (signed-byte-p 32 (make-code-addr cenvr offset))
;;   :rule-classes ((:forward-chaining :trigger-terms ((make-code-addr cenvr offset)))))

(defthm unsigned-byte-p-of-make-code-addr-fw
  (unsigned-byte-p 32 (make-code-addr cenvr offset))
  :rule-classes ((:forward-chaining :trigger-terms ((make-code-addr cenvr offset)))))

;; (defthm signed-byte-p-of-make-code-addr-better
;;   (implies (and (integerp n)
;;                 (<= 32 n))
;;            (signed-byte-p n (make-code-addr cenvr offset)))
;;   :hints (("Goal" :use (:instance signed-byte-p-of-make-code-addr)
;;            :in-theory (disable signed-byte-p-of-make-code-addr))))

(defthm unsigned-byte-p-of-make-code-addr-better
  (implies (and (integerp n)
                (<= 32 n))
           (unsigned-byte-p n (make-code-addr cenvr offset)))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-make-code-addr)
           :in-theory (disable unsigned-byte-p-of-make-code-addr))))

;can this (or the other one?) loop?
(defthm make-code-addr-cong16-cenvr
  (implies (and (equal (loghead 16 env1)
                       (loghead 16 env2))
                (syntaxp (acl2::smaller-term env2 env1)))
           (equal (make-code-addr env1 offset)
                  (make-code-addr env2 offset)))
  :hints (("Goal" :use ((:instance ACL2::LOGEXT-LOGHEAD (acl2::n 32) (acl2::m 32) (acl2::x  (* 65536 ENV1)))
                        (:instance ACL2::LOGEXT-LOGHEAD (acl2::n 32) (acl2::m 32) (acl2::x  (* 65536 ENV2))))
           :in-theory (e/d (make-code-addr logapp) (ACL2::LOGEXT-LOGHEAD)))))



;;
;;
;; MAKE-DATA-ADDR
;;
;;

;; Create a byte-address by concatenating a 15-bit data environment, DENVR,
;; onto a 16 bit offset, OFFSET, and then shifting the result one bit to the
;; left.  DENVR forms the most signficiant bits of the result.  See "Section
;; 2.1 MEMORY ADDRESSING" in the AAMP manual.
;;
;; Note that after logapp computes a 32-bit unsigned result, we sign-extend
;; that result to a signed 32-bit number.  This is because addresses in the
;; AAMP RAM are signed numbers (though perhaps we'll change that fact
;; later?). -ews
;;
;; we expect denvr to be a 15-bit value...
;; bzo add a guard and give this a fast body?
;;
;bzo could move the logext in?
(defund make-data-addr (denvr offset)
  (declare (type integer denvr offset))
  ;;(logext 32 (ash (logapp 16 offset denvr) 1))
  (loghead 32 (ash (logapp 16 offset denvr) 1))
  )

;; (defthm signed-byte-p-of-make-data-addr
;;   (signed-byte-p 32 (make-data-addr denvr offset))
;;   :hints (("Goal" :in-theory (enable make-data-addr))))

(defthm unsigned-byte-p-of-make-data-addr
  (unsigned-byte-p 32 (make-data-addr denvr offset))
  :hints (("Goal" :in-theory (enable make-data-addr))))

(defthm make-data-addr-when-offset-is-not-an-integerp
  (implies (not (integerp offset))
           (equal (make-data-addr denvr offset)
                  (make-data-addr denvr 0)))
  :hints (("Goal" :in-theory (enable make-data-addr))))

(defthm make-data-addr-when-denvr-is-not-an-integerp
  (implies (not (integerp denvr))
           (equal (make-data-addr denvr offset)
                  (make-data-addr 0 offset)))
  :hints (("Goal" :in-theory (enable make-data-addr))))

;generalize the 16?
(defthm make-data-addr-of-loghead-1
  (equal (make-data-addr (loghead 15 denvr) offset)
         (make-data-addr denvr offset))
  :hints (("Goal" :in-theory (enable make-data-addr acl2::logext-logapp))))

;generalize the 16?
(defthm make-data-addr-of-loghead-2
  (equal (make-data-addr denvr (loghead 16 offset))
         (make-data-addr denvr offset))
  :hints (("Goal" :in-theory (enable make-data-addr))))




;do we want this?
;this may have looped...
(defthm make-data-addr-of-+-loghead
  (implies (and (integerp y1)
                (integerp y2))
           (equal (make-data-addr x (+ y1 (loghead 16 y2)))
                  (make-data-addr x (loghead 16 (+ y1 y2))) ;further simplify this?
                  ))
  :hints (("Goal" :in-theory (enable make-data-addr logapp))))

;bzo
;weird.  do we still need this?
;; (defthm make-data-addr-of-make-data-addr
;;   (implies (and (integerp x) (integerp x2) (integerp y)  (integerp k))
;;            (equal (make-data-addr x (make-data-addr x2 y))
;;                   (make-data-addr x y)))
;;   :hints (("Goal" :in-theory (enable make-data-addr))))

;weird.  do we still need this?
;; (defthm make-data-addr-plus-hack
;;   (implies (and (integerp x) (integerp x2) (integerp y)  (integerp k))
;;            (equal (make-data-addr x (+ k (make-data-addr x2 y)))
;;                   (make-data-addr x (+ k y))))
;;   :hints (("Goal" :in-theory (enable make-data-addr))))

(defthm make-data-addr-cong16
  (implies (and (equal (loghead 16 offset1)
                       (loghead 16 offset2))
                (syntaxp (acl2::smaller-term offset2 offset1))
                )
           (equal (make-data-addr denvr offset1)
                  (make-data-addr denvr offset2)))
  :hints (("Goal" :in-theory (enable make-data-addr
                                     logapp ;bzo
                                     ))))

(defthm make-data-addr-cong16-lemma
  (implies (and (equal (loghead 16 offset1)
                       offset2)
                (syntaxp (acl2::smaller-term offset2 offset1))
                )
           (equal (make-data-addr denvr offset1)
                  (make-data-addr denvr offset2)))
  :hints (("Goal" :in-theory (enable make-data-addr
                                     logapp ;bzo
                                     ))))

;kill the other
(defthm make-data-addr-of-+-loghead-better
  (implies (and (integerp y1) (integerp y2))
           (equal (make-data-addr x (+ y1 (loghead 16 y2)))
                  (make-data-addr x (+ y1 y2))))
  :hints
  (("Goal" :in-theory (enable make-data-addr logapp))))

(defthm make-data-addr-subst-in-for-offset
  (implies (and (equal (loghead 16 y) z)
                (syntaxp (acl2::smaller-term z y))
                (integerp x)
                (integerp y)
                )
           (equal (MAKE-DATA-ADDR denvr (+ x y))
                  (MAKE-DATA-ADDR denvr (+ x z)))))

;bzo even if we prove this by closing things up, opening things may reveal good lemmas
;; (defthmd plus-make-data-addr
;;   (implies (and (unsigned-byte-p 16 (+ x pc))
;;                 (unsigned-byte-p 16 pc)
;;                 (unsigned-byte-p 16 cdenvr))
;;            (equal (+ x (make-data-addr cdenvr pc))
;;                   (make-data-addr cdenvr (+ x pc))))
;;   :hints (("Goal" :cases ((acl2-numberp x)) ;why suddenly needed?
;;            :in-theory (e/d (make-data-addr add32 lshl32 lshu
;;                                    ;         ACL2::LOGAPP-0-PART-2-BETTER
;;                                             acl2::ASH-AS-LOGAPP ;think about this
;;                                             )
;;                                   (ACL2::LOGAPP-0-PART-2-BETTER)))))

;enable?
;; (defthmd ash-plus-make-data-addr2
;;   (implies (and (unsigned-byte-p 16 base)
;;                 (unsigned-byte-p 16 offset)
;;                 (integerp k)
;;                 (unsigned-byte-p 16 (+ k offset)))
;;            (equal (+ (* 2 k) (ash (make-data-addr base offset) 1))
;;                   (ash (make-data-addr base (+ k offset)) 1)))
;;   :hints (("Goal" :use (:instance acl2::ash-plus-addr2 (acl2::k k) (acl2::addr (make-data-addr base offset)))
;;            :in-theory (enable plus-make-data-addr))))

(defthm make-data-addr-of-logext-gen
  (implies (and (integerp n)
                (<= 16 n))
           (equal (make-data-addr denvr (logext n offset))
                  (make-data-addr denvr offset)))
  :hints (("Goal" :use ((:instance make-data-addr-of-loghead-2)
                        (:instance make-data-addr-of-loghead-2 (offset (logext n offset))))
           :in-theory (disable make-data-addr-of-loghead-2))))

(defthm make-data-addr-of-sum-hack
  (implies (and (syntaxp (quotep a))
                (not (unsigned-byte-p 16 a))
                (integerp a)
                (integerp b)
                )
           (equal (make-data-addr denvr (+ a b))
                  (make-data-addr denvr (+ (loghead 16 a) b))))
  :hints (("Goal" :use ((:instance make-data-addr-of-loghead-2 (offset (+ a b)))
                        (:instance make-data-addr-of-loghead-2 (offset (+ (loghead 16 a) b)))
                        )
           :in-theory (disable make-data-addr-of-loghead-2))))

(defthm make-data-addr-chop-second-arg-when-constant
  (implies (and (syntaxp (quotep offset))
                (not (unsigned-byte-p 16 offset)))
           (equal (make-data-addr denvr offset)
                  (make-data-addr denvr (loghead 16 offset)))))

(defthm loghead-15-make-data-addr
  (implies (and (integerp y) (integerp x))
           (equal (loghead 15 (make-data-addr x y))
                  (ash (loghead 14 y) 1)))
  :hints (("Goal" :in-theory (enable make-data-addr))))

(defthm make-data-addr-plus-mult-16
  (implies  (and (syntaxp (not (quotep offset))) ;prevents loops
                 (integerp offset)
                 (integerp denvr))
            (equal (MAKE-DATA-ADDR denvr (+ 65536 offset))
                   (MAKE-DATA-ADDR denvr offset)))
  :hints (("Goal" :in-theory (enable make-data-addr))))




(in-theory (disable make-data-addr-OF-+-LOGHEAD)) ;looped!

(defthm make-data-addr-equal-same-env-rewrite
  (implies (and (integerp denvr)
                (integerp offset1)
                (integerp offset2))
           (equal (EQUAL (MAKE-DATA-ADDR DENVR OFFSET2)
                         (MAKE-DATA-ADDR DENVR OFFSET1))
                  (EQUAL (LOGHEAD 16 OFFSET1)
                         (LOGHEAD 16 OFFSET2))))
  :hints (("Goal" :in-theory (enable make-data-addr))))


(defthm logcar-of-make-data-addr
  (equal (acl2::logcar (make-data-addr denvr offset))
         0)
  :hints (("Goal" :in-theory (enable make-data-addr))))

;; (defthm signed-byte-p-of-make-data-addr-fw
;;   (signed-byte-p 32 (make-data-addr denvr offset))
;;   :rule-classes ((:forward-chaining :trigger-terms ((make-data-addr denvr offset)))))

(defthm unsigned-byte-p-of-make-data-addr-fw
  (unsigned-byte-p 32 (make-data-addr denvr offset))
  :rule-classes ((:forward-chaining :trigger-terms ((make-data-addr denvr offset)))))

(defthm unsigned-byte-p-of-make-data-addr-better
  (implies (and (integerp n)
                (<= 32 n))
           (unsigned-byte-p n (make-data-addr denvr offset)))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-make-data-addr)
           :in-theory (disable unsigned-byte-p-of-make-data-addr))))

(defthm evenp-of-make-data-addr
  (evenp (make-data-addr denvr offset))
  :hints (("Goal" :in-theory (enable make-data-addr))))

;bzo
(DEFTHM ODD-<-EVEN-TIGHTEN-alt
  (IMPLIES (AND; (INTEGERP ACL2::I)
               ; (INTEGERP ACL2::J)
                (evenp i)
                (evenp j)
                )
           (EQUAL (< (+ 1 j) i)
                  (< j i)))
  :hints (("Goal" :use (:instance acl2::ODD-<-EVEN-TIGHTEN (acl2::j (/ j 2)) (acl2::i (/ i 2)))
           :in-theory (disable acl2::ODD-<-EVEN-TIGHTEN))))


;can this (or the other one?) loop?
(defthm make-data-addr-cong16-denvr
  (implies (and (equal (loghead 15 env1)
                       (loghead 15 env2))
                (syntaxp (acl2::smaller-term env2 env1)))
           (equal (make-data-addr env1 offset)
                  (make-data-addr env2 offset)))
  :hints (("Goal" :use ((:instance ACL2::LOGEXT-LOGHEAD (acl2::n 32) (acl2::m 32) (acl2::x  (* 65536 ENV1)))
                        (:instance ACL2::LOGEXT-LOGHEAD (acl2::n 32) (acl2::m 32) (acl2::x  (* 65536 ENV2))))
           :in-theory (e/d (make-data-addr logapp) (ACL2::LOGEXT-LOGHEAD)))))

;; (if (logbitp 15 denvr)
;;                       (or (< -1 (logtail 31 x))
;;                           (and (equal -1 (logtail 31 x))
;;                                (< (logapp 16 offset (loghead 15 denvr))
;;                                   (loghead 31 x))))
;;                     (< (loghead 31 (logapp 16 offset denvr)) x))

;simplify more?
;; (defthm <-of-make-data-addr
;;   (implies (and (integerp x)
;;                 (integerp offset) ;drop?
;;                 )
;;            (equal (< (make-data-addr denvr offset) x)
;;                   (if (ACL2::LOGBITP 14 DENVR)
;;                       (< (ASH (LOGAPP 30 (LOGAPP 16 OFFSET DENVR) -1)
;;                               1)
;;                          X)
;;                     (< (ASH (LOGAPP 16 OFFSET (LOGHEAD 14 DENVR))
;;                             1)
;;                        X)
;;                     )))
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (e/d (make-data-addr logext acl2::logtail-loghead-better
;;                                                   )
;;                                   ( ;equal-of-if
;;                                    acl2::loghead-logtail
;;                                    acl2::logext-logapp ;why?
;;                                    )))))

(defthm <-of-make-data-addr
  (implies (and (integerp x)
                (integerp offset) ;drop?
                )
           (equal (< (make-data-addr denvr offset) x)
                  (< (ASH (LOGAPP 16 OFFSET (LOGHEAD 15 DENVR))
                            1)
                       X)))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (make-data-addr logext acl2::logtail-loghead-better
                                                  )
                                  ( ;equal-of-if
                                   acl2::loghead-logtail
                                   acl2::logext-logapp ;why?
                                   )))))

(defthm logtail-16-of-make-data-addr
  (equal (logtail 16 (make-data-addr x y))
         (logapp 1 (acl2::logbit 15 y) (loghead 15 x) ;(logext 15 x)
                 ))
  :hints (("Goal" :cases ((integerp x))
                          :in-theory (e/d (make-data-addr acl2::logext-logapp)
                                  (acl2::logtail-logapp)))))


(defthm loghead-16-of-make-data-addr
  (equal (loghead 16 (make-data-addr x y))
         (ash (loghead 15 y) 1))
  :hints (("Goal" :in-theory (enable make-data-addr))))

;; (defthm equal-of-two-make-data-addrs-rewrite
;;   (equal (equal (make-data-addr ddenvr2 offset2)
;;                 (make-data-addr ddenvr1 offset1))
;;          (and (equal (loghead 16 ddenvr1) ;we could also talk about logexts here?
;;                      (loghead 16 ddenvr2))
;;               (equal (loghead 16 offset1)
;;                      (loghead 16 offset2))))
;;   :hints (("Goal" :in-theory (enable make-data-addr-equal-rewrite))))

(defthm logtail-of-make-data-addr-hack
  (equal (logtail 17 (make-data-addr denvr offset1))
         (loghead 15 denvr); (logext 15 denvr)
         )
  :hints (("Goal" :in-theory (enable make-data-addr ACL2::LOGEXT-LOGAPP))))

;; (defthm logtail15-of-make-data-addr
;;   (equal (logtail 15 (make-data-addr denvr offset))
;;          (logapp 1 (acl2::logbit 15 offset) (logext 16 denvr)))
;;   :hints (("Goal" :in-theory (e/d (make-data-addr ifix ACL2::LOGEXT-LOGAPP)
;;                                   (acl2::logext-logtail)))))

(defthm loghead16-logcdr-make-data-addr
  (equal (loghead 16 (acl2::logcdr (make-data-addr denvr offset)))
         (loghead 16 offset))
  :hints (("Goal" :in-theory (enable make-data-addr))))

;zz4









;;
;; FETCH-CODE-BYTE
;;

;; bzo have Hardin check this.

;;Fetch the byte at offset OFFSET in code environment CENVR in ram RAM.
(defund fetch-code-byte (cenvr offset ram)
  (declare (type integer cenvr offset)
           (xargs :guard (aamp-ramp ram))
           )
  (rd (make-code-addr cenvr offset) ram) ;old: (rx 8 (make-code-addr cenvr offset) ram)
  )

(defthm fetch-code-byte-when-offset-is-not-an-integerp
  (implies (not (integerp offset))
           (equal (fetch-code-byte cenvr offset ram)
                  (fetch-code-byte cenvr 0 ram)))
  :hints (("Goal" :in-theory (enable fetch-code-byte))))

(defthm fetch-code-byte-when-cenv-is-not-an-integerp
  (implies (not (integerp cenvr))
           (equal (fetch-code-byte cenvr offset ram)
                  (fetch-code-byte 0 offset ram)))
  :hints (("Goal" :in-theory (enable fetch-code-byte))))

;bzo improve in the usual way -ews
(defthm usb8-of-fetch-code-byte
  (unsigned-byte-p 8 (fetch-code-byte cenvr offset ram))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((fetch-code-byte cenvr offset ram))))
  :hints (("Goal" :in-theory (enable fetch-code-byte))))

(defthm fetch-code-byte-of-loghead
  (equal (fetch-code-byte cenvr (loghead 16 offset) ram)
         (fetch-code-byte cenvr offset ram))
  :hints (("Goal" :in-theory (enable fetch-code-byte))))

(defthm fetch-code-byte-of-loghead-2
  (equal (fetch-code-byte (loghead 16 cenvr) offset ram)
         (fetch-code-byte cenvr offset ram))
  :hints (("Goal" :in-theory (enable fetch-code-byte))))


;;
;; FETCH-CODE-BYTES
;;

(defthm address-listp-of-loghead-list-32
  (implies (and (mem::memory-p ram)
                (equal (mem::size ram) 4294967296))
           (address-listp (loghead-list 32 vals) ram)))

;bzo handle this better. ADDRESS-LISTP is basically usb-list?
(defthm address-listp-of-logapp-list-of-loghead
  (implies (and (mem::memory-p ram)
                (equal (mem::size ram) 4294967296))
           (ADDRESS-LISTP (LOGAPP-LIST 16
                                       (OFFSET-RANGE-WRAP 16 OFFSET NUMBYTES)
                                       (LOGHEAD 16 CENVR))
                          RAM))
  :hints (("Goal" :in-theory (e/d (LOGAPP-LIST-OF-LOGHEAD) (LOGHEAD-LIST-OF-LOGAPP-LIST)))))

;;Fetch NUMBYTES bytes, starting at offset OFFSET in code environment CENVR in ram RAM.
;;This returns a bit vector (that is, a big number).

;;Note that the behavior of this function involves wrapping around; that is,
;;if we reach the end of the code environment, we start reading from the
;;begining of that same environment, not from the next environment.

;;All the calls to loghead and fix below could make this slow, so we could use
;;mbe to give this a fast body. -ews

;; bzo have Hardin check this.

;; Bbzo redo this to call RD-LIST?

;;bzo make this tail recursive?  or redo things to prevent 3 calls when numbytes is 2.

;bzo make a fast executable body..
;recently reordered the params on this

;bzo fast body
;think about guard
;bzo wrap the list of addresses up into a nice function?
;bzo could move the logext-list in?
(defun fetch-code-bytes (numbytes cenvr offset ram)
  (declare (type integer cenvr offset)
           (type (integer 0 *) numbytes)
           (xargs :guard (aamp-ramp ram)))
  (wintlist
   (rd-list ;;(logext-list 32 (logapp-list 16 (offset-range-wrap 16 offset numbytes) cenvr))
    (loghead-list 32 (logapp-list 16 (offset-range-wrap 16 offset numbytes) cenvr))
    ram)))

(defthm fetch-code-bytes-when-numbytes-is-non-positive
  (implies (<= numbytes 0)
           (equal (fetch-code-bytes numbytes cenvr offset ram)
                  0))
  :hints (("Goal" :in-theory (enable fetch-code-bytes))))

(defthm fetch-code-bytes-when-numbytes-is-1
  (equal (fetch-code-bytes 1 cenvr offset ram)
         (fetch-code-byte cenvr offset ram))
  :hints (("Goal" :expand (fetch-code-bytes 1 cenvr offset ram)
           :in-theory (enable fetch-code-bytes fetch-code-byte make-code-addr))))

;bzo fix this! - huh?
(defthm fetch-code-bytes-when-offset-is-not-an-integerp
  (implies (not (integerp offset))
           (equal (fetch-code-bytes numbytes cenvr offset ram)
                  (fetch-code-bytes numbytes cenvr (ifix offset) ram)))
  :hints (("Goal" :in-theory (e/d (fetch-code-bytes ifix) (FETCH-CODE-BYTE)))))

(defthm fetch-code-bytes-when-cenv-is-not-an-integerp
  (implies (not (integerp cenvr))
           (equal (fetch-code-bytes numbytes cenvr offset ram)
                  (fetch-code-bytes numbytes 0 offset ram)))
  :hints (("Goal" :in-theory
           (e/d (fetch-code-bytes ifix)
                (fetch-code-byte)))))

;bzo put a limit on this to prevent huge expansions (like the limit on read-data-words-opener)?
(defthmd fetch-code-bytes-opener
  (implies (and (syntaxp (quotep numbytes))
                (not (zp numbytes)))
           (equal (fetch-code-bytes numbytes cenvr offset ram)
                  (logapp 8
                          (fetch-code-byte cenvr (loghead 16 offset) ram)
                          (fetch-code-bytes (+ -1 (ifix numbytes))
                                            cenvr
                                            (loghead 16 (+ 1 (ifix offset)))
                                            ram))))
  :hints (("Goal" :expand ((OFFSET-RANGE-WRAP 16 OFFSET NUMBYTES) ;bzo
                           (OFFSET-RANGE-WRAP 16 0 NUMBYTES))
           :in-theory (enable fetch-code-bytes
                                     fetch-code-byte
                                     make-code-addr))))




;bzo will the multiplication get done during forward-chaining?
(defthm unsigned-byte-p-of-fetch-code-bytes
  (implies (and (integerp numbytes)
                (<= 0 numbytes))
           (unsigned-byte-p (* 8 numbytes) (fetch-code-bytes numbytes cenvr offset ram)))
  :rule-classes ((:forward-chaining :trigger-terms ((fetch-code-bytes numbytes cenvr offset ram))))
  :hints (("Goal" :in-theory (enable fetch-code-bytes))))

(defthm unsigned-byte-p-of-fetch-code-bytes-gen
  (implies (and (<= (* 8 numbytes) n)
                (integerp numbytes)
                (<= 0 numbytes)
                )
           (equal (unsigned-byte-p n (fetch-code-bytes numbytes cenvr offset ram))
                  (integerp n))))

(defthm fetch-code-bytes-of-loghead
  (equal (fetch-code-bytes numbytes cenvr (loghead 16 offset) ram)
         (fetch-code-bytes numbytes cenvr offset ram))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable fetch-code-bytes zp))))

(defthm fetch-code-bytes-of-loghead-2
  (equal (fetch-code-bytes numbytes (loghead 16 cenvr) offset ram)
         (fetch-code-bytes numbytes cenvr offset ram))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (fetch-code-bytes zp LOGAPP-LIST-OF-LOGHEAD) (LOGHEAD-LIST-OF-LOGAPP-LIST)))))

(defthm loghead-8-of-fetch-code-bytes-better
  (equal (loghead 8 (fetch-code-bytes numbytes cenvr offset ram))
         (if (zp numbytes)
             0
           (fetch-code-byte cenvr offset ram)))
  :hints (("Goal" :in-theory (enable fetch-code-bytes fetch-code-byte make-code-addr ;firstn
                                     ))))

(defthm fetch-code-bytes-simp-constant-offset
  (implies (and (syntaxp (quotep offset))
                (not (unsigned-byte-p 16 offset)))
           (equal (fetch-code-bytes numbytes cenvr offset ram)
                  (fetch-code-bytes numbytes cenvr (loghead 16 offset) ram)))
  :hints (("Goal" :use ((:instance FETCH-CODE-BYTES-OF-LOGHEAD (offset (logext 16 offset)))
                        (:instance FETCH-CODE-BYTES-OF-LOGHEAD))
           :in-theory (disable FETCH-CODE-BYTES-OF-LOGHEAD))))

;helps us prove fetch-code-bytes of loghead lemmas
(defthm fetch-code-bytes-agree-when-logheads-agree
  (implies (and (equal (loghead 16 offset1) (loghead 16 offset2))
                (integerp offset1)
                (integerp offset2))
           (equal (equal (gacc::fetch-code-bytes numbytes cenvr offset1 ram)
                         (gacc::fetch-code-bytes numbytes cenvr offset2 ram))
                  t))
  :hints (("Goal" :use ((:instance gacc::fetch-code-bytes-of-loghead
                                   (gacc::offset offset1)
                                   (gacc::numbytes numbytes)
                                   (gacc::cenvr cenvr)
                                   (gacc::ram ram)
                                   )
                        (:instance gacc::fetch-code-bytes-of-loghead
                                   (gacc::offset offset2)
                                   (gacc::numbytes numbytes)
                                   (gacc::cenvr cenvr)
                                   (gacc::ram ram)))
           :in-theory (disable gacc::fetch-code-bytes-of-loghead))))

;bzo
(defthm fetch-code-bytes-normalize-leading-constant
  (implies (and (syntaxp (and (quotep k) (not (unsigned-byte-p 16 (cadr k)))))
                (integerp k)
                (integerp offset))
           (equal (gacc::fetch-code-bytes numbytes cenvr (+ k offset) ram)
                  (gacc::fetch-code-bytes numbytes cenvr (+ (loghead 16 k) offset) ram))))

(defthm fetch-code-bytes-sum-subst
  (implies (and (equal (loghead 16 x) y)
                (syntaxp (acl2::smaller-term y x))
                (integerp x)
                (integerp y)
                (integerp n)
                )
           (equal (fetch-code-bytes numbytes cenvr (+ x n) ram)
                  (fetch-code-bytes numbytes cenvr (+ y n) ram)))
  :hints (("Goal" :in-theory (disable fetch-code-bytes-of-loghead)
           :use ((:instance fetch-code-bytes-of-loghead (offset (+ n (loghead 16 x))))
                 (:instance fetch-code-bytes-of-loghead (offset (+ n x)))))))

(defthm fetch-code-bytes-sum-subst-alt
  (implies (and (equal (loghead 16 x) y)
                (syntaxp (acl2::smaller-term y x))
                (integerp x)
                (integerp y)
                (integerp n)
                )
           (equal (fetch-code-bytes numbytes cenvr (+ n x) ram)
                  (fetch-code-bytes numbytes cenvr (+ n y) ram)))
  :hints (("Goal" :in-theory (disable fetch-code-bytes-of-loghead)
           :use ((:instance fetch-code-bytes-of-loghead (offset (+ n (loghead 16 x))))
                 (:instance fetch-code-bytes-of-loghead (offset (+ n x)))))))

(defthm fetch-code-bytes-sum-lemma
  (implies (and (integerp y)
                (integerp n)
                )
           (equal (fetch-code-bytes numbytes cenvr (+ n (loghead 16 y)) ram)
                  (fetch-code-bytes numbytes cenvr (+ n y) ram)))
  :hints (("Goal" :in-theory (disable fetch-code-bytes-of-loghead)
           :use ((:instance fetch-code-bytes-of-loghead (offset (+ n (loghead 16 y))))
                 (:instance fetch-code-bytes-of-loghead (offset (+ n y)))))))


(defun fetch-code-bytes-n-induct (numbytes offset n)
  (if (zp numbytes)
      (+ n offset)
    (fetch-code-bytes-n-induct (1- numbytes)  (+ 1 (loghead 16 offset))  (1- n))))







;will the (* 8 n) in the LHS sometimes prevent this from firing?
(defthm logtail-8n-fetch-code-bytes
  (implies (and (< n numbytes) ;gen?
                (<= 0 n)
                (integerp n)
                )
           (equal (logtail (* 8 n) (fetch-code-bytes numbytes cenvr offset ram))
                  (fetch-code-bytes (- numbytes n) cenvr (+ n (ifix offset)) ram)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand (fetch-code-bytes numbytes cenvr offset ram)
           :induct (fetch-code-bytes-n-induct numbytes offset n)
           :in-theory (enable fetch-code-bytes
                              FETCH-CODE-BYTE))))


;;
;; NO-CODE-DATA-CLASH
;;

;;says that the 15-bit data environment pointer DENVR doesn't equal the high 15
;;bits of the code environment pointer CENV.  Eric hopes to make this the key
;;fact that lets us conclude that code and data accesses don't interfere.
;bzo make a code-data-clash... instead of no-code-data-clash ?
(defund no-code-data-clash (cenvr denvr)
  (declare (type integer cenvr denvr))
  (not (equal (acl2::logcdr (loghead 16 cenvr)) ;add a loghead here?
              (loghead 15 denvr))))



;;
;; FETCH-CODE-BYTES-LIST
;;

;bzo add guard
(defund fetch-code-bytes-list (numbytes cenvr offset ram)
  (enlistw numbytes (fetch-code-bytes numbytes cenvr offset ram)))

(defthm fetch-code-bytes-list-of-loghead16
  (equal (fetch-code-bytes-list len cenvr (loghead 16 offset) ram)
         (fetch-code-bytes-list len cenvr offset ram))
  :hints (("Goal" :in-theory (enable fetch-code-bytes-list))))

;bzo redo this...
;i expect off-offset to be a small integer.
(defthm use-fetch-code-bytes-list-1
  (implies (and (equal prog (fetch-code-bytes-list numbytes cenvr offset ram)) ;prog and numbytes are free vars
                (< (loghead 16 (- ad offset)) numbytes)
                (unsigned-byte-p 16 offset) ;drop?
;                (integerp offset)
                (integerp numbytes)
                (integerp ad)
                )
           (equal (rd (make-code-addr cenvr ad) ram)
                  (nth (loghead 16 (- ad offset)) prog)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable fetch-code-byte fetch-code-bytes-list make-code-addr))))

(defthm use-fetch-code-bytes-list-2
  (implies (and (equal prog (fetch-code-bytes-list numbytes cenvr offset ram)) ;prog and numbytes are free vars
                (< (loghead 16 (- ad offset)) numbytes)
                (integerp offset)
                (integerp numbytes)
                (integerp ad)
                )
           (equal (rd (make-code-addr cenvr ad) ram)
                  (nth (loghead 16 (- ad offset)) prog)))
  :hints (("Goal" :in-theory (e/d (ifix fetch-code-bytes-list) (use-fetch-code-bytes-list-1))
           :use (:instance use-fetch-code-bytes-list-1 (offset (loghead 16 offset))))))

(defthm use-fetch-code-bytes-list-4
  (implies (and (equal prog (fetch-code-bytes-list numbytes cenvr offset ram)) ;prog and numbytes are free vars
                (< (loghead 16 (- ad offset)) numbytes)
                (integerp offset)
                (integerp numbytes)
                (integerp ad)
                )
           (equal (fetch-code-byte cenvr ad ram)
                  (nth (loghead 16 (- ad offset)) prog)))
  :hints (("Goal" :in-theory (e/d (ifix fetch-code-byte
                                        ;rx-to-rd
                                        fetch-code-bytes-list)
                                  (use-fetch-code-bytes-list-1))
           :use (:instance use-fetch-code-bytes-list-1 (offset (loghead 16 offset))))))

;eventually don't go to addr range?
;gen
;bzo remove the stuff that mentions addr-range?
;; (defthm disjoint-of-addr-ranges-of-make-data-addrs
;;   (implies (and (integerp denvr)
;;                 (integerp offset1)
;;                 (integerp offset2))
;;            (equal (bag::disjoint (addr-range (make-data-addr denvr offset1) 2)
;;                                  (addr-range (make-data-addr denvr offset2) 2))
;;                   (not (equal (loghead 16 offset1) (loghead 16 offset2)))))
;;   :hints (("Goal" :in-theory (e/d (disjoint-of-two-addr-ranges
;;                                    logext ;bzo disable and get lemmas!
;;                                    ash
;;                                    ;makeaddr
;;                                    ACL2::LOGTAIL-LOGHEAD-BETTER
;;                                    MAKE-data-ADDR
;;                                    )
;;                                   ( ;acl2::<-of-ash
;;                                    acl2::loghead-logtail
;;                                    acl2::extend-<
;;                                    MAKE-data-ADDR-CONG16
;;                                    )))))

(defthm code-addr-isnt-one-plus-data-addr
  (implies (no-code-data-clash cenvr denvr)
           (not (equal (make-code-addr cenvr offset)
                       (+ 1 (make-data-addr denvr offset2)))))
  :hints (("Goal" :in-theory (enable no-code-data-clash
                                     make-code-addr-equal-rewrite
                                     ;make-data-addr
                                     ))))

(defthm logcdr-of-code-addr-isnt-data-addr
  (implies (no-code-data-clash cenvr denvr)
           (not (equal (make-code-addr cenvr offset)
                       (make-data-addr denvr offset2))))
  :hints (("Goal" :in-theory (enable no-code-data-clash
                                     make-code-addr-equal-rewrite
                                     ))))



(defthm not-equal-code-addr-data-addr
  (implies (and (no-code-data-clash cenvr denvr)
;                (integerp offset)
                (integerp cenvr)
                (integerp offset2)
                (integerp denvr)
                )
           (not (equal (make-code-addr cenvr offset)
                       (make-data-addr denvr offset2))))
  :hints (("Goal" :in-theory (enable acl2::equal-to-ash-1-rewrite
                                     NO-CODE-DATA-CLASH
                                     ))))

(defthm fetch-code-byte-of-write-data-word
  (implies (no-code-data-clash cenvr denvr)
           (equal (fetch-code-byte cenvr offset (write-data-word ;write-data-word
                                                denvr offset2 val ram))
                  (fetch-code-byte cenvr offset ram)))
  :hints (("Goal" :in-theory (enable write-data-word
;                                     rx-to-rd
                                     make-code-addr
                                     WORD-AD-TO-BYTE-ADS
                                     fetch-code-byte no-code-data-clash))))



;; (defthm fetch-code-byte-of-write-data-words
;;   (implies (no-code-data-clash cenvr denvr)
;;            (equal (fetch-code-byte cenvr offset (write-data-words ;write-data-words
;;                                                 numwords denvr offset2 val ram))
;;                   (fetch-code-byte cenvr offset ram)))
;;   :hints (("Goal" :in-theory (enable write-data-words
;;                                      WORD-AD-TO-BYTE-ADS
;;                                      make-code-addr
;;                                      fetch-code-byte
;;                                      rx-to-rd
;;                                      ))))

;bzo gen this!  see above
(defthm fetch-code-byte-of-write-data-words
  (implies (no-code-data-clash cenvr denvr)
           (equal (fetch-code-byte cenvr offset (write-data-words ;write-data-words
                                                 2 ;numwords
                                                 denvr offset2 val ram))
                  (fetch-code-byte cenvr offset ram)))
  :hints (("Goal" :in-theory (e/d (write-data-words
                                   acl2::logext-logapp
                                   WORD-AD-TO-BYTE-ADS
                                   make-code-addr
                                   fetch-code-byte
;                                     rx-to-rd
                                   OFFSET-RANGE-WRAP-CONST-OPENER
                                   NO-CODE-DATA-CLASH
                                   )
                                  (WRITE-DATA-WORDS-OPENER)))))


;;  (defthm disjoint-of-data-addr-ranges-when-offs-differ
;;    (implies (not (equal (loghead 16 offset1) (loghead 16 offset2)))
;;             (BAG::DISJOINT (ADDR-RANGE (MAKE-data-ADDR DENVR1 OFFSET1) 2)
;;                            (ADDR-RANGE (MAKE-data-ADDR DENVR2 OFFSET2) 2)))
;;    :hints (("Goal" :use (:instance disjoint-of-data-addr-ranges-when-offs-differ-helper (denvr2 (ifix denvr2)) (denvr1 (ifix denvr1)) (offset1 (ifix offset1)) (offset2 (ifix offset2)))
;;             :in-theory (disable disjoint-of-data-addr-ranges-when-offs-differ-helper
;;                                 DISJOINT-OF-TWO-ADDR-RANGES)))))



;; (defthm disjoint-of-data-addr-ranges-when-denvrs-differ
;;   (implies (and (not (equal (loghead 15 denvr1) (loghead 15 denvr2)))
;;                 )
;;            (bag::disjoint (addr-range (make-data-addr denvr1 offset1)
;;                                             2)
;;                           (addr-range (make-data-addr denvr2 offset2)
;;                                             2)))
;;   :hints (("Goal" :in-theory (e/d (MAKE-DATA-ADDR-EQUAL-REWRITE
;;                                    disjoint-of-two-addr-ranges)
;;                                   (<-OF-MAKE-DATA-ADDR)))))


;; (defthm loghead-list-of-word-ads-to-byte-ads-hack
;;   (implies (unsigned-byte-p-list 31 word-ads)
;;            (equal (loghead-list 32 (word-ads-to-byte-ads word-ads))
;;                   (word-ads-to-byte-ads word-ads)))
;;   :hints (("Goal" :in-theory (enable word-ads-to-byte-ads
;;                                      word-ad-to-byte-ads
;;                                      ))))



;The :instance hints were needed because of stuff like this:
;; 2x (:REWRITE HACK-FOR-CODE-DATA-CLASH) failed because :HYP 1 is judged
;; more complicated than its ancestors (type :ANCESTORS to see the ancestors
;; and :PATH to see how we got to this point).
;; 2)
;; -ews
(defthm fetch-code-bytes-of-write-data-word
  (implies (no-code-data-clash cenvr denvr)
           (equal (fetch-code-bytes numbytes cenvr offset1 (write-data-word denvr offset2 val ram))
                  (fetch-code-bytes numbytes cenvr offset1 ram)))
  :hints (("Goal" :use ((:instance hack-for-code-data-clash (denvr ;(LOGEXT '31 (LOGAPP '16 OFFSET2 DENVR))
                                                             (LOGhead '31 (LOGAPP '16 OFFSET2 DENVR))
                                                             )
                                   (cenvs (LOGAPP-LIST '16
                                                       (OFFSET-RANGE-WRAP 16 OFFSET1 NUMBYTES)
                                                       (LOGhead '16 CENVR) ;(LOGEXT '16 CENVR)
                                                       )
                                          ))
                        (:instance hack-for-code-data-clash2 (denvr ;(LOGEXT '31 (LOGAPP '16 OFFSET2 DENVR))
                                                              (LOGhead '31 (LOGAPP '16 OFFSET2 DENVR))
                                                              )
                                   (cenvs (LOGAPP-LIST '16
                                                       (OFFSET-RANGE-WRAP 16 OFFSET1 NUMBYTES)
                                                       (LOGhead '16 CENVR) ;(LOGEXT '16 CENVR)
                                                       )
                                          )))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (fetch-code-bytes write-data-word WORD-AD-TO-BYTE-ADS
                                             NO-CODE-DATA-CLASH
                                             )
                           (hack-for-code-data-clash
                            hack-for-code-data-clash2
                            ;ACL2::ASSOCIATIVITY-OF-LOGAPP-BETTER
                            ACL2::LOGAPP-0-PART-2-BETTER)))))

(defthm fetch-code-bytes-list-of-write-data-word
  (implies (no-code-data-clash cenvr denvr)
           (equal (fetch-code-bytes-list numbytes cenvr offset1 (write-data-word denvr offset2 val ram))
                  (fetch-code-bytes-list numbytes cenvr offset1 ram)))
  :hints (("Goal" :in-theory (enable fetch-code-bytes-list))))

(defthm fetch-code-bytes-list-of-write-data-words-irrel
  (implies (no-code-data-clash cenvr denvr)
           (equal (fetch-code-bytes-list numbytes cenvr offset1 (write-data-words numwords denvr offset2 val ram))
                  (fetch-code-bytes-list numbytes cenvr offset1 ram)))
  :hints (("Goal" :in-theory (enable fetch-code-bytes-list
                                     fetch-code-bytes ;bzo
                                     write-data-words
                                     no-code-data-clash
                                     disjoint-of-WORD-AD-TO-BYTE-ADS
                                     disjoint-of-word-ads-to-byte-ads
                                     ))))

;(in-theory (disable BAG::SUBBAG-BY-MULTIPLICITY))

(defthm fetch-code-byte-of-sum-of-loghead-two
  (implies (and (integerp off1)
                (integerp off2))
           (equal (fetch-code-byte cenvr (+ off1 (loghead 16 off2)) ram)
                  (fetch-code-byte cenvr (+ off1 off2) ram)))
  :hints (("Goal" :in-theory (enable fetch-code-byte
                                     MAKE-CODE-ADDR ;bzo
                                     ))))

(defthm fetch-code-byte-of-sum-of-loghead-one
  (implies (and (integerp off1)
                (integerp off2))
           (equal (fetch-code-byte cenvr (+ (loghead 16 off2) off1) ram)
                  (fetch-code-byte cenvr (+ off1 off2) ram)))
  :hints (("Goal" :use (:instance  fetch-code-byte-of-sum-of-loghead-two)
           :in-theory (disable  fetch-code-byte-of-sum-of-loghead-two))))


(local (in-theory (disable ACL2::LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT)))


(defthm fetch-code-byte-of-write-data-word-bag-phrasing
  (implies (not (memberp (make-code-addr cenvr offset) (addresses-of-data-word denvr offset2)))
           (equal (fetch-code-byte cenvr offset (write-data-word denvr offset2 val ram))
                  (fetch-code-byte cenvr offset ram)))
  :hints (("Goal" :in-theory (e/d (write-data-word
                                   fetch-code-byte
                                   )
                                  (ADDRESSES-OF-DATA-WORD)))))

(defthm fetch-code-byte-of-clear-data-word-bag-phrasing
  (implies (not (memberp (make-code-addr cenvr offset) (addresses-of-data-word denvr offset2)))
           (equal (fetch-code-byte cenvr offset (clear-data-word denvr offset2 ram))
                  (fetch-code-byte cenvr offset ram)))
  :hints (("Goal" :in-theory (e/d (clear-data-word) (write-data-word-equal-rewrite)))))

(defun read-data-words-induct (numwords offset)
  (if (zp numwords)
      (list numwords offset)
    (read-data-words-induct (+ -1 numwords) (+ 1 (ifix offset)))))



;; ;bzo make this local !
;;  (defthm read-data-word-of-write-data-words-same-gen
;;    (implies (and (< (loghead 16 offset) (+ numwords (loghead 16 offset2)))
;;                  (<= (loghead 16 offset2) (loghead 16 offset)) ;bzo drop?
;;                  (integerp offset2)
;;                  (integerp numwords)
;;                  )
;;             (equal (read-data-word denvr offset (write-data-words numwords denvr offset2 value ram))
;;                    (nthword (- (loghead 16 offset) (loghead 16 offset2)) value)))
;;    :hints (("Goal" :in-theory (disable read-data-word-of-write-data-words-same )
;;             :use (:instance  read-data-word-of-write-data-words-same
;;                              (offset (loghead 16 offset))
;;                              (offset2 (loghead 16 offset2)))))))

(defthm loghead-16-of-diff-equals-0
  (implies (and (EQUAL (LOGHEAD 16 OFFSET) (LOGHEAD 16 OFFSET2))
                (integerp OFFSET)
                (integerp OFFSEt2))
           (equal (LOGHEAD 16 (+ OFFSET (- OFFSET2)))
                  0))
  :hints (("Goal" :in-theory (enable acl2::loghead-of-minus
                                     ACL2::LOGHEAD-SUM-SPLIT-INTO-2-CASES)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil))))



(defun read-data-words-induct-with-n (numwords offset n)
  (if (zp numwords)
      (list numwords offset n)
      (read-data-words-induct-with-n (+ -1 numwords)
                                     (+ 1 (ifix offset))
                                     (+ -1 n)
                                     )))

;make a both version?
;rename to have a same including same?
(defthm nthword-of-read-data-words
  (implies (and (<= 0 n)
                (< n numwords)
                (integerp n)
                (integerp offset2)
                (integerp offset)
                (integerp numwords)
                )
           (equal (NTHWORD n (READ-DATA-WORDS numwords denvr offset ram))
                  (read-data-word denvr (+ n offset) ram)))
  :hints (("subgoal *1/2"
           :expand (NTHWORD N
                            (READ-DATA-WORDS NUMWORDS DENVR OFFSET RAM))
           :in-theory (disable WRITE-DATA-WORDS-OPENER))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (read-data-words-induct-with-n numwords offset n))))

;;
;; WRITE-NTH-WORD
;;

;move to super-ihs? (along with nth-word)
;value is a big bit vector
;0 means the least significant word of VALUE
(defund write-nth-word (n word value)
  (if (zp n)
      (logapp 16 word (logtail 16 value))
    (logapp 16 (loghead 16 value) (write-nth-word (+ -1 n) word (logtail 16 value)))))

(defthm write-nth-word-when-n-is-zp
  (implies (zp n)
           (equal (write-nth-word n word value)
                  (logapp 16 word (logtail 16 value))))
  :hints (("Goal" :in-theory (enable write-nth-word))))

(defthm write-nth-word-when-value-it-not-an-integerp
  (implies (not (integerp value))
           (equal (write-nth-word n word value)
                  (write-nth-word n word 0)))
  :hints (("Goal" :in-theory (enable write-nth-word))))

(DEFUN WRITE-DATA-WORDS-INDUCT-with-n (NUMWORDS OFFSET VALUE n)
  (IF (ZP NUMWORDS)
      (LIST NUMWORDS OFFSET VALUE n)
      (WRITE-DATA-WORDS-INDUCT-with-n (+ -1 NUMWORDS)
                                            (+ 1 OFFSET)
                                            (LOGTAIL 16 VALUE)
                                            (+ -1 n)
                                            )))

(defun read-data-words-induct-wrap
  (numwords offset)
  (if (zp numwords)
      (list numwords offset)
    (read-data-words-induct-wrap (+ -1 numwords)
                                 (loghead 16 (+ 1 offset)))))

(defthm logtail-16-of-write-nth-word
  (equal (logtail 16 (write-nth-word n word value))
         (if (zp n)
             (logtail 16 value)
           (write-nth-word (+ -1 n) word (logtail 16 value))))
  :hints (("Goal" :in-theory (enable write-nth-word))))

(defthm loghead-16-of-write-nth-word
  (equal (loghead 16 (write-nth-word n word value))
         (if (zp n)
             (loghead 16 word)
           (loghead 16 value)))
  :hints (("Goal" :in-theory (enable write-nth-word))))

(defthm read-data-words-of-write-data-word-same-E
  (implies (and (< (loghead 16 (- offset2 offset1)) numwords)
                ;(unsigned-byte-p 16 numwords)
                (integerp numwords)
                (<= 0 numwords)
                (<= numwords 65536)
                (integerp offset1)
                (integerp offset2)
                )
           (equal (read-data-words numwords denvr offset1 (write-data-word denvr offset2 word ram))
                  (write-nth-word (loghead 16 (- offset2 offset1)) word (read-data-words numwords denvr offset1 ram))))
  :hints (("subgoal *1/2"
           :expand ((WRITE-NTH-WORD 0 WORD
                                    (READ-DATA-WORDS NUMWORDS DENVR 65535 RAM))
                    (WRITE-NTH-WORD 0 WORD
                                    (READ-DATA-WORDS NUMWORDS DENVR OFFSET1 RAM))
                    (write-nth-word (+ (- offset1) offset2)
                                    word
                                    (read-data-words numwords denvr offset1 ram)))

           :in-theory (e/d (zp ;write-nth-word
                            MEMBERP-OF-OFFSET-RANGE
                            acl2::loghead-sum-split-into-2-cases
                            acl2::loghead-of-minus
                            read-data-words-alt-def
                            ) (read-data-words-opener)))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable zp ;write-nth-word
                              )
           :induct (read-data-words-induct-wrap numwords offset1))))

(DEFUN WRITE-DATA-WORDS-INDUCT-wrap
  (NUMWORDS OFFSET VALUE)
  (IF (ZP NUMWORDS)
      (LIST NUMWORDS OFFSET VALUE)
      (WRITE-DATA-WORDS-INDUCT-wrap (+ -1 NUMWORDS)
                                          (loghead 16 (+ 1 OFFSET))
                                          (LOGTAIL 16 VALUE))))

;gen the 0?
(defthm write-nth-word-0-logapp
  (equal (write-nth-word 0 value (logapp 16 lowbits highbits))
         (logapp 16 value highbits))
  :hints (("Goal" :in-theory (enable write-nth-word))))

(defun induct-by-sub1-and-sub16 (n m)
  (if (zp n)
      (list n m)
    (induct-by-sub1-and-sub16 (+ -1 n) (+ -16 m))))

(defun induct-by-sub1-and-sub1 (n m)
  (if (zp n)
      (list n m)
    (induct-by-sub1-and-sub1 (+ -1 n) (+ -1 m))))

(defun induct-by-sub1-and-sub1-and-logtail16 (n m value)
  (if (zp n)
      (list n m value)
    (induct-by-sub1-and-sub1-and-logtail16 (+ -1 n) (+ -1 m) (logtail 16 value))))


;bzo can loop
(defthmd logtail-16-of-WRITE-NTH-WORD-back
  (implies (and (integerp n)
                (<= 0 n))
           (equal (WRITE-NTH-WORD n word (logtail 16 value))
                  (logtail 16 (WRITE-NTH-WORD (+ 1 n) word value))))
  :hints (("Goal" :in-theory (enable ;WRITE-NTH-WORD
                              ))))

(defthm loghead-of-WRITE-NTH-WORD
  (implies (and (< n m)
                (integerp m)
                (integerp n)
                (<= 0 n)
                (<= 0 m)
                )
           (equal (loghead (* 16 m) (WRITE-NTH-WORD N WORD VALUE))
                  (WRITE-NTH-WORD N WORD (loghead (* 16 m) VALUE))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct ( induct-by-sub1-and-sub1-and-logtail16 n m value)
           :expand (WRITE-NTH-WORD N WORD (LOGHEAD (* 16 M) VALUE))
           :in-theory (e/d (WRITE-NTH-WORD
     ;                           logtail-16-of-WRITE-NTH-WORD-back
                            )
                           ( logtail-16-of-WRITE-NTH-WORD)))))

(defthm write-data-word-of-write-data-words-same
  (implies (and (< (loghead 16 (- offset1 offset2)) numwords)
                (integerp offset1)
                (integerp offset2)
                (unsigned-byte-p 16 numwords)
                (integerp word)
                )
           (equal (write-DATA-WORD denvr offset1 word (WRITE-DATA-WORDS numwords denvr offset2 value ram))
                  (WRITE-DATA-WORDS numwords denvr offset2
                                          (write-nth-word (loghead 16 (- offset1 offset2)) word value) ram)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable ;usb-of-sum-with-two-other-addends-hack
                              MEMBERP-OF-OFFSET-RANGE
                              acl2::loghead-sum-split-into-2-cases
                              acl2::loghead-of-minus
                              )
     ;:induct (WRITE-DATA-WORDS-INDUCT-wrap numwords offset2 value)
           )))

(defthm clear-data-word-of-write-data-words-same
  (implies (and (< (loghead 16 (- offset1 offset2)) numwords)
                (integerp offset1)
                (integerp offset2)
                (unsigned-byte-p 16 numwords)
                (integerp word)
                )
           (equal (clear-DATA-WORD denvr offset1 (WRITE-DATA-WORDS numwords denvr offset2 value ram))
                  (WRITE-DATA-WORDS numwords denvr offset2
                                          (write-nth-word (loghead 16 (- offset1 offset2)) 0 value) ram)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (clear-DATA-WORD
                              ) (WRITE-DATA-WORD-EQUAL-REWRITE))
     ;:induct (WRITE-DATA-WORDS-INDUCT-wrap numwords offset2 value)
           )))


(defthm WRITE-NTH-WORD-of-logapp
  (equal (WRITE-NTH-WORD n word (LOGAPP 16 x y))
         (if (zp n)
             (LOGAPP 16 word y)
           (LOGAPP 16 x (WRITE-NTH-WORD (+ -1 n) word y))))
  :hints (("Goal" :in-theory (enable WRITE-NTH-WORD))))


(defthm write-nth-word-0-when-usb16
  (implies (unsigned-byte-p 16 value)
           (equal (write-nth-word 0 word value)
                  (loghead 16 word)))
  :hints (("Goal" :in-theory (enable write-nth-word))))

(defthm nthword-of-write-nth-word-same
  (equal (NTHWORD n (WRITE-NTH-WORD n word value))
         (loghead 16 word))
  :hints (("Goal" :in-theory (enable WRITE-NTH-WORD NTHWORD))))

;make a both?
(defthm nthword-of-write-nth-word-diff
  (implies (and (natp n1)
                (natp n2)
                (not (equal n1 n2))
                )
           (equal (NTHWORD n1 (WRITE-NTH-WORD n2 word value))
                  (NTHWORD n1 value)))
  :hints (("Goal" :in-theory (enable WRITE-NTH-WORD NTHWORD))))

(defthm write-nth-word-constant-opener
  (implies (syntaxp (quotep n))
           (equal (write-nth-word n word value)
                  (if (zp n)
                      (logapp 16 word (logtail 16 value))
                    (logapp 16 (loghead 16 value) (write-nth-word (+ -1 n) word (logtail 16 value))))))
  :hints (("Goal" :in-theory (enable write-nth-word))))

(defthm write-nth-word-of-write-nth-word-diff
  (implies (and (natp n1)
                (natp n2)
                (not (equal n1 n2)))
           (equal (write-nth-WORD n1 word1 (WRITE-NTH-WORD n2 word2 value))
                  (write-nth-WORD n2 word2 (WRITE-NTH-WORD n1 word1 value))))
  :rule-classes ((:rewrite :loop-stopper ((n1 n2))))
  :hints (("Goal" :in-theory (enable WRITE-NTH-WORD NTHWORD))))

(defthm write-nth-word-of-write-nth-word-same
  (equal (write-nth-word n word1 (write-nth-word n word2 value))
         (write-nth-word n word1 value))
  :hints (("Goal" :in-theory (enable write-nth-word nthword))))

;could make a bound about the second word?
(defthm read-data-words-bound
  (implies (and (integerp n)
                (< 0 n))
           (<= (read-data-word denvr offset ram)
               (read-data-words n denvr offset ram)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use (:instance read-data-words-alt-def
                                  (denvr denvr)
                                  (offset offset)
                                  (ram ram)
                                  (numwords n)
                                  )
           :in-theory (disable loghead-16-of-read-data-words
;                               loghead-times-16-of-read-data-words
                               read-data-words-alt-def))))

(defthm read-data-words-when-high-word-is-zero-cheap
  (implies (and (equal 0 (read-data-word denvr (+ 1 offset) ram))
                (integerp offset))
           (equal (read-data-words 2 denvr offset ram)
                  (read-data-word denvr offset ram)))
  :rule-classes ((:rewrite :backchain-limit-lst (1 nil)))
  :hints (("Goal" :in-theory (enable read-data-words-alt-def))))


;bzo generalize this sequence?
(defthm read-data-word-when-read-data-words-equals-constant
  (implies (and (equal k (read-data-words numwords denvr offset ram))
                (syntaxp (quotep k)) ;consider relaxing this?
                (< 0 numwords)
                (integerp numwords)
                )
           (equal (read-data-word denvr offset ram)
                  (loghead 16 k))))

(defthm read-data-word-when-read-data-words-equals-constant-2
  (implies (and (equal k (read-data-words numwords denvr offset ram))
                (syntaxp (quotep k)) ;consider relaxing this?
                (< 1 numwords)
                (integerp numwords)
                (integerp offset)
                )
           (equal (read-data-word denvr (+ 1 offset) ram)
                  (loghead 16 (logtail 16 k)))))



(defthm fetch-code-bytes-list-of-sum-normalize-constant
  (implies (and (syntaxp (quotep z))
                (not (acl2::unsigned-byte-p 16 z))
                (integerp z)
                )
           (equal (fetch-code-bytes-list numbytes cenvr (+ z offset) ram)
                  (fetch-code-bytes-list numbytes cenvr (+ (loghead 16 z) offset) ram)))
  :hints (("Goal" :in-theory (enable fetch-code-bytes-list fetch-code-bytes))))

;dup?
(defthm write-data-words-of-sum-normalize-constant
  (implies (and (syntaxp (quotep k))
                (not (unsigned-byte-p 16 k))
                (integerp k)
                (integerp offset)
                )
           (equal (write-data-words numwords denvr (+ k offset) value ram)
                  (write-data-words numwords denvr (+ (loghead 16 k) offset) value ram)))
  :hints (("Goal" :use ((:instance write-data-words-of-loghead-16 (offset (+ k offset)))
                        (:instance write-data-words-of-loghead-16 (offset (+ (loghead 16 k) offset))))
           :in-theory (e/d () (write-data-word-of-loghead-16
                               write-data-word-equal-rewrite)))))

;dup?
(defthm clear-data-words-of-sum-normalize-constant
  (implies (and (syntaxp (quotep k))
                (not (unsigned-byte-p 16 k))
                (integerp k)
                (integerp offset)
                )
           (equal (clear-data-words numwords denvr (+ k offset) ram)
                  (clear-data-words numwords denvr (+ (loghead 16 k) offset) ram)))
  :hints (("Goal" :in-theory (enable clear-data-words))))

;dup?
(defthm read-data-word-of-sum-normalize-constant-2
  (implies (and (syntaxp (quotep k))
                (integerp k)
                (integerp offset)
                (not (unsigned-byte-p 16 k)))
           (equal (read-data-word denvr (+ k offset) ram)
                  (read-data-word denvr (+ (loghead 16 k) offset) ram)))
  :hints (("Goal" :use ((:instance READ-DATA-WORD-OF-SUM-NORMALIZE-CONSTANT (k (+ k offset)))
                        (:instance READ-DATA-WORD-OF-SUM-NORMALIZE-CONSTANT (k (+ (loghead 16 k) offset))))
           :in-theory (e/d () (READ-DATA-WORD-OF-SUM-NORMALIZE-CONSTANT)))))

;bzo move this series
(defthmd write-data-words-opener-hack
  (implies (and (syntaxp (equal numwords 'numwords)) ;note this
                (not (zp numwords)))
           (equal (write-data-words numwords denvr offset value ram)
                  (write-data-word
                   denvr
                   offset (loghead 16 value)
                   (write-data-words (+ -1 numwords)
                                     denvr (+ 1 (ifix offset))
                                     (logtail 16 value)
                                     ram))))
  :hints (("Goal" :use (:instance write-data-words-opener
                                   (denvr denvr)
                                   (offset offset)
                                   (ram ram)
                                   (numwords numwords)
                                   (value value)
                                  )
           :in-theory (disable write-data-words))))



(defthm write-data-words-of-loghead
  (implies (and (acl2::natp numwords)
                (INTEGERP OFFSET))
           (equal (write-data-words numwords denvr offset (loghead (* 16 numwords) value) ram)
                  (write-data-words numwords denvr offset value ram)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (write-data-words-induct numwords offset value)
           :in-theory (e/d ( WRITE-DATA-WORDS-opener-hack
                           ;  WRITE-DATA-WORDS-alt-def
                             )
                           (WRITE-DATA-WORD-EQUAL-REWRITE)))))

(defthm write-data-words-of-sum-normalize-constant-addend-in-value
  (implies (and (syntaxp (and (quotep k)
                              (not (unsigned-byte-p (* 16 (cadr numwords)) (cadr k)))))
                (integerp k)
                (integerp offset)
                )
           (equal (write-data-words numwords denvr offset (+ k value) ram)
                  (write-data-words numwords denvr offset (+ (loghead (* 16 numwords) k) value) ram)))
  :hints (("Goal" :use ((:instance WRITE-DATA-WORDs-of-loghead
;;                                    (denvr denvr)
;;                                    (offset offset)
;;                                    (ram ram)
                                   (value (+ (loghead (* 16 numwords) k) value)))
                        (:instance WRITE-DATA-WORDs-of-loghead
;;                                    (denvr denvr)
;;                                    (offset offset)
;;                                    (ram ram)
                                   (value (+ k value))))
           :in-theory (e/d () (WRITE-DATA-WORDs-of-loghead
                               write-data-word-equal-rewrite)))))

(defthm write-data-words-of-sum-normalize-constant-value
  (implies (and (syntaxp (and (quotep k)
                              (quotep numwords)
                              (<= 0 (cadr numwords))
                              (not (unsigned-byte-p (* 16 (cadr numwords)) (cadr k)))))
                (integerp k)
                (integerp offset)
                )
           (equal (write-data-words numwords denvr offset k ram)
                  (write-data-words numwords denvr offset (loghead (* 16 numwords) k) ram)))
  :hints (("Goal" :use ((:instance WRITE-DATA-WORDs-of-loghead
;;                                    (denvr denvr)
;;                                    (offset offset)
;;                                    (ram ram)
                                   (value (loghead (* 16 numwords) k)))
                        (:instance WRITE-DATA-WORDs-of-loghead
;;                                    (denvr denvr)
;;                                    (offset offset)
;;                                    (ram ram)
                                   (value k)))
           :in-theory (e/d () (WRITE-DATA-WORDs-of-loghead
                               write-data-word-equal-rewrite)))))

(defthm write-data-words-hack
  (implies (and (integerp y)
                (integerp x)
                (integerp offset)
                (equal n (* 16 numwords))
                (< 0 numwords) ;bzo gen
                (integerp numwords)
                )
           (equal (write-data-words numwords denvr offset (+ (LOGEXT n x) y) ram)
                  (write-data-words numwords denvr offset (+ x y) ram)))
  :hints (("Goal" :use ((:instance WRITE-DATA-WORDs-of-loghead
                                   ;;                                    (denvr denvr)
                                   ;;                                    (offset offset)
                                   ;;                                    (ram ram)
                                   (value (+ (LOGEXT n x) y)))
                        (:instance WRITE-DATA-WORDs-of-loghead
                                   ;;                                    (denvr denvr)
                                   ;;                                    (offset offset)
                                   ;;                                    (ram ram)
                                   (value (+ x y))))
           :in-theory (e/d () (
                               WRITE-DATA-WORDS-OF-LOGHEAD
                               write-data-word-equal-rewrite)))))

(defthm write-data-words-hack-alt
  (implies (and (integerp y)
                (integerp x)
                (integerp offset)
                (equal n (* 16 numwords))
                (< 0 numwords) ;bzo gen
                (integerp numwords)
                )
           (equal (write-data-words numwords denvr offset (+ y (LOGEXT n x)) ram)
                  (write-data-words numwords denvr offset (+ x y) ram)))
  :hints (("Goal" :use (:instance write-data-words-hack)
           :in-theory (disable write-data-words-hack))))



;bzo gen and add theory invar with opener
(defthmd fetch-code-bytes-recollect
  (implies (and (equal (loghead 16 (+ 2 offset1)) (loghead 16 offset2))
                (integerp offset1))
           (equal (logapp 16
                          (gacc::fetch-code-bytes 2 cenvr offset1 ram)
                          (gacc::fetch-code-byte cenvr offset2 ram))
                  (gacc::fetch-code-bytes 3 cenvr offset1 ram)))
  :hints (("Goal" :in-theory (e/d (GACC::FETCH-CODE-BYTES-OPENER) (fetch-code-bytes)))))

(defthmd addresses-of-data-words-constant-opener
  (implies (and (syntaxp (quotep numwords))
                (integerp numwords)
                (< 0 numwords)
                (integerp offset))
           (equal (gacc::addresses-of-data-words numwords denvr offset)
                  (append (gacc::addresses-of-data-word denvr offset)
                          (gacc::addresses-of-data-words (+ -1 numwords) denvr (+ 1 offset)))))
  :hints (("Goal" :in-theory (enable gacc::word-ads-to-byte-ads))))

(defthm addresses-of-data-words-of-0
  (equal (gacc::addresses-of-data-words 0 denvr offset)
         nil))

(defthm addresses-of-data-word-of-sum-loghead
  (implies (and (integerp a)
                (integerp b))
           (equal (gacc::addresses-of-data-word denvr (+ a (loghead 16 b)))
                  (gacc::addresses-of-data-word denvr (+ a b)))))

(defthm cadr-of-word-ad-to-byte-ads
  (equal (cadr (gacc::word-ad-to-byte-ads word-ad))
         (acl2::logapp 1 1 word-ad))
  :hints (("Goal" :in-theory (enable gacc::word-ad-to-byte-ads))))

(defthm car-of-word-ad-to-byte-ads
  (equal (car (gacc::word-ad-to-byte-ads word-ad))
         (acl2::logapp 1 0 word-ad))
  :hints (("Goal" :in-theory (enable gacc::word-ad-to-byte-ads))))

(defthm logcdr-list-of-word-ad-to-byte-ads
  (equal (gacc::logcdr-list (gacc::word-ad-to-byte-ads ad))
         (list (ifix ad) (ifix ad)))
  :hints (("Goal" :in-theory (enable gacc::word-ad-to-byte-ads))))

(defun dup-and-ifix-all (lst)
  (if (endp lst)
      nil
    (cons (ifix (car lst)) (cons (ifix (car lst)) (dup-and-ifix-all (cdr lst))))))

(defthm logcdr-list-of-word-ads-to-byte-ads
  (equal (gacc::logcdr-list (gacc::word-ads-to-byte-ads word-ads))
         (dup-and-ifix-all word-ads))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::word-ads-to-byte-ads gacc::logcdr-list))))

(defthm dup-and-ifix-perm
  (implies (integer-listp lst)
           (bag::perm (dup-and-ifix-all lst)
                      (append lst lst)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


(defthm nthword-of-0-value
  (equal (nthword n 0)
         0)
  :hints (("Goal" :in-theory (enable gacc::nthword))))

(defthm nthword-when-value-is-not-an-integerp
  (implies (not (integerp value))
           (equal (gacc::nthword n value)
                  0))
  :hints (("Goal" :in-theory (enable gacc::nthword ;-rewrite
                                     ))))

;move to gacc/ram3
(defthm loghead-times-16-of-read-data-words
  (implies (and (integerp numwords1)
                (integerp numwords2)
                )
           (equal (loghead (* 16 numwords1) (gacc::read-data-words numwords2 denvr offset ram))
                  (if (<= numwords1 numwords2)
                      (gacc::read-data-words numwords1 denvr offset ram)
                    (gacc::read-data-words numwords2 denvr offset ram))))

  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::read-data-words-alt-def
                       )
           :induct (gacc::read-data-words-induct-with-n numwords2 offset numwords1))))

;ram3
(defthm logtail-times-16-of-read-data-words
  (implies  (and (integerp numwords1)
                 (integerp numwords2)
;                 (<= 0 numwords2)
                 (<= 0 numwords1)
                 (integerp offset)
                 )
            (equal (LOGTAIL (* 16 NUMWORDS1) (GACC::READ-DATA-WORDS NUMWORDS2 DENVR offset ram))
                   (GACC::READ-DATA-WORDS (- NUMWORDS2 numwords1) DENVR (+ offset numwords1) ram)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::read-data-words-alt-def
                       )
           :induct (gacc::read-data-words-induct-with-n numwords2 offset numwords1)))
  )

;add to ram3
(defthm write-data-word-of-write-data-words-diff-better
  (implies (and (syntaxp (gacc::smaller-params denvr2 offset2
                                               denvr1 offset1))
                (<= numwords (loghead 16 (- offset1 offset2)))
                (integerp offset2)
                (integerp offset1)
                )
           (equal (gacc::write-data-word denvr1 offset1 val1 (gacc::write-data-words numwords denvr2 offset2 val2 ram))
                  (gacc::write-data-words numwords denvr2 offset2 val2 (gacc::write-data-word denvr1 offset1 val1 ram))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (e/d (gacc::memberp-of-offset-range) (gacc::write-data-word-of-write-data-words-diff
                                                                   gacc::write-data-words-equal-rewrite))
           :use (:instance gacc::write-data-word-of-write-data-words-diff))))

;add to ram3!
(defthm gacc::write-data-word-when-value-is-not-an-integerp
  (implies (not (integerp value))
           (equal (gacc::write-data-word denvr offset value ram)
                  (gacc::write-data-word denvr offset 0 ram)))
  :hints (("Goal" :in-theory (enable gacc::write-data-word))))


;bzo make an alt version?
;ram3
(defthmd gacc::write-data-words-recollapse
  (implies (and (equal (loghead 16 offset2) (loghead 16 (+ 1 (ifix offset1))))
;(integerp val2)
                )
           (equal (gacc::write-data-word denvr offset1 val1 (gacc::write-data-word denvr offset2 val2 ram))
                  (gacc::write-data-words 2 denvr offset1 (logapp 16 val1 (ifix val2)) ram)))
  :hints (("Goal" :in-theory (e/d (gacc::write-data-words-opener)
                                  (acl2::loghead-sum-split-into-2-when-i-is-a-constant)))))

;(defthm DATA-WRITE-ALLOWED-when-offset-is-not-an-UNSIGNED-BYTE-P
;  (IMPLIES (NOT (UNSIGNED-BYTE-P 16 AAMP::OFFSET))
;           (equal (AAMP::DATA-WRITE-ALLOWED AAMP::DENVR AAMP::OFFSET AAMP::PMU)
;                  (AAMP::DATA-WRITE-ALLOWED AAMP::DENVR (loghead 16 AAMP::OFFSET) AAMP::PMU)))
;  :hints (("Goal" :in-theory (e/d (AAMP::DATA-WRITE-ALLOWED
;                                   GACC::MAKE-DATA-ADDR)
;                                  (AAMP::ACCESS-CHECK-BECOMES-DATA-WRITE-ALLOWED)))))




;(defthm GACC::READ-DATA-WORD-smaller-than-big-constant
;  (implies (and (syntaxp (quotep k))
;                (<= 65536 k))
;           (equal (< (GACC::READ-DATA-WORD denvr offset ram) k)
;                  t)))
;ram3
(defthm fetch-code-bytes-list-when-offset-is-not-a-usb16
  (implies (and (syntaxp (quotep offset))
                (not (unsigned-byte-p 16 offset)))
           (equal (gacc::fetch-code-bytes-list numbytes cenvr offset ram)
                  (gacc::fetch-code-bytes-list numbytes cenvr (loghead 16 offset) ram))))

;bzo gen
;bzo or should we just open up nthword?
(defthm nthword-1-of-loghead8
  (equal (gacc::nthword 1 (loghead 8 x))
         0)
  :hints (("Goal" :in-theory (enable gacc::nthword))))


(defthm nthword-1-of-ash-16
  (equal (gacc::nthword 1 (ash x 16))
         (loghead 16 x))
  :hints (("Goal" :in-theory (enable gacc::nthword))))


;scary?
(defthmd logtail-16-loghead-32
  (equal (logtail 16 (loghead 32 x))
         (gacc::nthword 1 x))
  :hints (("Goal" :expand ((gacc::nthword 1 x)))))


;gen?
(defthm gacc::write-nth-word-0-0
  (equal (gacc::write-nth-word n 0 0)
         0)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::write-nth-word))))

(defthm gacc::write-nth-word-non-negative
  (implies (and (<= 0 word)
                (integerp value) ;bzo
                (<= 0 value))
           (<= 0 (gacc::write-nth-word n word value)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable gacc::write-nth-word))))

(defthm gacc::write-nth-word-logapp32-hack
  (implies (and (integerp n)
                (integerp x)
                (integerp y))
           (equal (gacc::write-nth-word n word (logapp 32 x y))
                  (if (< n 2)
                      (logapp 32 (gacc::write-nth-word n word x) y)
                    (logapp 32 x (gacc::write-nth-word (+ -2 n) word y)))))
  :hints (("Goal" :in-theory (enable gacc::write-nth-word))))

(defthm gacc::write-data-words-opener-2
  (implies (and (syntaxp (and (quotep gacc::numwords)
                              (<= (cadr gacc::numwords) 20)))
                (not (zp gacc::numwords)))
           (equal (gacc::write-data-words gacc::numwords gacc::denvr gacc::offset value gacc::ram)
                  (gacc::write-data-word
                   gacc::denvr
                   gacc::offset (loghead 16 value)
                   (gacc::write-data-words
                    (+ -1 gacc::numwords)
                    gacc::denvr (+ 1 (ifix gacc::offset))
                    (logtail 16 value)
                    gacc::ram))))
  :hints
  (("Goal"
    :expand
    ((gacc::offset-range-wrap 16 gacc::offset gacc::numwords))
    :in-theory
    (e/d (gacc::write-data-words
          gacc::write-data-word
          acl2::logext-logapp gacc::word-ad-to-byte-ads)
         nil))))

;bzo push this change back?
(in-theory (disable list::nthcdr-of-firstn))
(in-theory (enable list::firstn-of-nthcdr))

(defthmd gacc::write-data-words-opener-n
  (implies (and (integerp nwords) (> nwords 2) (< nwords 20) (integerp offset1))
           (equal (gacc::write-data-words nwords denvr offset1 val ram)
                  (gacc::write-data-words 2 denvr offset1 (loghead 32 val)
                                          (gacc::write-data-words (- nwords 2) denvr
                                                                  (loghead 16 (+ 2 offset1))
                                                                  (logtail 32 val) ram))))
  :hints (("Goal" :in-theory (e/d (gacc::write-data-words-opener-2)
                                  (gacc::write-data-words-opener)))))

;bzo gen
(defthm logapp-of-READ-DATA-WORDS
  (equal (LOGAPP 64 (GACC::READ-DATA-WORDS 5 denvr offset ram)
                 1)
         (LOGAPP 64 (GACC::READ-DATA-WORDS 4 denvr offset ram)
                 1)))

;bzo gen
(defthm nthword-2-ash-32-hack
  (equal (gacc::nthword 2 (ash x 32))
         (loghead 16 x))
  :hints (("Goal" :in-theory (e/d (gacc::nthword-rewrite) (gacc::logtail-16-loghead-32)))))

;bzo gen
(defthm nthword-3-ash-32-hack
  (equal (gacc::nthword 3 (ash x 32))
         (gacc::nthword 1 x))
  :hints (("Goal" :in-theory (e/d (gacc::nthword-rewrite) (gacc::logtail-16-loghead-32)))))

(defthm nthword-of-READ-DATA-WORDS-too-far
  (implies (and (<= numwords n)
                (<= 0 numwords)
                (integerp numwords)
                (integerp n))
           (equal (GACC::NTHWORD n (GACC::READ-DATA-WORDS numwords denvr offset ram))
                  0))
 :hints (("Goal" :in-theory (e/d (GACC::NTHWORD-rewrite) (gacc::LOGTAIL-16-LOGHEAD-32)))))

(defthm loghead-times-16-of-read-data-words-special
  (implies (and (integerp numwords1)
                (integerp numwords2)
                )
           (equal (loghead (+ -64 (* 16 NUMWORDS1)) (gacc::read-data-words numwords2 denvr offset ram))
                  (if (<= (+ -4 NUMWORDS1) numwords2)
                      (gacc::read-data-words (+ -4 NUMWORDS1) denvr offset ram)
                    (gacc::read-data-words numwords2 denvr offset ram))))
  :otf-flg t
  :hints (("Goal" :in-theory (disable loghead-times-16-of-read-data-words)
           :use (:instance loghead-times-16-of-read-data-words (numwords1 (+ -4 NUMWORDS1)))))
  )

;bzo gen
(defthm hack1
  (implies (integerp numwords)
           (equal (loghead (+ -64 (* 16 numwords)) (gacc::wintlist byte-list))
                  (gacc::wintlist (firstn (+ -8 (* 2 numwords)) byte-list))))
  :hints (("Goal" :in-theory (disable gacc::loghead-times-8-of-wintlist)
           :use (:instance gacc::loghead-times-8-of-wintlist
                           (gacc::byte-list byte-list)
                           (gacc::numbytes (+ -8 (* 2 numwords)))))
          ))

(defthm logtail-times-16-of-read-data-words-hack
  (implies  (and (integerp numwords1)
                 (integerp numwords2)
                 (<= 0 numwords2)
                 (<= 4 numwords1)
                 (integerp offset)
                 )
            (equal (LOGTAIL (+ -64 (* 16 NUMWORDS1)) (GACC::READ-DATA-WORDS NUMWORDS2 DENVR offset ram))
                   (GACC::READ-DATA-WORDS (+ 4 (- NUMWORDS2 numwords1)) DENVR (+ -4 offset numwords1) ram)))
  :hints (("Goal" :use (:instance gacc::logtail-times-16-of-read-data-words
                                  (numwords1 (+ -4 numwords1))
                                  )

           :in-theory (disable gacc::logtail-times-16-of-read-data-words)))

  )

;bzo remove the -hack version?
;matches better
(defthm logtail-times-16-of-read-data-words-alt
  (implies (and (integerp (/ n 16))
;                (integerp n)
                (<= 0 n) ;drop?
                (integerp numwords2)
;                (<= 0 numwords1)
                (integerp offset))
           (equal (logtail n (gacc::read-data-words numwords2 denvr offset ram))
                  (gacc::read-data-words (- numwords2 (/ n 16))
                                         denvr (+ offset (/ n 16))
                                         ram)))
  :hints (("Goal" :in-theory (disable logtail-times-16-of-read-data-words)
           :use (:instance logtail-times-16-of-read-data-words (numwords1 (/ n 16))))))

(defthm consp-of-cdr-of-addresses-of-data-words
  (implies (and (integerp numwords)
                (< 0 numwords))
           (consp (cdr (gacc::addresses-of-data-words numwords denvr offset))))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-words))))

(defthm cdr-of-cdr-of-addresses-of-data-words
  (implies (and (integerp numwords)
                (< 0 numwords)
                (integerp offset) ;this may cause problems
                )
           (equal (cdr (cdr (gacc::addresses-of-data-words numwords denvr offset)))
                  (gacc::addresses-of-data-words (+ -1 numwords) denvr (acl2::loghead 16 (+ 1 offset)))))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-words))))

(defthm car-of-addresses-of-data-words
  (implies (and (integerp numwords)
                (< 0 numwords))
           (equal (car (gacc::addresses-of-data-words numwords denvr offset))
                  (car (gacc::addresses-of-data-word denvr offset))))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-words))))

(defthm cadr-of-addresses-of-data-words
  (implies (and (integerp numwords)
                (< 0 numwords))
           (equal (cadr (gacc::addresses-of-data-words numwords denvr offset))
                  (cadr (gacc::addresses-of-data-word denvr offset))))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-words))))

(defthm car-of-addresses-of-data-word
  (equal (car (gacc::addresses-of-data-word denvr offset))
         (acl2::logapp 1 0 (acl2::logapp 16 offset (acl2::loghead 15 denvr)))
         )
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-words))))

(defthm cadr-of-addresses-of-data-word
  (equal (cadr (gacc::addresses-of-data-word denvr offset))
         (acl2::logapp 1 1 (acl2::logapp 16 offset (acl2::loghead 15 denvr)))
         )
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-words))))

(in-theory (disable gacc::cadr-when-offset-rangep)) ;bzo move up?

(defthm consp-of-cdr-of-addresses-of-data-word
  (consp (cdr (gacc::addresses-of-data-word denvr offset)))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-word))))

(defthm cdr-of-cdr-of-addresses-of-data-word
  (equal (cdr (cdr (gacc::addresses-of-data-word denvr offset)))
         nil)
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-word))))

(defthm addresses-of-data-words-of-1
  (equal (gacc::addresses-of-data-words 1 denvr offset)
         (gacc::addresses-of-data-word denvr offset))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-words))))


;disable?
;gen?
;add backchain limit?
(defthmd loghead-15-not-equal-hack
  (implies (not (acl2::unsigned-byte-p 15 x))
           (not (equal x (acl2::loghead 15 y)))))

(defthm memberp-of-addresses-of-data-words
  (implies (and (integerp offset)
                (integerp numwords))
           (equal (memberp ad (gacc::addresses-of-data-words numwords denvr offset))
                  (and (acl2::unsigned-byte-p 32 ad)
                       (equal (acl2::logtail 17 ad) (acl2::loghead 15 denvr))
                       (< (acl2::loghead 16 (- (acl2::loghead 16 (acl2::logtail 1 ad))
                                               offset))
                          numwords))))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::addresses-of-data-words
                              loghead-15-not-equal-hack
                              gacc::memberp-of-offset-range))))

(defthm memberp-of-addresses-of-data-word
  (implies (integerp offset)
           (equal (memberp ad (gacc::addresses-of-data-word denvr offset))
                  (and (acl2::unsigned-byte-p 32 ad)
                       (equal (acl2::logtail 17 ad) (acl2::loghead 15 denvr))
                       (< (acl2::loghead 16 (- (acl2::loghead 16 (acl2::logtail 1 ad)) offset)) 1)
                       )))
  :hints (("Goal" :use (:instance memberp-of-addresses-of-data-words
                                  (numwords 1))
           :in-theory (disable memberp-of-addresses-of-data-words))))

(defthm addresses-of-data-word-simp-leading-constant
  (implies (and (syntaxp (quotep k))
                (not (acl2::unsigned-byte-p 16 k))
                (integerp k)
                (integerp offset))
           (equal (gacc::addresses-of-data-word denvr (+ k offset))
                  (gacc::addresses-of-data-word denvr (+ (acl2::loghead 16 k) offset)))))

(defthm word-ads-to-byte-ads-of-fix
  (equal (gacc::word-ads-to-byte-ads (list::fix ads))
         (gacc::word-ads-to-byte-ads ads))
  :hints (("Goal" :in-theory (enable gacc::word-ads-to-byte-ads))))

(defthm word-ads-to-byte-ads-of-remove-1
  (implies (and (gacc::unsigned-byte-p-list 31 ads)
                (acl2::unsigned-byte-p 31 x))
           (equal (gacc::word-ads-to-byte-ads (bag::remove-1 x ads))
                  (bag::remove-bag (gacc::word-ad-to-byte-ads x)
                                   (gacc::word-ads-to-byte-ads ads))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::word-ads-to-byte-ads
                              WORD-AD-TO-BYTE-ADS
                              bag::remove-1))))

(defthm addresses-of-data-word-of-loghead-around-offset
  (equal (gacc::addresses-of-data-word denvr (acl2::loghead 16 offset))
         (gacc::addresses-of-data-word denvr offset))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-word))))

(defthm len-of-addresses-of-data-words
  (equal (len (gacc::addresses-of-data-words numwords denvr offset))
         (* 2 (nfix numwords)))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-words))))

(local
 (defun 2-list-induct (l1 l2)
   (if (endp l1)
       (list l1 l2)
     (2-list-induct (cdr l1) (bag::remove-1 (car l1) l2)))))

;make this and the forward rule local?
(defthm gacc::subbagp-of-word-ads-to-byte-ads-and-word-ads-to-byte-ads-back
  (implies (and (bag::subbagp (gacc::word-ads-to-byte-ads ads1)
                              (gacc::word-ads-to-byte-ads ads2))
                (gacc::unsigned-byte-p-list 31 ads1)
                (gacc::unsigned-byte-p-list 31 ads2))
           (bag::subbagp ads1 ads2))
  :hints
  (("Goal" :do-not '(generalize eliminate-destructors)
               :induct (2-list-induct ads1 ads2)
    :in-theory (e/d (len gacc::word-ads-to-byte-ads
                         WORD-AD-TO-BYTE-ADS)
                    (list::len-cdr-equal-len-cdr-rewrite
                     BAG::SUBBAG-BY-MULTIPLICITY
                     ;GACC::WORD-AD-TO-BYTE-ADS

                     )))))

;bzo improve GACC::SUBBAGP-OF-WORD-ADS-TO-BYTE-ADS-AND-WORD-ADS-TO-BYTE-ADS to not use integer-listp but rather the better one
(defthm gacc::subbagp-of-word-ads-to-byte-ads-and-word-ads-to-byte-ads-both
  (implies (and (gacc::unsigned-byte-p-list 31 ads1)
                (gacc::unsigned-byte-p-list 31 ads2)
                (true-listp ads1) ;yuck
                (true-listp ads2) ;yuck
                )
           (equal (bag::subbagp (gacc::word-ads-to-byte-ads ads1)
                                (gacc::word-ads-to-byte-ads ads2))
                  (bag::subbagp ads1 ads2))))



;make GACC::UNIQUE-OF-OFFSET-RANGE-WRAP into an equal rule?

;(set-default-hints nil)

;bzo gen?
;bzo prove single word versions
(defthm subbagp-of-addresses-of-data-words-and-addresses-of-data-words
  (implies (and (natp numwords1)
                (natp numwords2)
                (< 0 numwords1)
                (<= NUMWORDS2 (EXPT 2 16))
                (<= NUMWORDS1 (EXPT 2 16))
                (ACL2::UNSIGNED-BYTE-P 16 NUMWORDS2)
                (natp offset1)
                (natp offset2))
           (equal (bag::subbagp (gacc::addresses-of-data-words numwords1 denvr offset1)
                                (gacc::addresses-of-data-words numwords2 denvr offset2))
                  (and (< (acl2::loghead 16 (- offset1 offset2)) numwords2)
                       (<= (+ numwords1 (acl2::loghead 16 (- offset1 offset2))) numwords2))))
  :otf-flg t
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-words
                                     GACC::SUBBAGP-OF-TWO-OFFSET-RANGE-wraps))))

(defthm subbagp-of-addresses-of-data-words-and-addresses-of-data-word
  (implies (and (natp numwords1)
                (< 0 numwords1)
                (<= NUMWORDS1 (EXPT 2 16))
                (natp offset1)
                (natp offset2))
           (equal (bag::subbagp (gacc::addresses-of-data-words numwords1 denvr offset1)
                                (gacc::addresses-of-data-word denvr offset2))
                  (and (< (acl2::loghead 16 (- offset1 offset2)) 1)
                       (<= (+ numwords1 (acl2::loghead 16 (- offset1 offset2))) 1))))
  :hints (("Goal" :use (:instance subbagp-of-addresses-of-data-words-and-addresses-of-data-words (numwords2 1))
           :in-theory (disable subbagp-of-addresses-of-data-words-and-addresses-of-data-words))))

(defthm subbagp-of-addresses-of-data-word-and-addresses-of-data-words
  (implies (and (natp numwords2)
                (<= NUMWORDS2 (EXPT 2 16))
                (ACL2::UNSIGNED-BYTE-P 16 NUMWORDS2)
                (natp offset1)
                (natp offset2))
           (equal (bag::subbagp (gacc::addresses-of-data-word denvr offset1)
                                (gacc::addresses-of-data-words numwords2 denvr offset2))
                  (and (< (acl2::loghead 16 (- offset1 offset2)) numwords2)
                       (<= (+ 1 (acl2::loghead 16 (- offset1 offset2))) numwords2))))
  :hints (("Goal" :use (:instance subbagp-of-addresses-of-data-words-and-addresses-of-data-words (numwords1 1))
           :in-theory (disable subbagp-of-addresses-of-data-words-and-addresses-of-data-words))))

(defthm subbagp-of-addresses-of-data-word-and-addresses-of-data-word
  (implies (and (natp offset1)
                (natp offset2))
           (equal (bag::subbagp (gacc::addresses-of-data-word denvr offset1)
                                (gacc::addresses-of-data-word denvr offset2))
                  (and (< (acl2::loghead 16 (- offset1 offset2)) 1)
                       (<= (+ 1 (acl2::loghead 16 (- offset1 offset2))) 1))))
  :hints (("Goal" :use (:instance subbagp-of-addresses-of-data-words-and-addresses-of-data-words (numwords1 1) (numwords2 1))
           :in-theory (disable subbagp-of-addresses-of-data-words-and-addresses-of-data-words))))


;one is even and the other odd
(defthm cadr-of-addresses-of-data-word-not-equal-car-of-addresses-of-data-word
  (not (equal (cadr (gacc::addresses-of-data-word denvr1 offset1))
              (car (gacc::addresses-of-data-word denvr2 offset2))))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-word))))

;one is even and the other odd
(defthm cadr-of-addresses-of-data-words-not-equal-car-of-addresses-of-data-word
  (implies (and (integerp numwords)
                (< 0 numwords))
           (not (equal (cadr (gacc::addresses-of-data-words numwords denvr1 offset1))
                       (car (gacc::addresses-of-data-word denvr2 offset2)))))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-word CADR-OF-ADDRESSES-OF-DATA-WORDS))))

;one is even and the other odd
(defthm cadr-of-addresses-of-data-word-not-equal-car-of-addresses-of-data-words
  (implies (and (integerp numwords)
                (< 0 numwords))
           (not (equal (cadr (gacc::addresses-of-data-word denvr2 offset2))
                       (car (gacc::addresses-of-data-words numwords denvr1 offset1)))))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-word CAR-OF-ADDRESSES-OF-DATA-WORDS))))

;one is even and the other odd
(defthm cadr-of-addresses-of-data-words-not-equal-car-of-addresses-of-data-words
  (implies (and (integerp numwords1)
                (< 0 numwords1)
                (integerp numwords2)
                (< 0 numwords2))
           (not (equal (cadr (gacc::addresses-of-data-words numwords2 denvr2 offset2))
                       (car (gacc::addresses-of-data-words numwords1 denvr1 offset1)))))
  :hints (("Goal" :in-theory (enable gacc::addresses-of-data-word CAR-OF-ADDRESSES-OF-DATA-WORDS CADR-OF-ADDRESSES-OF-DATA-WORDS))))

(defthm rd-of-write-data-word-diff-denvr
  (implies (and (not (equal (acl2::loghead 15 denvr) (acl2::logtail 17 ad)))
                (integerp offset) ;drop?
                )
           (equal (gacc::rd ad (gacc::write-data-word denvr offset value ram))
                  (gacc::rd ad ram)))
  :hints (("Goal" :in-theory (enable gacc::write-data-word))))

(defthm rd-of-write-data-word-diff-offset
  (implies (and (not (equal (acl2::loghead 16 offset) (acl2::loghead 16 (acl2::logtail 1 ad))))
                (integerp offset) ;drop?
                )
           (equal (gacc::rd ad (gacc::write-data-word denvr offset value ram))
                  (gacc::rd ad ram)))
  :hints (("Goal" :in-theory (enable gacc::write-data-word))))

(defthm rd-of-write-data-word-same
  (implies (and (equal (acl2::loghead 15 denvr) (acl2::logtail 17 ad))
                (equal (acl2::loghead 16 offset) (acl2::loghead 16 (acl2::logtail 1 ad)))
                (integerp offset) ;drop?
                (ACL2::UNSIGNED-BYTE-P '32 AD) ;drop?
                )
           (equal (gacc::rd ad (gacc::write-data-word denvr offset value ram))
                  (acl2::loghead 8 (acl2::logtail
                                    (* 8 (acl2::logcar ad)) ;if ad is even, take word 0, else take word 1
                                    value))
                  ))
  :hints (("Goal" :in-theory (enable gacc::write-data-word
                                     WORD-AD-TO-BYTE-ADS
                                     GACC::ADDRESSES-OF-DATA-WORD
                                     ACL2::EQUAL-LOGAPP-X-Y-Z))))

(defthm rd-of-write-data-words-diff-denvr
  (implies (and (not (equal (acl2::loghead 15 denvr) (acl2::logtail 17 ad)))
                (integerp offset) ;drop?
                (integerp numwords)
                )
           (equal (gacc::rd ad (gacc::write-data-words numwords denvr offset value ram))
                  (gacc::rd ad ram)))
  :hints (("Goal" :in-theory (enable gacc::write-data-words))))

(defthm rd-of-write-data-words-diff-offset
  (implies (and (not (< (acl2::loghead 16 (- (acl2::loghead 16 (acl2::logtail 1 ad)) offset)) numwords))
                (integerp offset) ;drop?
                (integerp numwords)
;                (integerp ad) ;drop?
                )
           (equal (gacc::rd ad (gacc::write-data-words numwords denvr offset value ram))
                  (gacc::rd ad ram)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::write-data-words
                              MEMBERP-OF-OFFSET-RANGE))))

(defthm find-index-of-word-ads-to-byte-ads
  (implies (and (integerp ad)
                (acl2::integer-listp word-ads)
                (list::memberp (acl2::logcdr ad) word-ads))
           (equal (list::find-index ad (gacc::word-ads-to-byte-ads word-ads))
                  (+ (acl2::logcar ad)
                     (* 2 (list::find-index (acl2::logcdr ad) word-ads)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::word-ads-to-byte-ads
                              WORD-AD-TO-BYTE-ADS
                              (:definition list::find-index)
                              acl2::equal-logapp-x-y-z
                              MEMBERP-OF-OFFSET-RANGE
                              LIST::MEMBERP-WHEN-NOT-MEMBERP-OF-CDR
                              ))))


;;; RBK: Additions begin here.  Integrate these with the rest of the book,
;;; and put them in the proper palces.

(defthm addresses-of-data-word-normalize-leading-constant
  (implies (and (syntaxp (and (quotep k)
                              (not (acl2::unsigned-byte-p 16 (cadr k)))))
                (integerp k)
                (integerp offset))
           (equal (GACC::ADDRESSES-OF-DATA-WORD cenvr (+ k offset))
                  (GACC::ADDRESSES-OF-DATA-WORD cenvr (+ (acl2::loghead 16 k) offset)))))

(defthm addresses-of-data-words-normalize-leading-constant
  (implies (and (syntaxp (and (quotep k)
                              (not (acl2::unsigned-byte-p 16 (cadr k)))))
                (integerp k)
                (integerp offset))
           (equal (GACC::ADDRESSES-OF-DATA-WORDS n cenvr (+ k offset))
                  (GACC::ADDRESSES-OF-DATA-WORDS n cenvr (+ (acl2::loghead 16 k) offset)))))

(defthm fetch-code-byte-normalize-leading-constant
  (implies (and (syntaxp (and (quotep k)
                              (not (acl2::unsigned-byte-p 16 (cadr k)))))
                (integerp k)
                (integerp offset))
           (equal (gacc::fetch-code-byte cenvr (+ k offset) ram)
                  (gacc::fetch-code-byte cenvr (+ (acl2::loghead 16 k) offset) ram))))

(defthm addresses-of-data-words-loghead-normalization
           (equal (GACC::ADDRESSES-OF-DATA-WORDS n X2
                                                 (acl2::LOGHEAD 16 x))
                  (GACC::ADDRESSES-OF-DATA-WORDS n X2
                                                 x)))

(defthm addresses-of-data-words-loghead-normalization-a
  (implies (and (integerp x)
                (integerp y))
           (equal (GACC::ADDRESSES-OF-DATA-WORDS n X2
                                                 (+ y (acl2::LOGHEAD 16 x)))
                  (GACC::ADDRESSES-OF-DATA-WORDS n X2
                                                 (+ y x))))
  :hints (("Goal" :use (:instance addresses-of-data-words-loghead-normalization
                                  (x (+ y (acl2::LOGHEAD 16 x))))
                  :in-theory (disable addresses-of-data-words-loghead-normalization
                                      GACC::OFFSET-RANGE-WRAP-OF-LOGHEAD))))

;;; RBK: Generalize
(defthm loghead-addresses-of-code-bytes-3-normalization
  (equal (acl2::LOGHEAD 31
                  (GACC::FETCH-CODE-BYTES 3 X0
                                          x
                                          X23))

         (GACC::FETCH-CODE-BYTES 3 X0
                                 x
                                 X23)))

;;; RBK: Generalize
(defthm loghead-addresses-of-code-bytes-3-normalization-a
  (equal (acl2::LOGHEAD 31
                  (+ 1 (GACC::FETCH-CODE-BYTES 3 X0
                                               x
                                               X23)))

         (+ 1 (GACC::FETCH-CODE-BYTES 3 X0
                                      x
                                      X23)))
  :hints (("Goal" :use (:instance GACC::UNSIGNED-BYTE-P-OF-FETCH-CODE-BYTES-GEN
                                  (GACC::N 24)
                                  (GACC::NUMBYTES 3)
                                  (GACC::CENVR X0)
                                  (GACC::OFFSET x)
                                  (GACC::RAM X23))
                  :in-theory (disable GACC::UNSIGNED-BYTE-P-OF-FETCH-CODE-BYTES-GEN
                                      FETCH-CODE-BYTES))))

;;; RBK: Generalize
(defthm loghead-addresses-of-code-bytes-2-normalization
  (equal (acl2::LOGHEAD 31
                  (GACC::FETCH-CODE-BYTES 2 X0
                                          x
                                          X23))

         (GACC::FETCH-CODE-BYTES 2 X0
                                 x
                                 X23)))

;;; RBK: Generalize
(defthm loghead-addresses-of-code-bytes-2-normalization-a
  (equal (acl2::LOGHEAD 31
                  (+ 1 (GACC::FETCH-CODE-BYTES 2 X0
                                               x
                                               X23)))

         (+ 1 (GACC::FETCH-CODE-BYTES 2 X0
                                      x
                                      X23)))
  :hints (("Goal" :use (:instance GACC::UNSIGNED-BYTE-P-OF-FETCH-CODE-BYTES-GEN
                                  (GACC::N 24)
                                  (GACC::NUMBYTES 2)
                                  (GACC::CENVR X0)
                                  (GACC::OFFSET x)
                                  (GACC::RAM X23))
                  :in-theory (disable GACC::UNSIGNED-BYTE-P-OF-FETCH-CODE-BYTES-GEN
                                      FETCH-CODE-BYTES))))

;;; RBK: Generalize
(defthm loghead-addresses-of-code-bytes-1-normalization
  (equal (acl2::LOGHEAD 31
                  (GACC::FETCH-CODE-BYTES 1 X0
                                          x
                                          X23))

         (GACC::FETCH-CODE-BYTES 1 X0
                                 x
                                 X23)))

;;; RBK: Generalize
(defthm loghead-addresses-of-code-bytes-1-normalization-a
  (equal (acl2::LOGHEAD 31
                  (+ 1 (GACC::FETCH-CODE-BYTES 1 X0
                                               x
                                               X23)))

         (+ 1 (GACC::FETCH-CODE-BYTES 1 X0
                                      x
                                      X23)))
  :hints (("Goal" :use (:instance GACC::UNSIGNED-BYTE-P-OF-FETCH-CODE-BYTES-GEN
                                  (GACC::N 24)
                                  (GACC::NUMBYTES 1)
                                  (GACC::CENVR X0)
                                  (GACC::OFFSET x)
                                  (GACC::RAM X23))
                  :in-theory (disable GACC::UNSIGNED-BYTE-P-OF-FETCH-CODE-BYTES-GEN))))

;;; RBK: Generalize?
(defthm size-of-fetch-code-bytes-3
  (acl2::unsigned-byte-p 31 (GACC::FETCH-CODE-BYTES 3 X0
                                              x
                                              X23)))

;;; RBK: Generalize?
(defthm size-of-fetch-code-bytes-3-a
  (acl2::unsigned-byte-p 31 (+ 1 (GACC::FETCH-CODE-BYTES 3 X0
                                                   x
                                                   X23)))
  :hints (("Goal" :use (:instance GACC::UNSIGNED-BYTE-P-OF-FETCH-CODE-BYTES-GEN
                                  (GACC::N 24)
                                  (GACC::NUMBYTES 3)
                                  (GACC::CENVR X0)
                                  (GACC::OFFSET x)
                                  (GACC::RAM X23))
           :in-theory (disable GACC::UNSIGNED-BYTE-P-OF-FETCH-CODE-BYTES-GEN
                                      FETCH-CODE-BYTES))))

(in-theory (disable g* s* x*))
(in-theory (enable
            (:induction s*)
            (:induction g*)
            (:induction x*)
            ))

(in-theory (disable
            DISJOINT-MESH-G*-FIX
            DISJOINT-G*-BLKS-G*-FIX-2
            DISJOINT-BLKS-G*-FIX
            DISJOINT-MESH-FROM-X*-INSTANCE
            DISJOINT-BLKS-FROM-X*-INSTANCE
            DISJOINT-BLK-SUBBAGP-RIGHT
;            bag::DISJOINT-CONS
;            DEFAULT-CDR
        ;    DEFAULT-CAR
            (:TYPE-PRESCRIPTION BINARY-APPEND)
            (:TYPE-PRESCRIPTION acl2::APPEND-TRUE-LISTP-TYPE-PRESCRIPTION)
            ))

(in-theory (disable
            DISJOINT-BLK-SUBBAGP-LEFT
;            bag::DISJOINT-of-APPEND
            blk-disjoint-from-blk-1
            blk-disjoint-from-blk-2
;            DISJOINT
            bag::UNIQUE-of-APPEND ;remove?
;            bag::SUBBAGP-IMPLIES-SUBBAGP-APPEND-REC
        ;    bag::SUBBAGP-IMPLIES-SUBBAGP-APPEND-CAR
;            bag::REMOVE-bag-APPEND
;            bag::META-SUBBAGP
            ))



;trying with just the regular unicity-of-0
;; ;why??
;; (defthm integerp-unicity-of-0
;;   (implies
;;    (integerp x)
;;    (equal (+ 0 x) x)))
;;
;;(in-theory (disable UNICITY-OF-0))

;; Typically, there will be a uniqueness hyp. in your theorem.  By
;; starting out in a state in which this statement can be simplified
;; as much as possible without disturbing the rest of the terms, you
;; will probably save quite a bit of time in the long run.

(deftheory simplify-uniqueness
  (union-theories
   `(
     (BLKS)
     (MAX-OFFSET)
     (MESH)
     FLATTEN
     SYNTAX-ATOM
     SYNTAX-CONSP-OR-SYMBOL
     list::append-associative
;     bag::APPEND-NIL
;     INTEGERP-UNICITY-OF-0
     OPEN-BLKS
     OPEN-G*
     OPEN-MESH
     TRUE-LISTP-BLK
     TRUE-LISTP-MESH
     (:TYPE-PRESCRIPTION RX)
     (:TYPE-PRESCRIPTION UNIQUE))
   (theory 'ground-zero)))

(in-theory (disable
            ;;UNIQUE RULES
            ;; bag::UNIQUE-DESPITE-REMOVE-bag
            bag::*TRIGGER*-SYNTAX-EV-SYNTAX-SUBBAGP ;;bzo move this disable to bags/top?
            ;;bag::SUBBAGP-UNIQUENESS
            UNIQUE-BLKS-PTR-INDEPENDENT-OF-PTR
            UNIQUE-BLK
            UNIQUE-BLK-REC
            ;;bag::UNIQUE-of-APPEND
            ;;UNIQUE
            ;;DISJOINT RULES
            bag::*TRIGGER*-UNIQUE-SUBBAGPS-IMPLIES-DISJOINTNESS
            bag::*TRIGGER*-SUBBAGP-PAIR-DISJOINT
            ;;bag::SUBBAGP-DISJOINT-COMMUTE
            ;;    bag::SUBBAGP-DISJOINT
            DISJOINT-MESH-G*-FIX
            DISJOINT-G*-BLKS-G*-FIX-2
            DISJOINT-BLKS-G*-FIX
            DISJOINT-MESH-FROM-X*-INSTANCE
            DISJOINT-BLKS-FROM-X*-INSTANCE
            DISJOINT-BLK-PTR-BLKS-PTR-INDEPENDENT-OF-PTR-0-HYP
            DISJOINT-BLK-PTR-BLKS-PTR-INDEPENDENT-OF-PTR-0-CONCLUSION
            DISJOINT-BLK-PTR-BLKS-PTR-INDEPENDENT-OF-PTR
            DISJOINT-RELOCATION
            ;;DISJOINT-BLK-SUBBAGP-LEFT
            ;;DISJOINT-BLK-SUBBAGP-RIGHT
            disjoint-of-blk-recs-1
            disjoint-of-blk-recs-2
            DISJOINT-BLK-REC-SUBBAGP-LEFT
            DISJOINT-BLK-REC-SUBBAGP-RIGHT
            DISJOINT-BLK-REC-SUBBAGP
            ;;bag::DISJOINT-of-APPEND
            bag::DISJOINT-COMMUTATIVE ;;bzo really?
            ;;DISJOINT-NIL
            ;;bag::DISJOINT-CONS
            ;;DISJOINT

            ;;SUBBAGP RULES
            bag::V2-SYNTAX-REMOVE-bag-IMPLICATION
            bag::V2-SYNTAX-REMOVE-bag-IMPLICATION-LEMMA
            ;;PERM-SUBBAGP-SUBBAGP-2
            bag::V1-SYNTAX-REMOVE-bag-IMPLICATION
            ;;V1-SYNTAX-REMOVE-LIST-IMPLICATION-LEMMA
            ;;bag::SUBBAGP-REMOVE-bag-SUBBAGP-APPEND
            ;;bag::SUBBAGP-MEMBERp-REMOVE-1
            ;;SUBBAGP-PERM-SUBBAGP-CONS
            ;;bag::CONSP-SUBBAGP
            ;;bag::PERM-SUBBAGP-SUBBAGP
            ;;bag::SUBBAGP-APPEND-NIL
            bag::SYNTAX-SUBBAGP-IMPLEMENTS-SUBBAGP
            ;;REMOVE-1-SUBBAGP-APPEND
            bag::V0-REMOVE-1-SUBBAGP
            ;;bag::SUBBAGP-CDR-REMOVE-1
            ;;bag::SYNTAX-REMOVE-bag-1-NOT bzo this disappeared
            ;;V1-REMOVE-1-SUBBAGP
            ;;bag::SUBBAGP-REMOVE-bag-APPEND
            bag::SYNTAX-REMOVE-bag-1-IMPLEMENTS-SUBBAGP
            ;;bag::SUBBAGP-APPEND
            BLK-REC-LOWER-SUBBAGP
            BLK-UPPER-SUBBAGP
            BLK-REC-UPPER-SUBBAGP
            ;;bag::SUBBAGP-REMOVE-BAG
            ;;bag::SUBBAGP-REMOVE
            ;;SUBBAGP-X-X we want this one
            ;;bag::SUBBAGP-REMOVE-1
            ;;bag::SUBBAGP-IMPLIES-REMOVE-bag
            ;;bag::NON-CONSP-SUBBAGP
            ;;SUBBAGP-CDR
            ;;bag::SUBBAGP-CHAINING
            ;;SUBBAGP-IMPLIES-COMMON-MEMBERS-ARE-IRRELEVANT
            ;;SUBBAGP-APPEND-APPEND
            ;;SUBBAGP-APPEND-APPEND-LEFT
            ;;SUBBAGP-IMPLIES-SUBBAGP-APPEND-CAR
            ;;SUBBAGP-IMPLIES-SUBBAGP-APPEND-REC
            ;;bag::SUBBAGP-CONS
            ;;SUBBAGP-IMPLIES-SUBBAGP-CONS
            ;;SUBBAGP already out

            ;;MEMBERp RULES
            ;;bag::SYNTAX-MEMBERP-IMPLEMENTS-MEMBERP
            ;;bag::UNIQUE-REMOVE-1
            ;;bag::UNIQUE-MEMBERP-REMOVE
            ;;bag::SUBBAGP-CONS-CAR-MEMBERP
            MEMBERP-RELOCATE-BLK
            BLK-NON-MEMBERSHIP-MORE
            BLK-NON-MEMBERSHIP-LESS
            BLK-MEMBERSHIP
            BLK-MEMBERSHIP-SUBBAGP
            BLK-REC-MEMBERSHIP-SUBBAGP
            BLK-REC-MEMBERSHIP
            BLK-REC-NON-MEMBERSHIP-MORE
            BLK-REC-NON-MEMBERSHIP-LESS
            ;;bag::NOT-MEMBERP-IMPLIES-NOT-MEMBERP-REMOVE-1
            ;;bag::MEMBERP-FROM-DISJOINT-MEMBERP
            ;;bag::SUBBAGP-IMPLIES-MEMBERSHIP
            ;;bag::REMOVE-bag-ADDS-NO-TERMS
            ;;bag::MEMBERP-APPEND
            ;;bag::MEMBERP-SUBBAGP-NOT-CONSP-VERSION
            ;;bag::MEMBERP-SUBBAGP
            ;;bag::MEMBERP-X-REMOVE-X-IMPLIES-MEMBERP-X-REMOVE-1-Y
            ;;bag::MEMBERP-REMOVE
            ;;bag::memberp-remove-1-lemma ;;MEM-REM
            ;;MEMBERP
            ))


(defthm unsigned-byte-p--of--rv
  (implies (or (equal size 8)
               (equal size 16)
               (equal size 32)) ;;improve using a wintn rule?
  (acl2::unsigned-byte-p size (rv size gacc::off gacc::base gacc::spec))))

;;(in-theory (enable WFIXN-REWRITE-TO-LOGHEAD))

;;; ;this is a duplicate, because I wanted it to come last. -huh?
;; (defthmd unsigned-byte-p-wintn-equality-2
;;   (implies (or (equal size 8)
;;                (equal size 16)
;;                (equal size 32))
;;            (equal (gacc::wintn 8 size x)
;;                   (acl2::unsigned-byte-p size x))))


(defun set::rkeys (r)
  (list::2set (rkeys r)))

;;
;; mypush (turn a record into a typed-record)
;;

(defun mypush-aux (keys r)
  (if (set::empty keys)
      nil ;the empty typed record
    (gacc::wr (set::head keys)
              (g (set::head keys) r)
              (mypush-aux (set::tail keys) r))))

(defun mypush (r)
  (mypush-aux (set::rkeys r) r))


(defthm rd-of-mypush-aux
  (equal (gacc::rd a (mypush-aux rkeys r))
         (if (set::in a rkeys)
             (loghead 8 (g a r))
           0)))


(defthm rd-of-mypush
  (equal (gacc::rd a (mypush r))
         (if (set::in a (set::rkeys r))
             (loghead 8 (g a r))
           0)))

(defthm memory-clr-of-mypush-aux
  (equal (gacc::memory-clr key (mypush-aux rkeys r))
         (mypush-aux rkeys (clr key r))))

;; ;what we really need is the analogous theorem for insert?
;; (defthm mypush-aux-of-cons
;;   (equal (mypush-aux (cons a rkeys) r)
;;          (gacc::wr a (g a r) (mypush-aux rkeys r)))
;;   :hints (("Goal" :induct t
;;            :expand ((MYPUSH-AUX (CONS A (SET::TAIL RKEYS))
;;                                  R)
;;                     (MYPUSH-AUX (CONS A RKEYS) R)
;;                     (SET::HEAD (CONS A RKEYS))
;;                     (SET::SETP (CONS A RKEYS))
;;                     (SET::EMPTY (CONS A RKEYS))
;;                     (SET::TAIL (CONS A RKEYS)))
;;            :in-theory (disable GACC::WR==R!)
;;            :do-not '(generalize eliminate-destructors))))


(defun my-ind (a rkeys r)
  (if (set::empty rkeys)
      (list a rkeys r)
    (if (equal a (set::head (set::insert a rkeys)))
        (list a rkeys r)
      (my-ind a (set::tail rkeys) (s (set::head rkeys) (g (set::head rkeys) r) r)))))



;clean up conclusion?
(defthmd car-of-insert
  (equal (CAR (SET::INSERT a x))
         (COND ((SET::EMPTY X) A)
               ((EQUAL (SET::HEAD X) A) (SET::HEAD X))
               ((<< A (SET::HEAD X)) A)
               (T (SET::HEAD X))))
  :hints (("Goal" :expand (SET::INSERT A X)
           :in-theory (enable SET::INSERT SET::HEAD))))

(defthm set-hack
  (implies (not (equal a (set::head (set::insert a s))))
           (equal (set::tail (set::insert a s))
                  (set::insert a (set::tail s))))
  :otf-flg t
  :hints (
          ("Goal" :expand ((SET::INSERT A S) ;prove a setp of cons rule?
                           (SET::SETP S)
                           (SET::INSERT A NIL)
                           (SET::INSERT A (CDR S))
                           (SET::SETP (CDDR S))
                           (SET::SETP (CDR S))
                           (:free (x y) (set::setp (cons x y)))
                           )
           :in-theory (e/d (car-of-insert SET::EMPTY SET::HEAD SET::tail SET::SFIX) ( SET::PICK-A-POINT-SUBSET-STRATEGY))
           :do-not '(generalize eliminate-destructors))))

(defthm set-hack2
  (implies (not (equal a (set::head (set::insert a s))))
           (equal (SET::HEAD (SET::INSERT A s))
                  (SET::HEAD s)))
  :otf-flg t
  :hints (("Goal" :expand ((SET::INSERT A S) ;prove a setp of cons rule?
                           (SET::SETP S)
                           (SET::INSERT A NIL)
                           (SET::INSERT A (CDR S))
                           (SET::SETP (CDDR S))
                           (SET::SETP (CDR S))
                           (:free (x y) (set::setp (cons x y)))
                           )
           :in-theory (e/d (car-of-insert SET::EMPTY SET::HEAD SET::tail SET::SFIX) ( SET::PICK-A-POINT-SUBSET-STRATEGY))
           :do-not '(generalize eliminate-destructors))))



(defthm not-in-when-<<-car
 (IMPLIES (AND ;A (SET::SETP S)
               ;(NOT (EQUAL (CAR S) A))
               (<< A (CAR S))
               ;(CONSP S)
               )
          (not (set::in a s)))
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
          :expand ((SET::EMPTY S)
                   (SET::SETP S))
          :in-theory (enable SET::HEAD set::tail))))



(defthm tail-of-insert-when-equal-head-of-insert
  (implies (and (syntaxp (not (equal a ''nil)))
                (equal a (set::head (set::insert a s))))
           (equal (set::tail (set::insert a s))
                  (set::delete a s)))
  :otf-flg t
  :hints (("Goal" :expand ((SET::INSERT A S) ;prove a setp of cons rule?
                           (SET::SETP S)
                           (SET::INSERT A NIL)
                           (SET::INSERT A (CDR S))
                           (SET::SETP (CDDR S))
                           (SET::SETP (CDR S))
                           (:free (x y) (set::setp (cons x y)))
                           )
           :in-theory (e/d (car-of-insert SET::EMPTY SET::HEAD SET::tail SET::SFIX) ( SET::PICK-A-POINT-SUBSET-STRATEGY))
           :do-not '(generalize eliminate-destructors))))



;combine these cases?
(defthm mypush-aux-of-insert
  (equal (mypush-aux (set::insert a rkeys) r)
         (if (set::in a rkeys)
             (mypush-aux rkeys r)
           (gacc::wr a (g a r) (mypush-aux rkeys r))))
  :otf-flg t
  :hints (("Goal" :induct (my-ind a rkeys r)
           :expand ((MYPUSH-AUX (SET::INSERT A RKEYS) R))
           :in-theory (disable GACC::WR==R!
                               )
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))


(defthm memory-clr-of-mypush-aux2
  (equal (gacc::memory-clr key (mypush-aux rkeys r))
         (mypush-aux (set::delete key rkeys) r))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


;rename to say insert
(defthm mypush-aux-of-cons-irrel
  (implies (not (g key r))
           (equal (mypush-aux (set::insert key rkeys) r)
                  (mypush-aux rkeys r)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))




;drop?
(defthm mypush-aux-of-insert-irrel-of-clr
  (equal (mypush-aux (set::insert key rkeys) (clr key r))
         (mypush-aux rkeys (clr key r)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


(defthm mypush-irrel
  (implies (not (set::in key rkeys))
           (equal (mypush-aux rkeys (clr key r))
                  (mypush-aux rkeys r)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


(defthm mypush-aux-of-clr
  (equal (mypush-aux rkeys (clr a r))
         (mypush-aux (set::delete a rkeys) r))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


(defthm mypush-irrel2
  (implies (not (set::in key rkeys))
           (equal (mypush-aux rkeys (s key v r))
                  (mypush-aux rkeys r)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

;; (thm
;;  (equal (mypush-aux (set::insert a rkeys) (s a v r))
;;         (gacc::wr a v (mypush-aux rkeys r)))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

;; (thm
;;  (equal (mypush-aux (set::rkeys r) (s a v r))
;;         (gacc::wr a v (mypush-aux (set::rkeys r) r))))

;for dave
(defthm mypush-of-s
  (equal (mypush (s a v r))
         (gacc::wr a v (mypush r)))
  :otf-flg t)

;for dave
(defthm mypush-of-sp
  (equal (mypush (cpath::sp (list a) v r))
         (gacc::wr a v (mypush r)))
  :hints (("Goal" :in-theory (enable cpath::sp))))

;need a way to get the keys of a typed record...  -can it be rkeys?
;then prove keys of wr = blah...

;;
;; my-lift (turn a typed-record into a regular record)
;;

;keys "bound" to 0 don't show up in the typed record (since 0 is the default
;value for typed records) and so become keys "bound" to nil in the record
;(such keys don't show up, since nil is the default value for records).
(defun mylift-aux (keys tr)
  (if (set::empty keys)
      nil ;the empty record
    (s (set::head keys)
       (gacc::rd (set::head keys) tr)
       (mylift-aux (set::tail keys) tr))))

;bzo
(defun mylift (tr)
  (mylift-aux (set::rkeys tr) tr))

(defthm rkeys-of-wr
  (equal (set::rkeys (gacc::wr a v tr))
         (if (gacc::wf-usbp8 (g a tr))
             (if (gacc::usbp8-zp v)
                 (if (cdr (g a tr))
                     (set::insert a (set::rkeys tr))
                   (set::delete a (set::rkeys tr)))
               (set::insert a (set::rkeys tr)))
           (if (gacc::usbp8-zp v)
               (set::rkeys tr)
             (set::insert a (set::rkeys tr)))))
  :hints (("Goal" :expand ((gacc::wr a v tr))
;          :induct nil
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))

(defthm g-of-mylift-aux
  (equal (g a (mylift-aux rkeys tr))
         (if (set::in a rkeys)
             (loghead 8 (gacc::rd a tr))
           nil)))


(defthm g-of-mylift
  (equal (g a (mylift tr))
         (if (set::in a (set::rkeys tr))
             (loghead 8 (gacc::rd a tr))
           nil)))

(defun val-fix (v)
  (if (equal 0 (loghead 8 v))
      nil
     (loghead 8 v)))

(defthm wr-of-0-is-clr
  (implies (EQUAL (LOGHEAD 8 V) 0)
           (equal (GACC::WR A V TR)
                  (gacc::memory-clr A TR))))


;bzo improve CLR-OVER-CLR?

(defthm clr-of-clr-match-hack
  (IMPLIES (EQUAL (CLR b r1)
                  (CLR b r2))
           (EQUAL (equal (CLR b (CLR a r1))
                         (CLR b (CLR a r2)))
                  t))
  :hints (("Goal" :cases ((equal a b)))))

(defthm mylist-aux-of-insert
  (equal (mylift-aux (set::insert a rkeys) tr)
         (if (set::in a rkeys)
             (mylift-aux rkeys tr)
           (s a (gacc::rd a tr) (mylift-aux rkeys tr))))
  :otf-flg t
  :hints (("Goal" :induct (my-ind a rkeys rt)
           :expand ((MYLIFT-AUX (SET::INSERT A RKEYS) tR))
           :in-theory (disable GACC::WR==R!
                               )
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))

(defthm delete-of-head
  (equal (set::delete (set::head s) s)
         (if (set::setp s)
             (set::tail s)
           nil ;the empty set - is there a function for that?
           ))
  :hints (("Goal" :in-theory (enable SET::EMPTY))))

;could be expensive?
(defthm empty-means-tail-nil
  (implies (set::empty s)
           (equal (set::tail s)
                  nil))
  :hints (("Goal" :in-theory (enable set::empty set::tail set::sfix))))

;bzo may loop with defn delete or something?
(defthmd delete-from-tail-when-not-head
  (implies (not (equal key (set::head s)))
           (equal (set::delete key (set::tail s))
                  (set::delete (set::head s) (set::delete key s))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((set::delete key s)))))

(defthm clr-of-mylift-aux
  (equal (clr key (mylift-aux rkeys tr))
         (mylift-aux (set::delete key rkeys) (gacc::memory-clr key tr)))
  :hints (("Goal" :in-theory (disable SET::DELETE)
           :expand ((SET::DELETE KEY RKEYS))
           :do-not '(generalize eliminate-destructors))))


;bzo bad name? really this checks the values?
(defun check-tr-keys (keys tr)
  (if (set::empty keys)
      t
    (let* ((val (g (set::head keys) tr)))
      (and (equal nil (cdr val)) ;(equal 1 (len val))
           (unsigned-byte-p 8 (car val))
           (not (equal 0 (car val)))
           (check-tr-keys (set::tail keys) tr)
           ))))

;; ;drop?
;; (defun wfr-weak (r)
;;   (and (rcdp r)
;;        (not (ifrp r)) ;;should really just use a typed version of ifrp?
;;        ))


(defun wf-tr (tr)
  (and ;;(wfr-weak tr) ;;
       (wfr tr)
       (check-tr-keys (set::rkeys tr) tr)))

(defun wf-tr-weak (tr)
  (and ;;(wfr-weak tr) ;;
;       (wfr tr)
       (check-tr-keys (set::rkeys tr) tr)))

(defthm mylift-of-wr-1
  (implies (and (wf-tr-weak tr)
                (not (EQUAL 0 (LOGHEAD 8 V))))
           (equal (mylift (gacc::wr a v tr))
                  (s a (val-fix v) (mylift tr))))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable ;gacc::wr
                       ))))

(defthm cdr-of-g-nil-when-in-keys
  (implies (and (check-tr-keys keys tr)
                (set::in k keys)
                )
           (not (cdr (g k tr))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm sfix-of-rkeys
  (equal (SET::SFIX (SET::RKEYS TR))
         (SET::RKEYS TR))
  :hints (("Goal" :in-theory (enable RKEYS))))

;false
;; (thm
;;  (implies (rcdp r)
;;           (not (ifrp r)))
;;  :hints (("Goal" :in-theory (enable rcdp ifrp))))

(defthm wfr-implies-wfr-of-cdr
  (implies (wfr tr)
           (wfr (cdr tr)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand (ifrp (cdr tr))
           :in-theory (enable wfr ifrp rcdp wfkeyed))))

;; (defthm wfr-weak-implies-wfr-weak-of-cdr
;;   (implies (wfr-weak tr)
;;            (wfr-weak (cdr tr)))
;;   :otf-flg t
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :expand (ifrp (cdr tr))
;;            :in-theory (enable wfr ifrp rcdp wfkeyed))))


;; (defthm wfr-weak-cancellations
;;   (implies (wfr-weak r)
;;            (and (equal (rcd->acl2 r) r)
;;                 (equal (acl2->rcd r) r)))
;;   :hints (("Goal" :in-theory (enable rcd->acl2 acl2->rcd))))

(defthm wf-tr-cancellations
  (implies (wf-tr r)
           (and (equal (rcd->acl2 r) r)
                (equal (acl2->rcd r) r)))
  :hints (("Goal" :in-theory (enable rcd->acl2 acl2->rcd))))


;; (defthm wf-tr-implies-wf-tr-of-cdr
;;   (implies (wf-tr tr)
;;            (wf-tr (cdr tr)))
;;   :otf-flg t
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :expand (ifrp (cdr tr))
;;            :in-theory (enable wfr ifrp rcdp wfkeyed))))


(defthm not-consp-g-of-cdr-but-consp-g
  (IMPLIES (AND (NOT (CONSP (G A (CDR TR))))
                (CONSP (G A TR))
                (WFR TR) ;was wfr-weak
                )
           (EQUAL (CAAR TR) A))
  :hints (("Goal" :in-theory (enable g))))

(defthm consp-g-means-in-keys
  (implies (and (consp (g a tr))
                (wfr tr)
                )
           (set::in a (set::rkeys tr)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))
;;         :in-theory (enable rkeys key-set))))

(defthm g-of-caar
  (implies (wfr tr)
           (equal (g (caar tr) tr)
                  (cdar tr)
                  ))
  :hints (("Goal" :in-theory (enable g)
           :do-not '(generalize eliminate-destructors))))

(defthm cons-g-cdr-means-consp-g
  (implies (and (consp (g a (cdr tr)))
                (wfr tr))
           (consp (g a tr)))
  :hints (("Goal" :in-theory (enable g wfr))))

;bzo disable?
(defthm cdar-of-wfr-non-nil
  (implies (and (consp tr)
                (wfr tr))
           (cdar tr))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand (rcdp tr)
           :in-theory (enable wfr rcdp wfkeyed wfkey))))

;bzo combine?
;; (defthm not-g-means-not-in-rkeys
;;   (implies (and (not (g a tr))
;;                 (wfr tr))
;;            (not (set::in a (set::rkeys tr))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;; ;           :expand ((G A TR))
;;            :in-theory (enable rkeys key-set))))

(defthm mylift-irrel
  (implies (not (set::in key keys))
           (equal (mylift-aux keys (gacc::memory-clr key tr))
                  (mylift-aux keys tr)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


;; (defthm mylift-aux-of-clr
;;   (equal (mylift-aux rkeys (gacc::memory-clr a t))
;;          (mylift-aux (set::delete a rkeys) t))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors))))


(defthm rd-of-s-irrel
  (implies (not (equal key1 key2))
           (equal (GACC::RD key1 (S KEY2 V TR))
                  (GACC::RD key1 TR)))
  :hints (("Goal" :in-theory (enable GACC::RD))))

(defthm mylift-irrel2
  (implies (not (set::in key rkeys))
           (equal (mylift-aux rkeys (s key v tr))
                  (mylift-aux rkeys tr)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


;; (thm
;;  (IMPLIES (AND (WFR TR)
;;                ;(CHECK-TR-KEYS (SET::RKEYS TR) TR)
;;                ;(NOT (CONSP (G A TR)))
;;                )
;;           (EQUAL (MYLIFT-AUX (SET::DELETE A (SET::RKEYS TR))
;;                              (GACC::WR A 0 TR))
;;                  (MYLIFT-AUX (SET::RKEYS TR)
;;                              (GACC::WR A 0 TR)))))

(defthmd check-tr-keys-lemma
  (IMPLIES (and (CHECK-TR-KEYS keys TR)
                (set::in a keys)
                (consp tr))
           (NOT (EQUAL (LOGHEAD 8 (CAR (G A TR))) 0))))

(defthmd check-tr-keys-lemma2
  (IMPLIES (and (CHECK-TR-KEYS keys TR)
                (set::in a keys)
                (consp tr))
           (UNSIGNED-BYTE-P 8 (CAR (G A TR)))))

(defthm mylift-of-wr-0-case
 (implies (and (wf-tr tr) ;(wfr tr)
               (equal 0 (loghead 8 v)))
          (equal (mylift (gacc::wr a v tr))
                 ;if what was there was well-formed, we get 0.  otherwise (including if it was 0 before!), we get what was there!
                 (s a nil (mylift tr))))
 :otf-flg t
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
        ;  :cases ((SET::in A (SET::RKEYS TR)))
          :use ((:instance check-tr-keys-lemma (keys (set::rkeys tr)))
                (:instance check-tr-keys-lemma2 (keys (set::rkeys tr))))
          :in-theory (e/d ( ;gacc::wr
                           GACC::MEMORY-CLR
                           )
                          (
                           set::rkeys
                           WR-OF-0-IS-CLR
                           LOGHEAD*-BETTER ;bzo why isn't this disabled?
                           LOGCAR-LOGCDR-ELIM
                           )))))

(in-theory (disable LOGHEAD*-BETTER))

;for dave
(defthm mylift-of-wr
  (implies (wf-tr tr)
           (equal (mylift (gacc::wr a v tr))
                  (s a (val-fix v) (mylift tr))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :use ((:instance mylift-of-wr-0-case)
                 (:instance mylift-of-wr-1))
           :in-theory (disable MYLIFT g-of-mylift))))

;see S-PRESERVES-WFR (should WFKEY be enabled?)

;bzo maybe wf-tr should allow nil keys?

(defun check-tr-val (val)
  (and (UNSIGNED-BYTE-P 8 VAL)
       (NOT (EQUAL 0 VAL))))

(defun check-tr-entry (val)
  (and (equal nil (cdr val))
       (check-tr-val (car val))))

;bzo really what's checked by CHECK-TR-KEYS is the value -rename

(defthm check-tr-keys-of-s
  (implies (and (check-tr-keys keys tr)
                (check-tr-entry v) ;the whole entry, not the val
                )
           (check-tr-keys keys (s a v tr)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


(defthm CHECK-TR-KEYS-of-s-irrel
  (implies (not (set::in a keys))
           (equal (CHECK-TR-KEYS keys (S A NIL TR))
                  (CHECK-TR-KEYS keys TR))))

(defthm delete-when-would-be-head
  (implies (equal a (set::head (set::insert a keys)))
           (equal (set::delete a keys)
                  (if (set::in a keys)
                      (set::tail keys)
                    (set::sfix keys))))
  :hints (("Goal" :in-theory (enable SET::SFIX ;bzo
                                     ))))

(defthm car-of-insert-of-nil
  (equal (car (set::insert k nil))
         k)
  :hints (("Goal" :in-theory (enable set::insert))))

(defthm check-tr-keys-of-insert
  (equal (check-tr-keys (set::insert a keys) tr)
         (let* ((val (g a tr)))
           (and (equal nil (cdr val))
                (unsigned-byte-p 8 (car val))
                (not (equal 0 (car val)))
                (check-tr-keys keys tr))))
  :otf-flg t
  :hints (("Goal" :induct (my-ind a keys r)
           :expand ((CHECK-TR-KEYS (SET::INSERT A KEYS) tR)
                    )
           :in-theory (disable gacc::wr==r! )
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))

(defthm check-tr-keys-of-delete
  (implies (check-tr-keys keys tr)
           (check-tr-keys (set::delete a keys) tr))
  :hints (("Goal"
           :expand (CHECK-TR-KEYS (SET::INSERT (SET::HEAD KEYS)
                                               (SET::DELETE A (SET::TAIL KEYS)))
                                  TR)
           :do-not '(generalize eliminate-destructors))))

(defthm consp-g-when-in-keys-and-check-tr-keys
  (implies (and (check-tr-keys keys tr)
                (set::in a keys)
                )
           (consp (g a tr)))
  :hints (("Goal" :in-theory (enable check-tr-keys))))

;replace the consp-g-version?
(defthm g-means-in-keys
  (implies (and (g a tr)
                (wfr tr)
                )
           (set::in a (set::rkeys tr)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))
;;           :in-theory (enable rkeys key-set g))))

(defthm consp-g-when-g-and-check-tr-keys
  (implies (and (check-tr-keys (set::rkeys tr) tr)
                (g a tr) ;is not nil
                (wfr tr)
                )
           (consp (g a tr)))
  :hints (("Goal" :use (:instance consp-g-when-in-keys-and-check-tr-keys (keys (set::rkeys tr)))
           :in-theory (e/d (check-tr-keys) (consp-g-when-in-keys-and-check-tr-keys)))))

(defthm set::rkeys-s
  (equal (set::rkeys (s a v r))
         (if v (set::insert a (set::rkeys r))
           (set::delete a (set::rkeys r)))))

;for dave
(defthm wf-tr-of-wr
  (implies (and (wf-tr tr)
                a ;that is, a is not nil
                )
           (wf-tr (gacc::wr a v tr)))
  :otf-flg t
  :hints (("Goal" :expand (CHECK-TR-KEYS (SET::INSERT A NIL)
                                         (S A (LIST (LOGHEAD 8 V)) NIL))
           :use ((:instance check-tr-keys-lemma2 (keys (set::rkeys tr)))
                 (:instance check-tr-keys-lemma (keys (set::rkeys tr))))
           :in-theory (e/d (GACC::WR wfkey) (set::rkeys
                                             check-tr-keys-lemma2
                                             check-tr-keys-lemma)))))


;for dave
(defthm mylift-of-wr-sp-version
  (implies (wf-tr tr)
           (equal (mylift (gacc::wr a v tr))
                  (cpath::sp (list a) (val-fix v) (mylift tr))))
  :hints (("Goal" :in-theory (e/d ( CPATH::SP) (MYLIFT WF-TR val-fix)))))

(defun non-nil (x)
  (declare (xargs :guard t))
  (not (null x)))

;; ;bzo dup?
;; (defun all-non-nil (lst)
;; ;  (declare (xargs :guard t))
;;   (if (set::empty lst)
;;       t
;;     (and (not (null (set::head lst)))
;;          (all-non-nil (set::tail lst)))))

(defthm head-non-nil-when-all-non-nil
  (implies (and (set::all<non-nil> s)
                (not (set::empty s)))
           (set::head s))
  :hints (("Goal" :in-theory (enable))))

(defthm wfr-of-mylift-aux
  (implies (set::all<non-nil> keys)
           (wfr (mylift-aux keys tr)))
  :hints (("Goal" :in-theory (enable wfkey)
           :do-not '(generalize eliminate-destructors))))

(defthm rkeys-of-mylift-aux
  (implies (and (wf-tr tr)
                (set::all<non-nil> keys)
                (set::setp keys))
           (equal (set::rkeys (mylift-aux keys tr))
                  keys))
  :hints (("Goal" :in-theory (enable SET::EMPTY))))

#+joe
(defthm wfkeyed-implies-not-nil-memberp
  (implies
   (wfkeyed r)
   (not (bag::memberp nil (alist::Keys r))))
  :hints (("Goal" :in-theory (enable wfkeyed alist::keys bag::memberp))))

#+joe
(defthm wfr-implies-not-nil-memberp
  (implies
   (wfr r)
   (not (bag::memberp nil (rkeys r))))
  :hints (("Goal" :in-theory (enable wfr rkeys))))

(defthm all-non-nil-of-rkeys
  (implies (and (wfkeyed tr)
                (wfr tr))
           (set::all<non-nil> (set::rkeys tr)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))
;;           :in-theory (enable ;wfr
;;                       wfkeyed wfkey rkeys))))

(defthm all-non-nil-of-rkeys2
  (implies (wf-tr tr)
           (set::all<non-nil> (SET::RKEYS TR)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable wfr WFKEYED))))

(defthm empty-list2set
  (equal (set::empty (list::2set list))
         (not (consp list)))
  :hints (("Goal" :in-theory (e/d (list::2set)
                                  (SET::|2SET-REWRAP|)))))

(defthm empty-rkeys-when-wfr
  (IMPLIES (AND  (WFR TR))
           (equal (SET::EMPTY (SET::RKEYS TR))
                  (NOT TR)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))
;;           :in-theory (enable wfr RKEYS))))

(defun ind (keys tr)
  (declare (xargs :verify-guards nil))
  (if (or (not (set::setp keys))
          (set::empty keys))
      (list keys tr)
    (ind (set::tail keys)
         (GACC::MEMORY-CLR (SET::HEAD (SET::RKEYS TR)) tr);
         ;(gacc::wr (set::head keys) (gacc::rd (set::head keys) tr) tr)
         )))

(in-theory (disable set::rkeys))

(defthm rkeys-of-memory-clr
  (implies (and (rcdp tr) ;; (wfr tr)
                (not (ifrp tr)))
           (equal (set::rkeys (gacc::memory-clr a tr))
                  (if (gacc::wf-usbp8 (g a tr))
                      (if (cdr (g a tr))
                          (set::insert a (set::rkeys tr))
                        (set::delete a (set::rkeys tr)))
                    (set::rkeys tr))))
  :hints (("Goal" :in-theory (e/d (gacc::memory-clr) (WR-OF-0-IS-CLR)))))

;bzo move?
(defthm wfr-of-wr
  (implies (and (wfr tr)
                (wfkey a))
           (wfr (GACC::WR A v TR)))
  :hints (("Goal" :in-theory (e/d (GACC::WR) ()))))

(defthm wfr-of-memory-clr
  (implies (and (wfr tr)
                (wfkey a))
           (wfr (gacc::memory-clr a tr)))
  :hints (("Goal" :in-theory (e/d (gacc::memory-clr) (wr-of-0-is-clr)))))



(defthm not-check-tr-keys-1
  (implies (equal (loghead 8 (car (g (set::head rkeys) tr))) 0)
           (equal (check-tr-keys rkeys tr)
                  (set::empty rkeys))))

(defthm check-tr-keys-of-memory-clr-irrel
  (implies (and (not (set::in key keys))
                (wfr tr))
           (equal (check-tr-keys keys (gacc::memory-clr key tr))
                  (check-tr-keys keys tr)))
  :hints (("Goal" :in-theory (e/d (GACC::MEMORY-CLR GACC::WR) (WR-OF-0-IS-CLR))
           :do-not '(generalize eliminate-destructors))))

#|
(defthm nil-not-in-key-set-when-wfkeyed
  (implies (WFKEYED R)
           (not (set::in nil (key-set r))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable key-set wfr wfkeyed wfkey))))

(defthm nil-not-in-key-set-when-wfr
 (implies (wfr r)
          (not (set::in nil (key-set r))))
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
          :in-theory (enable key-set wfr wfkeyed wfkey))))
|#

(defthm wfkey-when-in-rkeys
  (implies (and (wfr tr)
                (set::in key (set::rkeys tr))
                )
           (wfkey key))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable wfkey set::rkeys))))
;;            :in-theory (enable wfr rkeys wfkey wfkeyed))))

(defthm wkeys-of-head-of-rkeys
  (implies (and (wfr tr)
                tr ;
                )
           (wfkey (set::head (set::rkeys tr))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable ;wfr rkeys wfkey wfkeyed
                       ))))

(defthm setp-rkeys
  (set::setp (set::rkeys tr))
  :hints (("Goal" :in-theory (enable set::rkeys))))

(defthm mypuhs-aux-of-mylift-aux
  (implies (and (wf-tr tr)
                (equal rkeys (set::rkeys tr)))
           (equal (mypush-aux rkeys
                              (mylift-aux rkeys tr))
                  tr))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d ( ;wfr
                            CHECK-TR-KEYS
                            mypush-aux mylift-aux)
                           ( ;gacc::wr==r!
                            ))
           :induct (ind rkeys tr)
           )))

;for dave
(defthm mypush-of-mylift
  (implies (wf-tr tr)
           (equal (mypush (mylift tr))
                  tr)))


(defun typed-fix-aux (keys r)
  (declare (xargs :verify-guards nil))
  (if (set::empty keys)
      nil ;the empty record
    (s (set::head keys)
       (val-fix (g (set::head keys) r))
       (typed-fix-aux (set::tail keys) r))))

;takes a true record and fixes it by dropping all pairs whose value has a
;loghead8 of 0 and chopping the value on all pairs whose value is not a usb8.
(defun typed-fix (r)
  (declare (xargs :verify-guards nil))
  (typed-fix-aux (set::rkeys r) r))


(DEFTHM RKEYS-OF-WR-alt
  (IMPLIES (wfr tr)
           (EQUAL (SET::RKEYS (GACC::WR A V TR))
                  (IF (GACC::WF-USBP8 (G A TR))
                      (IF (GACC::USBP8-ZP V)
                          (IF (CDR (G A TR))
                              (SET::INSERT A (SET::RKEYS TR))
                              (SET::DELETE A (SET::RKEYS TR)))
                          (SET::INSERT A (SET::RKEYS TR)))
                      (IF (GACC::USBP8-ZP V)
                          (SET::RKEYS TR)
                          (SET::INSERT A (SET::RKEYS TR))))))
)

;; (SET::RKEYS (MYPUSH-AUX (SET::RKEYS R) R))

;; (DEFTHM WFR-OF-WR-strong
;;   (IMPLIES (WFR TR)
;;            (equal (WFR (GACC::WR A V TR))
;;                   (WFKEY A)))
;;   :HINTS (("Goal" :IN-THEORY (E/D (wfkey) NIL))))



(defun ind3 (keys r)
  (declare (xargs :verify-guards nil))
  (if (or (not (set::setp keys))
          (set::empty keys))
      (list keys r)
    (ind3 (set::tail keys)
         (CLR (SET::HEAD (SET::RKEYS R)) r);
         ;(gacc::wr (set::head keys) (gacc::rd (set::head keys) tr) tr)
         )))





;; ;bbzo - in the record library but local there!
;; ;(skip-proofs
;; ;bzo dup from records book
;; (defthm wfkeyed-s-aux
;;          (implies (and (not (ifrp r))
;;                        (rcdp r)
;;                        (wfkeyed r)
;;                        (wfkey a))
;;                   (wfkeyed (s-aux a v r)))
;;          :hints (("goal" :induct (s-aux a v r))))
;; ;)




(defthmd g-when-not-g-of-cdr
  (implies (and (not (g key (cdr r)))
                (wfr r))
           (equal (g key r)
                  (if (equal key (caar r))
                      (cdar r)
                    nil)))
  :hints (("Goal" :in-theory (enable g)
           :do-not '(generalize eliminate-destructors))))


(defthm g-when-not-in-rkeys
  (implies (and (not (set::in key (set::rkeys r)))
                (wfr r))
           (equal (g key r)
                  nil))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable rkeys g-when-not-g-of-cdr ))))

(defthm nil-not-in-rkeys
  (implies (and (wfkeyed r) ;drop?
                (wfr r))
           (not (set::in nil (set::rkeys r))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable rkeys wfkeyed))))

(defthm g-of-nil
  (implies (and ;(wfkeyed r)
                (wfr r))
           (not (g nil r)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable ;wfkeyed wfkey
                       ))))

;bzo move some of these?
(defthm s-nil-nil
  (implies (wfr r)
           (equal (S NIL NIL R)
                  r)))

(defthm wfkeyed-of-clr
  (implies (and (wfr r)
                ;(wfkeyed r)
                )
           (wfkeyed (clr key r)))
  :otf-flg t
  :hints (("Goal" :cases (key)
           :in-theory (e/d (clr WFKEY) (S==R)))))

;; (defthm wfr-of-mypush-aux-helper
;;   (implies (and (wfr r)
;;                 (wfkeyed r)
;;                 (equal keys (set::rkeys r))
;;                 )
;;            (wfr (mypush-aux keys r)))
;;   :hints (("Goal" :induct (ind3 keys r)
;;            :do-not '(generalize eliminate-destructors))))

;; (defthm wfr-of-mypush-aux-helper
;;   (implies (and (wfr r)
;;                 (wfkeyed r)
;;                 (set::setp keys)
;;                 (set::subset keys (set::rkeys r))
;;                 )
;;            (wfr (mypush-aux keys r)))
;;   :hints (("Goal" :induct (ind3 keys r)
;;            :in-theory (disable SET::SUBSET ;bzo was getting specious simp..
;;                                )
;;            :do-not '(generalize eliminate-destructors))))

(defthm wfr-of-mypush-aux-helper
  (implies (and (wfr r)
                (set::all<non-nil> keys)
                )
           (wfr (mypush-aux keys r)))
  :hints (("Goal" ;:induct (ind3 keys r)
           :in-theory (e/d (wfkey) (set::subset ;bzo was getting specious simp..
                               ))
           :do-not '(generalize eliminate-destructors))))


;; subset is enough?
;; (thm
;;  (equal (SET::RKEYS (MYPUSH-AUX keys R))
;;         ..

(defthm g-of-mypush-aux-when-not-in-keys
  (implies (not (set::in key keys))
           (equal (g key (mypush-aux keys r))
                  nil))
  :hints (("Goal" :in-theory (enable GACC::WR)
           :do-not '(generalize eliminate-destructors))))

(defthm clr-of-typed-fix-aux-irrel
  (implies (not (set::in key keys))
           (equal (CLR key (TYPED-FIX-AUX keys R))
                  (TYPED-FIX-AUX keys (CLR key r))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm not-in-of-rkeys-of-mypush-aux
  (implies (and (NOT (SET::IN key keys))
                (set::all<non-nil> keys) ;drop?
                (wfr r))
           (NOT (SET::IN key (SET::RKEYS (MYPUSH-AUX keys R)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm set::rkeys-clr
  (equal (set::rkeys (clr a r))
         (set::delete a (set::rkeys r)))
  :hints (("Goal" :in-theory (enable set::rkeys))))

(defthm MYLIFt-of-mypush-helper
  (IMPLIES (and (WFR R)
                (equal keys (SET::RKEYS R)))
           (EQUAL (MYLIFT-AUX (SET::RKEYS (MYPUSH-AUX keys R))
                              (MYPUSH-AUX keys R))
                  (TYPED-FIX-AUX keys R)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (ind3 keys r)
           )))

(defthm mylift-of-mypush
  (implies (wfr r)
           (equal (mylift (mypush r))
                  (typed-fix r))))

;Bbzo give the predicate for which lift of push really is the identity and prove that typed-fix is a no-op if that predicate is true

(defun all-vals-okay-aux (keys r)
  (declare (xargs :verify-guards nil))
  (if (set::empty keys)
      t
    (and (unsigned-byte-p 8(g (set::head keys) r))
         (not (equal 0 (g (set::head keys) r)))
         (all-vals-okay-aux (set::tail keys) r))))

(defthm all-vals-okay-aux-of-clr-irrel
  (implies (not (set::in key keys))
           (equal (all-vals-okay-aux keys (clr key r))
                  (all-vals-okay-aux keys r)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;          :induct (ind3 keys r)
           )))


(defthm typed-fix-does-nothing-helper
  (implies (and (all-vals-okay-aux keys r)
                (equal keys (set::rkeys r))
                (wfr r)
                )
           (equal (typed-fix r)
                  r))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (ind3 keys r))))

;;bzo Dave, what do we want to call this?
(defun well-typed-record (r)
  (declare (xargs :verify-guards nil))
  (and (wfr r)
       (all-vals-okay-aux (set::rkeys r) r)))

;for Dave
(defthm typed-fix-does-nothing
  (implies (well-typed-record r)
           (equal (typed-fix r)
                  r))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


;; (defun mypush (r)
;;   (if (endp r)
;;       nil
;;     (let* ((entry (car r))
;;            (key (car entry))
;;            (val (cdr entry)) ;not cadr
;;            )
;;       (gacc::wr key val (mypush (cdr r))))))

;; (defun wf-tr (tr)
;;   (if (endp tr)
;;       (null tr)
;;     (let* ((entry (car tr))
;; ;           (key (car entry))
;;            (val (cadr entry)) ;not cdr
;;            )
;;       (and (equal 2 (len entry))
;;            (unsigned-byte-p 8 val)
;;            (not (equal 0 val))
;;            (wf-tr (cdr tr))))))

(local (in-theory (disable ACL2::LOGHEAD-IDENTITY-2))) ;for efficiency... ;bzo, disable elsewhere?

;;
;; OFFSET-RANGE-WRAP
;;

;reorder params?
;bzo is the 2nd call to loghead necessary?
;rename size param?
(defund offset-range-wrap (width base size)
  (declare (type integer base)
           (type (integer 0 *) size)
           (type (integer 0 *) width))
  (if (zp size)
      nil
    (cons (loghead width base)
          (offset-range-wrap width (loghead width (+ 1 (ifix base))) (+ -1 size)))))

;; (in-theory (disable (:executable-counterpart OFFSET-RANGE-WRAP)))

(defthm offset-range-wrap-when-size-is-not-positive
  (implies (<= size 0)
           (equal (offset-range-wrap width base size)
                  nil))
  :hints (("Goal" :in-theory (enable offset-range-wrap))))

(defthm offset-range-wrap-when-size-is-not-an-integerp
  (implies (not (integerp size))
           (equal (offset-range-wrap width base size)
                  nil))
  :hints (("Goal" :in-theory (enable offset-range-wrap))))

(defthm offset-range-wrap-when-width-is-zero
  (equal (offset-range-wrap 0 y size)
         (repeat size 0))
  :hints (("Goal" :in-theory (enable offset-range-wrap))))

(defthm offset-range-wrap-when-width-is-zp
  (implies (zp width)
           (equal (offset-range-wrap width base size)
                  (repeat size 0)))
  :hints (("Goal" :in-theory (enable offset-range-wrap zp))))

(defthm offset-range-wrap-when-offset-is-not-an-integerp
  (implies (not (integerp offset))
           (equal (offset-range-wrap width offset numwords)
                  (offset-range-wrap width 0 numwords)))
  :hints (("Goal" :in-theory (enable offset-range-wrap))))

(defthm offset-range-wrap-when-size-is-1
  (equal (offset-range-wrap width base 1)
         (list (loghead width base)))
  :hints (("Goal" :in-theory (enable offset-range-wrap))))

(defthm car-of-offset-range-wrap
  (equal (car (offset-range-wrap width base size))
         (if (zp size)
             nil
           (loghead width base)))
  :hints (("Goal" :in-theory (enable offset-range-wrap))))

(defthm consp-of-offset-range-wrap
  (equal (consp (offset-range-wrap width base size))
         (not (zp size)))
  :hints (("Goal" :in-theory (enable offset-range-wrap))))

(defthm integer-listp-of-offset-range-wrap
  (integer-listp (offset-range-wrap width base size))
  :hints (("Goal" :in-theory (enable offset-range-wrap))))

(defthm offset-range-wrap-of-loghead
  (equal (offset-range-wrap width (loghead width base) size)
         (offset-range-wrap width base size))
  :hints (("Goal" :in-theory (enable offset-range-wrap))))

(defthm offset-range-wrap-of-sum-hack
  (implies (and (syntaxp (quotep a))
                (not (acl2::unsigned-byte-p width a))
                (integerp a)
                (integerp b)
                )
           (equal (offset-range-wrap width (+ a b) size)
                  (offset-range-wrap width (+ (acl2::loghead width a) b) size)))
  :hints (("Goal" :use ((:instance offset-range-wrap-of-loghead (base (+ (acl2::loghead width a) b)))
                        (:instance offset-range-wrap-of-loghead (base (+ a b)))
                        )
           :in-theory (disable offset-range-wrap-of-loghead))))

(defthm not-memberp-of-offset-range-wrap-when-not-usbwidth
  (implies (not (unsigned-byte-p (nfix width) offset))
           (not (list::memberp offset (offset-range-wrap width base size))))
  :hints (("Goal" :expand (OFFSET-RANGE-WRAP WIDTH 0 SIZE)
           :in-theory (enable offset-range-wrap))))

(defthm memberp-of-offset-range-wrap-of-self
  (equal (bag::memberp offset (offset-range-wrap width offset size))
         (and (unsigned-byte-p (nfix width) offset)
              (integerp size)
              (< 0 size)))
  :hints (("Goal" :expand (offset-range-wrap width offset size)
           :in-theory (enable offset-range-wrap
                              list::memberp-of-cons
                              memberp-when-x-is-an-integer-listp))))

;bzo
;might this be expensive?

(defthmd not-equal-hack
  (implies (and (BAG::DISJOINT bag (OFFSET-RANGE-WRAP width offset1 size))
                (bag::memberp offset2 bag)
                (unsigned-byte-p width offset2) ;handle this better?
                (integerp size)
                (< 0 size)
                (equal width 16);bzo
                )
           (not (equal offset1 offset2)))
  :hints (("Goal" :in-theory (enable BAG::NOT-MEMBERP-FROM-DISJOINTNESS-ONE
                                     BAG::NOT-MEMBERP-FROM-DISJOINTNESS-two))))

;this may be expensive
;if we have a wrapping version of wx, this stuff may be nicer?
(defthmd use-DISJOINT-of-offset-range-wraps-hack
  (implies (and (BAG::DISJOINT (OFFSET-RANGE-WRAP width offset1 size1) (OFFSET-RANGE-WRAP width offset2 size2))
                (list::memberp offset3 (OFFSET-RANGE-WRAP width offset1 size1))
                (list::memberp offset4 (OFFSET-RANGE-WRAP width offset2 size2)))
           (not (equal offset3 offset4))))

(defthmd offset-range-wrap-const-opener ;bzo yuck!
  (implies (and (syntaxp (quotep size))
                (not (zp size))
                )
           (equal (offset-range-wrap width base size)
                  (cons (loghead width base)
                        (offset-range-wrap width (loghead width (+ 1 (ifix base)))
                                           (+ -1 size)))))
  :hints (("Goal" :in-theory (enable offset-range-wrap))))

(defthm offset-range-wrap-of-logext
  (equal (offset-range-wrap width (acl2::logext width base) size)
         (offset-range-wrap width base size))
  :hints (("Goal" :use ((:instance offset-range-wrap-of-loghead (base base))
                        (:instance offset-range-wrap-of-loghead (base (acl2::logext width base))))
           :in-theory (disable offset-range-wrap-of-loghead))))

(defthm offset-chop-first-arg-when-constant
  (implies (and (syntaxp (and (quotep offset) (quotep width)))
                (< 0 width) ;helps prevent loops
                (not (acl2::signed-byte-p width offset))
                (integerp offset)
                (integerp size))
           (equal (offset-range-wrap width offset size)
                  (offset-range-wrap width (acl2::logext width offset) size))))


(defthm use-disjoint-of-offset-range-wraps-hack-better
  (implies (and (bag::disjoint (offset-range-wrap width offset1 size1)
                               bag)
                (list::memberp offset3 (offset-range-wrap width offset1 size1))
                (list::memberp offset4 bag))
           (not (equal offset3 offset4))))

(defthm use-disjoint-of-offset-range-wraps-hack-better-alt
  (implies (and (bag::disjoint bag
                               (offset-range-wrap width offset1 size1))
                (list::memberp offset3 (offset-range-wrap width offset1 size1))
                (list::memberp offset4 bag))
           (not (equal offset3 offset4))))

(defthm use-disjoint-of-offset-range-wraps-hack-better-2
  (implies (and (bag::disjoint (offset-range-wrap width offset1 size1)
                               bag)
                (list::memberp offset4 (offset-range-wrap width offset1 size1))
                (list::memberp offset3 bag))
           (not (equal offset4 offset3))))

(defthm use-disjoint-of-offset-range-wraps-hack-better-alt-2
  (implies (and (bag::disjoint bag
                               (offset-range-wrap width offset1 size1))
                (list::memberp offset4 (offset-range-wrap width offset1 size1))
                (list::memberp offset3 bag))
           (not (equal offset4 offset3))))


(defthm cdr-of-offset-range-wrap
  (equal (cdr (offset-range-wrap width base size))
         (if (zp size)
             nil
           (offset-range-wrap width (+ 1 (ifix base)) (+ -1 size))))
  :hints (("Goal" :expand (OFFSET-RANGE-WRAP width BASE SIZE)
           :in-theory (enable offset-range-wrap))))


(defun offset-range-wrap-induct-with-x (width base size x)
  (if (zp size)
      x
      (cons (loghead width base)
            (offset-range-wrap-induct-with-x width (loghead width (+ 1 (ifix base))) (+ -1 size) x))))


;; (defthm consp-of-offset-range-wrap
;;   (equal (consp (offset-range-wrap 16 k size))
;;          (and (integerp size)
;;               (< 0 size)))
;;   :hints (("Goal" :in-theory (enable offset-range-wrap))))

(defthm memberp-of-offset-range-sum-self-hack
  (implies (and (integerp k)
                (integerp x)
                (integerp width)
                (<= 0 width)
                )
           (equal (list::memberp x (offset-range-wrap width (+ k x) size))
                  (and (unsigned-byte-p width x)
                       (< (loghead width (- k)) size)
     ;                       (<= 0 (loghead width (- k)))
                       (integerp size))))
  :hints (("Goal" :in-theory (enable memberp-when-x-is-an-integer-listp
                                     memberp-of-offset-range))))



(defthm memberp-of-offset-range-sum-self-hack-other
  (implies (and (integerp k)
                (integerp x)
                (integerp width)
                (<= 0 width)
                )
           (equal (list::memberp (loghead width (+ k x)) (offset-range-wrap width x size))
                  (and (< (loghead width k) size)
     ;                       (<= 0 (loghead width k))
                       (integerp size))))
  :hints (("Goal" :in-theory (enable memberp-when-x-is-an-integer-listp
                                     memberp-of-offset-range))))


(defthm memberp-loghead-offset-range-wrap-simplify-constants
  (implies (and (syntaxp (and (quotep k1) ;i think i want these syntaxp hyps, right?
                              (quotep k2)))
                (integerp x)
                (integerp y)
                (integerp k1)
                (integerp k2)
                (integerp size)
                (integerp width)
                (<= 0 width)
                )
           (equal (list::memberp (loghead width (+ k1 x)) (offset-range-wrap width (+ k2 y) size))
                  (list::memberp (loghead width (+ (- k1 k2) x)) (offset-range-wrap width y size))))
  :hints (("Goal" :in-theory (enable memberp-of-offset-range))))


(in-theory (enable MEMBERP-OF-OFFSET-RANGE))

(local (defthmd helper1
         (IMPLIES (AND (INTEGERP SIZE1)
                       (< 0 SIZE1)
;               (INTEGERP SIZE2)
;                (<= 0 SIZE2)
                       (INTEGERP BASE1)
                       (INTEGERP BASE2)
                       (integerp width)
                       (<= 0 width)

                       (BAG::SUBBAGP (OFFSET-RANGE-WRAP width BASE1 SIZE1)
                                     (OFFSET-RANGE-WRAP width BASE2 SIZE2)))
                  (< (LOGHEAD width (+ BASE1 (- BASE2)))
                     SIZE2))
         :hints (("Goal" :do-not '(generalize eliminate-destructors)
                  :induct (OFFSET-RANGE-WRAP width BASE1 SIZE1)
                  :in-theory (enable OFFSET-RANGE-WRAP)))))


;; This is basically a version of sblkp that handles wrapping.
;rename wrapped-range?
;generalize the width?
;bzo could weaken the guard...
(defund offset-rangep (width range)
  (declare (xargs :guard (integer-listp range)))
  (if (endp range)
      t
    (if (endp (cdr range))
        (unsigned-byte-p width (car range)) ;bzo use (integerp (car range)) ?
      (and (equal (car range) (loghead (nfix width) (+ -1 (cadr range))))
           (offset-rangep width (cdr range))))))


;bzo - disable for general use
(defthm integerp-of-car-of-offset-rangep
  (implies (offset-rangep width range)
           (equal (integerp (car range))
                  (< 0 (len range))))
  :hints (("Goal" :in-theory (enable offset-rangep))))


(local (defthmd helper2
         (implies (and (integerp size1)
                       (< 0 size1)
                       (integerp size2)
                       (<= 0 size2)
                       ;; (<= size2 65536)
                       (unsigned-byte-p width size2)

                       (integerp base1)
                       (integerp base2)
                       (bag::subbagp (offset-range-wrap width base1 size1)
                                     (offset-range-wrap width base2 size2))

                       (integerp width)
                       (<= 0 width)
                       )
                  (<= (+ size1 (loghead width (+ base1 (- base2)))) size2))
         :hints (("Goal" :do-not '(generalize eliminate-destructors)
;:induct (OFFSET-RANGE-WRAP '16 BASE1 SIZE1)
                  :in-theory (enable
                              ACL2::LOGHEAD-SUM-SPLIT-INTO-2-CASES
                              ACL2::LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT
                              OFFSET-RANGE-WRAP)))))


;bzo should offset-rangep chop its size parameter down to 16 bits?

(defthm offset-rangep-of-cdr
  (implies (offset-rangep width y)
           (offset-rangep width (cdr y)))
  :hints (("Goal" :in-theory (enable offset-rangep))))

;hung on cadr
;disable?
(defthm cadr-when-offset-rangep
  (implies (offset-rangep width x)
           (equal (cadr x)
                  (if (not (and (consp x) (consp (cdr x))))
                      nil
                    (loghead width (+ 1 (car x))))))
  :hints (("Goal" :in-theory (enable OFFSET-RANGEP))))

;move to bags?
(defthm subbagp-cdr-when-memberp-car
  (implies (and (list::memberp (car x) y)
                (not (list::memberp (car x) (cdr x)))
                )
           (equal (bag::subbagp (cdr x) y)
                  (bag::subbagp x y)
                  )))


(local (in-theory (disable len)))
(local (in-theory (enable list::len-of-cdr-better)))

(defthm offset-rangep-when-x-is-not-a-consp
  (implies (not (consp x))
           (offset-rangep width x))
  :hints (("Goal" :in-theory (enable offset-rangep))))

(defthm offset-rangep-when-car-isnt-a-usb
  (implies (not (unsigned-byte-p width (car x)))
           (equal (offset-rangep width x)
                  (not (consp x))))
  :hints (("Goal" :in-theory (enable offset-rangep))))


(local (defthm helper-lemm
         (implies (and (consp x)
                       (offset-rangep width x)
                       )
                  (acl2-numberp (car x)))
         :hints (("Goal" :in-theory (enable offset-rangep)))))

(defthm offset-range-hack
  (implies (offset-rangep width x)
           (equal (unsigned-byte-p width (car x))
                  (consp x)))
  :hints (("Goal" :in-theory (enable offset-rangep))))

(defthm offset-range-hack2
  (implies (and (offset-rangep width x)
                (consp x))
           (unsigned-byte-p width (car x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable offset-rangep))))



(defthm offset-rangep-of-offset-range-wrap
  (implies (and (integerp width)
                (<= 0 width))
           (offset-rangep width (offset-range-wrap width base size)))
  :hints (("Goal" :in-theory (enable offset-rangep offset-range-wrap))))

(defthm len-of-offset-range-wrap
  (implies (and (integerp width)
                (<= 0 width))
           (equal (len (offset-range-wrap width base size))
                  (nfix size)))
  :hints (("Goal" :induct t
           :expand (OFFSET-RANGE-WRAP WIDTH 0 SIZE)
           :in-theory (enable offset-range-wrap))))

(local (defthmd helper3
         (IMPLIES (AND (<= (+ SIZE1 (LOGHEAD width (+ BASE1 (- BASE2))))
                           (loghead width SIZE2))
                       (< (LOGHEAD width (+ BASE1 (- BASE2))) (loghead width SIZE2))
                       (<= 0 SIZE2)
                       (INTEGERP BASE1)
                       (INTEGERP BASE2)
                       (integerp width)
                       (<= 0 width) )
                  (BAG::SUBBAGP (OFFSET-RANGE-WRAP width BASE1 SIZE1)
                                (OFFSET-RANGE-WRAP width BASE2 SIZE2)))
         :hints (("Goal" :in-theory (e/d (zp) ( hard-way))
                  :use (:instance hard-way (x  (OFFSET-RANGE-WRAP width BASE1 SIZE1)) (y (OFFSET-RANGE-WRAP width BASE2 SIZE2)))))))


(defthm large-OFFSET-RANGE-WRAP-contains-all
  (IMPLIES (AND (<= (expt 2 width) SIZE) ;note this
                (INTEGERP SIZE)
                (integerp width)
                (<= 0 width)
                )
           (equal (MEMBERP val (OFFSET-RANGE-WRAP WIDTH BASE SIZE))
                  (unsigned-byte-p width val)))
  :hints (("Goal" :in-theory (enable MEMBERP-OF-OFFSET-RANGE))))

(defthm count-when-OFFSET-RANGE-WRAP-just-misses
  (IMPLIES (AND (<= SIZE (expt 2 width))
                (INTEGERP BASE)
                (INTEGERP WIDTH)
                (<= 0 WIDTH))
           (equal (BAG::COUNT (LOGHEAD WIDTH BASE)
                              (OFFSET-RANGE-WRAP WIDTH (+ 1 BASE)
                                                 (+ -1 SIZE)))
                  0)))

(defthm subbagp-when-contains-all
  (IMPLIES (AND (NOT (UNSIGNED-BYTE-P WIDTH SIZE2))
                (<= SIZE1 (expt 2 width)) ;(UNSIGNED-BYTE-P WIDTH SIZE1)
;                (INTEGERP SIZE1)
;                (<= 0 SIZE1)
                (integerp size2)
                (<= 0 size2)
                (INTEGERP BASE1)
                (INTEGERP BASE2)
                (integerp width)
                (<= 0 width)
                )
           (SUBBAGP (OFFSET-RANGE-WRAP WIDTH BASE1 SIZE1)
                    (OFFSET-RANGE-WRAP WIDTH BASE2 SIZE2)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct t
           :do-not-induct t
           :in-theory (enable OFFSET-RANGE-WRAP))))


(defthm disjoint-of-two-offset-ranges
  (implies (and (BAG::DISJOINT (OFFSET-RANGE-WRAP width base3 size3)
                               (OFFSET-RANGE-WRAP width base4 size4))
                (< (loghead width (- base1 base3)) size3)
                (<= (+ size1 (loghead width (+ base1 (- base3))))
                    size3)
                (< (loghead width (- base2 base4)) size4)
                (<= (+ size2 (loghead width (+ base2 (- base4))))
                    size4)

;             (integerp size3)
;            (<= 0 size3)
                (case-split (integerp base1))
                (case-split (integerp base3))
                (unsigned-byte-p width size3)

;             (integerp size4)
;            (<= 0 size4)
                (case-split (integerp base2))
                (case-split (integerp base4))
                (unsigned-byte-p width size4)
                (integerp width)
                (<= 0 width)

                )
           (BAG::DISJOINT (OFFSET-RANGE-WRAP width base1 size1)
                          (OFFSET-RANGE-WRAP width base2 size2))
           )
  :hints (("Goal" :in-theory (enable BAG::SUBBAGP-DISJOINT))))


(defthm offset-range-wrap-of-sum-of-loghead
  (implies (integerp y)
           (equal (offset-range-wrap width (+ x (loghead width y)) size)
                  (offset-range-wrap width (+ x y) size)))
  :hints (("Goal" :in-theory (disable offset-range-wrap-of-loghead)
           :use ((:instance offset-range-wrap-of-loghead (base (+ x y)))
                 (:instance offset-range-wrap-of-loghead (base (+ x (loghead width y))))))))

(defthm offset-range-wrap-subst-in-sum-offset
  (implies (and (equal (loghead width off2) off3)
                (syntaxp (acl2::smaller-term off3 off2))
                (integerp off2)
                (integerp off1)
                )
           (equal (offset-range-wrap width (+ off1 off2) size)
                  (offset-range-wrap width (+ off1 off3) size))))

(defthm offset-range-wrap-subst-in-sum-offset-2
  (implies (and (equal (loghead width off2) (loghead width off3))
                (syntaxp (acl2::smaller-term off3 off2))
                (integerp off2)
                (integerp off1)
                )
           (equal (offset-range-wrap width (+ off1 off2) size)
                  (if (integerp off3)

                      (offset-range-wrap width (+ off1 off3) size)
                    (offset-range-wrap width off1 size)
                    )))
  :hints (("Goal" :use ((:instance offset-range-wrap-of-sum-of-loghead (x off1) (y off2))
                        (:instance offset-range-wrap-of-sum-of-loghead (x off1) (y off3)))
           :in-theory (disable offset-range-wrap-of-sum-of-loghead
                               offset-range-wrap-subst-in-sum-offset
                               ))))

(defthm offset-range-wrap-subst
  (implies (and (equal (loghead width off1) (loghead width off2))
                (syntaxp (acl2::smaller-term off2 off1))
                )
           (equal (offset-range-wrap width off1 size)
                  (offset-range-wrap width off2 size)))
  :hints (("Goal" :use ((:instance offset-range-wrap-of-loghead (base off2))
                        (:instance offset-range-wrap-of-loghead (base off1))
                        )
           :in-theory (disable offset-range-wrap-of-loghead
                               ))))

(local (defun induct4 (x y)
         (if (or (endp x) (endp y))
             (list x y)
           (induct4 (cdr x) (cdr y)))))


(defthmd equiv-of-two-offset-ranges
  (implies (and (offset-rangep width x)
                (offset-rangep width y))
           (equal (list::equiv x y)
                  (and (equal (len x) (len y))
                       (or (equal 0 (len x))
                           (equal (car x)
                                  (car y))))))
  :hints (("Goal" :induct (induct4 x y)
           :in-theory (enable OFFSET-RANGEP))))

;BZO change offset-rangep to enfore true-listp as well?
(defthm equiv-of-two-offset-ranges-true-list-case
  (implies (and (offset-rangep width x)
                (offset-rangep width y)
                (true-listp x)
                (true-listp y)
                )
           (equal (equal x y)
                  (and (equal (len x) (len y))
                       (or (equal 0 (len x))
                           (equal (car x)
                                  (car y))))))
  :hints (("Goal" :use (:instance  equiv-of-two-offset-ranges))))

(defthm equal-of-two-offset-range-wraps
  (implies (and (integerp width)
                (<= 0 width))
           (equal (equal (offset-range-wrap width base1 size1)
                         (offset-range-wrap width base2 size2))
                  (and (equal (nfix size1) (nfix size2))
                       (or (equal 0 (nfix size1))
                           (equal (loghead width base1)
                                  (loghead width base2))))))
  :hints (("Goal"
           :use (:instance EQUIV-OF-TWO-OFFSET-RANGES-TRUE-LIST-CASE
                           (x  (offset-range-wrap width base1 size1))
                           (y  (offset-range-wrap width base2 size2))))))

(defun get-enabled-structure (pspv)
  (strip-cdrs
   (cdr
    (access enabled-structure
            (access rewrite-constant
                    (access prove-spec-var pspv :rewrite-constant)
                    :current-enabled-structure)
            :theory-array))))

(defun turn-on-expensive-rules (stable-under-simplificationp pspv)
  (if stable-under-simplificationp
      `(:in-theory (union-theories ',(get-enabled-structure pspv)
                                   '((:rewrite ACL2::LOGHEAD-SUM-SPLIT-INTO-2-CASES)
                                     (:rewrite acl2::loghead-of-minus)
                                     )))
    nil))



(defthm disjoint-of-offset-range-wraps-shift
  (implies (and (integerp i)
                (integerp j)
                (integerp k)
                (integerp width)
                (< 0 width))
           (equal (bag::disjoint (offset-range-wrap width (+ j i) size)
                                 (offset-range-wrap width (+ k i) size))
                  (or (bag::disjoint (offset-range-wrap width j size)
                                     (offset-range-wrap width k size))
                      (not (integerp size))
                      (<= size 0))))
  :hints (("Goal" :in-theory (enable disjoint-of-two-offset-range-wraps))))

;bzo gen
(defthm offset-range-wrap-of-logext-special
  (equal (gacc::offset-range-wrap 31 (logext 32 x) 2)
         (gacc::offset-range-wrap 31 x 2)))

(defthm unique-of-offset-range-wrap
  (implies (and (<= numwords (expt 2 width))
                (natp width))
           (bag::unique (offset-range-wrap width offset numwords)))
  :hints (("Goal" :expand (OFFSET-RANGE-WRAP width 0 NUMWORDS)
           :in-theory (enable offset-range-wrap
                              memberp-of-offset-range))))


(defun sub1-sub1-induct (m n)
  (if (zp n)
      (list m n)
    (sub1-sub1-induct (+ -1 m) (+ -1 n))))

;bzo gen and move
(defthm nth-of-repeat
  (implies (and (natp n)
                (natp num)
                (< n num))
           (equal (nth n (repeat num item))
                  item))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (sub1-sub1-induct num n)
           :in-theory (enable REPEAT))))


(defthm memberp-of-offset-range-wrap-same
  (implies (natp width)
           (equal (list::memberp (loghead width offset) (offset-range-wrap width offset numwords))
                  (not (zp numwords)))))

(defthm not-memberp-of-one-smaller-offset-range
  (implies (and (not (list::memberp x (offset-range-wrap width offset2 numwords)))
                (integerp offset2)
                )
           (not (list::memberp x (offset-range-wrap width (+ 1 offset2) (+ -1 numwords)))))
  :hints (("Goal" :expand (offset-range-wrap width offset2 numwords)
           :in-theory (disable ACL2::LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT ;bzo
                               ))))


(defthm offset-range-wrap-sum-integer-and-non-integer
  (implies (and (integerp n)
                (not (integerp c)))
           (equal (offset-range-wrap width (+ c n) size)
                  (if (acl2-numberp c)
                      (offset-range-wrap width 0 size)
                    (offset-range-wrap width n size)))))

(defthm offset-range-wrap-of-sum-loghead
  (implies (and (integerp base)
                (integerp n)
                (integerp m)
                (<= 0 m)
                (<= m n))
           (equal (gacc::offset-range-wrap m (+ 1 (loghead n base)) size)
                  (gacc::offset-range-wrap m (+ 1 base) size))))

(defthm offset-range-wrap-of-sum-of-loghead-lemma
  (implies (and (integerp a)
                (natp width))
           (equal (offset-range-wrap width (+ 1 (loghead width a) b) size)
                  (offset-range-wrap width (+ 1 a b) size))))

(defthm offset-range-wrap-of-sum-of-loghead-lemma-two
  (implies (and (integerp a)
                (natp width))
           (equal (offset-range-wrap width (+ 1 b (loghead width a)) size)
                  (offset-range-wrap width (+ 1 b a) size))))

;slow proof?
(defthm find-index-of-offset-range-wrap
  (implies (and (< (acl2::loghead 16 (- ad offset)) numwords)
                (natp numwords)
                (integerp ad)
                (integerp offset)
                (acl2::unsigned-byte-p 16 ad)
                )
           (equal (list::find-index ad (gacc::offset-range-wrap 16 offset numwords))
                  (acl2::loghead 16 (- ad offset))))
  :hints (("Goal" :induct t
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::offset-range-wrap
                              ACL2::LOGHEAD-SUM-SPLIT-INTO-2-CASES
                              (:definition list::find-index)))))

(defthmd OFFSET-RANGE-WRAP-opener
  (implies (syntaxp (quotep GACC::SIZE))
           (equal (GACC::OFFSET-RANGE-WRAP GACC::WIDTH GACC::BASE GACC::SIZE)
                  (AND (NOT (ZP GACC::SIZE))
                       (CONS (LOGHEAD GACC::WIDTH GACC::BASE)
                             (GACC::OFFSET-RANGE-WRAP
                              GACC::WIDTH
                              (LOGHEAD GACC::WIDTH (+ 1 (IFIX GACC::BASE)))
                              (+ -1 GACC::SIZE))))))
  :hints (("Goal" :in-theory (enable offset-range-wrap))))
