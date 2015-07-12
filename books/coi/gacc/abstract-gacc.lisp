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

(in-package "ACL2")
; cert_param: (non-acl2r)
(include-book "../records/defrecord")

;; This file represents the beginnings of the future of gacc.
;;
;; Using records as its foundation, this file provides a gacc-like
;; representation for abstract imperative data structures that enables
;; us to encode d/u information about arbitrary functions over those
;; data structures.
;;
;; Arbitrary imparative data structures with arbitrary levels of
;; nesting can be described using this technique.
;;
;; We believe that this technique may be a good replacment for the
;; implementation of "defstructure"s
;;
;; Note, too, that "typed" records can be implemented using these
;; techniques along with "defthing".

; (include-book "/accts/dagreve/CVS/linux/xxx/gacc/defrecord")

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

(in-theory
 (disable
  z* (z*)
  ))

#|

;; A spec is a recursive data structure with the following "grammar"

spec: (
       (off1 spec1)
       (off2)
       (off3 spec3)
       )

|#

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

;;
;;
;; How about typed records?
;;
;;

(defthing integer+
  :rd g-int
  :wr s-int
  :default 0
  :fix ifix
  :typep integerp
  )

;; These rules should be added to defthing ..

(defthm g-s-int-equality
  (implies
   (equal (g-int x) (g-int y))
   (iff (equal (s-int 0 x) (s-int 0 y))
        (equal x y)))
  :hints (("goal" :in-theory (enable g-int s-int))))

(defun fix-whole-list (list)
  (declare (type t list))
  (if (true-listp list) list nil))

(defthing true-listp+
  :rd g-list
  :wr s-list
  :default nil
  :fix fix-whole-list
  :typep true-listp
  )

(defthm g-s-list-equality
  (implies
   (equal (g-list x) (g-list y))
   (iff (equal (s-list 0 x) (s-list 0 y))
        (equal x y)))
  :hints (("goal" :in-theory (enable g-list s-list))))


;; These macros are just window dressing ..

(defmacro k1-get (x)
  `(g-int ,x))

(defmacro k1-set (&rest args)
  `(s-int ,@args))

(defmacro k1-default ()
  `0)

(defmacro k1-fix (v)
  `(ifix ,v))

(defmacro k2-get (x)
  `(g-list ,x))

(defmacro k2-set (&rest args)
  `(s-list ,@args))

(defmacro k2-default ()
  `nil)

(defmacro k2-fix (v)
  `(fix-whole-list ,v))


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

;; Below is the unified theorem of gacc.  It is a generalized
;; formulation of the g/s theorem:

(equal (g* spec1 (s* spec2 ram))
       (s* spec3 (g* spec4 ram)))


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

(equal (g a (m* spec1 r1 spec2 r2))
       (if (member a (flat-keys spec2))
           (g* (remap a spec2 spec1) r1)
         (g a r2)))

(equal (m* spec1 (s a v r1) spec2 r2)
       (if (member a (flat-keys spec1))
           (s* (remap a spec1 spec2) r2)
         (m* spec1 r1 spec2 r2)))

(equal (m* spec1 (m* speca ra specb rb) spec2 r2)
       (m* speca ra specb rb)

(re-key (flat speca) (flat specb))

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


(equal (m* lista (m* listb stb listc rc) listd rd)
       (let ((list1 (lista - listc) % listb)
             (list2 (lista - listc) % listd)
             (list3 (lista ^ listc) % listb)
             (list4 (lista ^ listc) % listd))
         (m* list1 rc list2 (m* list3 rb list4 rd))))

;; Or, perhaps it would be easer to just generalize the copy function to take
;; a list of address pairs (from -> to).  Lets call this new function c*

(defun c* (pair r1 r2)
  (if (consp pair)
      (let ((v1 (g-path (car (car pair)) r1)))
        (let ((r2 (s-path (cdr (car pair)) v1 r2)))
          (c* (cdr pair) r1 r2)))
    r2))

;; (def list) and (use list) might be used extract these lists of
;; keys.  Intersect and Difference compare two lists and create a u/d
;; list based on the results.
;;
;; We will often want identity mappings (u==d).  In such case, we might
;; want the function (ud list), such that (use (ud list)) = list and (def
;; (ud list)) = list.
;;
;; (ud list) is just a simplification of the general case (dot a b)
;; where a==b==list.

(equal (c* a (c* b r1 r2) r3)
       (c* (intersect (use a) (def b) (use b) (def a)) r1
           (c* (difference (use a) (def b) (use a) (def a)) r2 r3)))

(implies
 (perm b c)
 (equal (c* (dot a b) r1 r2)
        (c* (pair c) (c* (dot a b) r1 nil) r2)))

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

(m* mud mu (mapfn (m* umd u r1 md nil)) d r2)

(defun map< (a m)
  (remap a (def m) (use m)))

(defun map> (a m)
  (remap a (use m) (def m)))

(equal (g a (m* m u r1 d r2))
       (if (member a d)
           (g (map< a m) r1)
         (g a r2)))

(equal (m* m u (s a v r1) d r2)
       (if (member a u)
           (s (map> a m) (m* m u r1 d r2))
         (m* m u r1 d r2)))

(equal (m* m1 u1 (m* m2 u2 ru2 d2 rd2) d1 rd1)
       (m* m' u' ru2 (m* m u rd2 d rd1)))

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

(equal (push spec list r1)
       (c* (flat-keys list) (push spec list (c* (flat-keys list) r nil)) r))

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

(equal (step st)
       (c* def (step (c* use st nil)) st))

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

;; Boom .. done.



|#
