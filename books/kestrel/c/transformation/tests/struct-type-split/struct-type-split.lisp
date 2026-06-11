; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

(include-book "../../../syntax/input-files")
(include-book "../../../syntax/output-files")

(include-book "../../struct-type-split")
(include-book "../utilities")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Successes

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files '("test1.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "point"
                     :right-members ("z")
                     :new-tag "point_right")

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/test1.c"
    :content "struct point {
  int x;
  int y;
};

struct point_right {
  int z;
};

static struct point p;

static struct point_right p_0;

int main(void) {
  p.x = 4;
  p_0.z = 2;
  return p.x + p_0.z;
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Without a :new-tag, the right struct tag is freshened
;; from the original tag.

(acl2::must-succeed*
  (c$::input-files :files '("test2.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "pair"
                     :right-members ("snd"))

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/test2.c"
    :content "struct pair {
  int fst;
};

struct pair_0 {
  int snd;
};

int main(void) {
  struct pair x = {.fst = 1};
  struct pair_0 x_0 = {.snd = 2};
  struct pair *ptr = &x;
  struct pair_0 *ptr_0 = &x_0;
  return x.fst + ptr_0->snd;
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Failures

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files '("test1.c")
                   :const *old*)

  ;; The struct tag does not exist.
  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "nonexistent"
                       :right-members ("z")))

  ;; The struct tag is not a string.
  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag point
                       :right-members ("z")))

  ;; No right members are specified.
  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "point"
                       :right-members ()))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An initializer list without syntactic designations is routed
;; using the implicit designators recorded by the validator.

(acl2::must-succeed*
  (c$::input-files :files '("positional-init.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "pair"
                     :right-members ("snd"))

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/positional-init.c"
    :content "struct pair {
  int fst;
};

struct pair_0 {
  int snd;
};

int main(void) {
  struct pair x = {1};
  struct pair_0 x_0 = {2};
  return x_0.snd;
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The split struct type may not appear in a sizeof expression.

(acl2::must-succeed*
  (c$::input-files :files '("sizeof.c")
                   :const *old*)

  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "point"
                       :right-members ("z")))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The split struct type may not appear
;; in the return type of a function definition.

(acl2::must-succeed*
  (c$::input-files :files '("ret-struct.c")
                   :const *old*)

  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "point"
                       :right-members ("z")))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Unnamed members (named and anonymous bit-fields, anonymous unions)
;; always stay in the left struct type,
;; since they cannot be listed in the right members.

(acl2::must-succeed*
  (c$::input-files :files '("anon-member.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "point"
                     :right-members ("z")
                     :new-tag "point_right")

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/anon-member.c"
    :content "struct point {
  int x;
  int b : 4;
  union { int c; int d; };
  int : 8;
};

struct point_right {
  int z;
};

static struct point p;

static struct point_right p_0;

int main(void) {
  p.c = 3;
  return p.x + p.b + p_0.z;
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Initializers which are split apart must be pure,
;; since splitting reorders them.

(acl2::must-succeed*
  (c$::input-files :files '("impure-init.c")
                   :const *old*)

  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "pair"
                       :right-members ("snd")))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The tag names a union type, not a struct type.

(acl2::must-succeed*
  (c$::input-files :files '("union.c")
                   :const *old*)

  ;; Without a filepath, the search reports that
  ;; no struct type with the tag exists.
  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "pair"
                       :right-members ("snd")))

  ;; With a filepath, the union-specific error is reported.
  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "pair"
                       :filepath "union.c"
                       :right-members ("snd")))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The struct type is defined in multiple translation units
;; (as if from a shared header).
;; Compatible struct types in other translation units are also split,
;; with the same right struct tag,
;; and the external object receives the same right name
;; in both translation units.

(acl2::must-succeed*
  (c$::input-files :files '("multi1.c" "multi2.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "point"
                     :right-members ("z")
                     :new-tag "point_right")

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/multi1.c"
    :content "struct point {
  int x;
  int y;
};

struct point_right {
  int z;
};

struct point p;

struct point_right p_0;

int getx(void) {
  return p.x;
}
")

  (assert-file-contents
    :file "new/multi2.c"
    :content "struct point {
  int x;
  int y;
};

struct point_right {
  int z;
};

extern struct point p;

extern struct point_right p_0;

int getz(void) {
  return p_0.z;
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The code ensemble must use the C17 standard.
;; (The transformation assumes the C17 struct type compatibility rules.)

(acl2::must-succeed*
  (c$::input-files :files '("test1.c")
                   :const *old*)

  (defconst *old-c23*
    (change-code-ensemble
      *old*
      :ienv (c$::change-ienv (c$::code-ensemble->ienv *old*)
                             :dialect (c::make-dialect
                                        :std (c::standard-c23)))))

  (must-fail
    (struct-type-split *old-c23*
                       *new*
                       :struct-tag "point"
                       :right-members ("z")))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The struct type is defined via a typedef.
;; The left declarations keep the typedef name,
;; while the right declarations reference the right struct type directly.

(acl2::must-succeed*
  (c$::input-files :files '("typedef.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "point"
                     :right-members ("z")
                     :new-tag "point_right")

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/typedef.c"
    :content "typedef struct point {
  int x;
} point_t;

struct point_right {
  int z;
};

static point_t p;

static struct point_right p_0;

int main(void) {
  p.x = 4;
  return p.x + p_0.z;
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A typedef denoting a derived type (here a pointer to the struct type)
;; is not supported, and is detected and rejected.
;; TODO: we need to consider how to better support typedefs.

(acl2::must-succeed*
  (c$::input-files :files '("typedef-ptr.c")
                   :const *old*)

  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "point"
                       :right-members ("z")
                       :new-tag "point_right"))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Safety checks: the split struct type may not appear in
;; array types, function types, or the members of
;; other struct or union types (including its own members).

(acl2::must-succeed*
  ;; An array of the split struct type.
  (c$::input-files :files '("array.c")
                   :const *old*)
  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "point"
                       :right-members ("z")))
  :with-output-off nil)

(acl2::must-succeed*
  ;; A member of another struct type.
  (c$::input-files :files '("member.c")
                   :const *old*)
  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "point"
                       :right-members ("z")))
  :with-output-off nil)

(acl2::must-succeed*
  ;; A pointer member of another struct type.
  (c$::input-files :files '("ptr-member.c")
                   :const *old*)
  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "point"
                       :right-members ("z")))
  :with-output-off nil)

(acl2::must-succeed*
  ;; A member of a union type.
  (c$::input-files :files '("union-member.c")
                   :const *old*)
  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "point"
                       :right-members ("z")))
  :with-output-off nil)

(acl2::must-succeed*
  ;; A self-referential struct type.
  (c$::input-files :files '("self-ref.c")
                   :const *old*)
  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "point"
                       :right-members ("z")))
  :with-output-off nil)

(acl2::must-succeed*
  ;; A function prototype returning a pointer to the split struct type.
  (c$::input-files :files '("fn-proto.c")
                   :const *old*)
  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "point"
                       :right-members ("z")))
  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Function parameters of splittable type are split in place,
;; in prototypes, definitions, and call sites.
;; (Note that the right parameters of the prototype and definition
;; of setz receive different fresh names;
;; this is valid, since prototype parameter names are immaterial.)

(acl2::must-succeed*
  (c$::input-files :files '("fn-param.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "point"
                     :right-members ("z")
                     :new-tag "point_right")

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/fn-param.c"
    :content "struct point {
  int x;
};

struct point_right {
  int z;
};

static struct point p;

static struct point_right p_0;

void setz(struct point *q, struct point_right *q_0, int v);

void setz(struct point *q, struct point_right *q_1, int v) {
  q_1->z = v;
}

int getx(struct point pt, struct point_right pt_0) {
  return pt.x;
}

int main(void) {
  setz(&p, &p_0, 5);
  return getx(p, p_0);
}
")

  :with-output-off nil)
