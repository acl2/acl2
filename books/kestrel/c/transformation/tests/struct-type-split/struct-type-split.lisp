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

  ;; Neither a struct tag nor a typedef name is specified.
  (must-fail
    (struct-type-split *old*
                       *new*
                       :right-members ("z")))

  ;; A struct tag and a typedef name cannot both be specified.
  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "point"
                       :typedef-name "point_t"
                       :right-members ("z")))

  ;; The typedef name does not exist.
  (must-fail
    (struct-type-split *old*
                       *new*
                       :typedef-name "nonexistent"
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
;; using the implicit designators recorded by the validator,
;; which are made explicit in the split initializer lists.

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
  struct pair x = {.fst = 1};
  struct pair_0 x_0 = {.snd = 2};
  return x_0.snd;
}
")

  :with-output-off nil)

(acl2::must-succeed*
  ;; When every explicit initializer is routed to one side, initialize the
  ;; other side with {0}; omitting its initializer would be wrong for an
  ;; automatic object, while an empty initializer list is not valid C17.
  (c$::input-files :files '("partial-init.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "pair"
                     :right-members ("snd"))

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/partial-init.c"
    :content "struct pair {
  int fst;
};

struct pair_0 {
  int snd;
};

int main(void) {
  struct pair left = {.fst = 1};
  struct pair_0 left_0 = {0};
  struct pair right = {0};
  struct pair_0 right_0 = {.snd = 2};
  return left_0.snd + right.fst;
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An initializer list with mixed explicit and implicit designations.
;; The implicit initializer (of z, following the explicit .y) is made
;; explicit when split apart; if it stayed positional, it would
;; initialize the wrong member (x) of the left struct type.

(acl2::must-succeed*
  (c$::input-files :files '("mixed-init.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "triple"
                     :right-members ("y"))

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/mixed-init.c"
    :content "struct triple {
  int x;
  int z;
};

struct triple_0 {
  int y;
};

int main(void) {
  struct triple t = {.z = 3};
  struct triple_0 t_0 = {.y = 2};
  return t.x + t.z;
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
;; The typedef is split into a parallel right typedef,
;; and uses of the typedef name are split accordingly.

(acl2::must-succeed*
  (c$::input-files :files '("typedef.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :typedef-name "point_t"
                     :right-members ("z")
                     :new-tag "point_right")

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/typedef.c"
    :content "typedef struct point {
  int x;
} point_t;

typedef struct point_right {
  int z;
} point_t_0;

static point_t p;

static point_t_0 p_0;

int main(void) {
  p.x = 4;
  return p.x + p_0.z;
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An untagged struct type can only be selected via its typedef name.
;; The split produces a second untagged struct and a fresh typedef name.

(acl2::must-succeed*
  (c$::input-files :files '("typedef-anon.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :typedef-name "point_t"
                     :right-members ("z"))

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/typedef-anon.c"
    :content "typedef struct {
  int x;
} point_t;

typedef struct {
  int z;
} point_t_0;

static point_t p;

static point_t_0 p_0;

int main(void) {
  p.x = 4;
  return p.x + p_0.z;
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A typedef denoting a derived type (here a pointer to the struct type)
;; is split into a parallel right typedef of the corresponding right type.

(acl2::must-succeed*
  (c$::input-files :files '("typedef-ptr.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "point"
                     :right-members ("z")
                     :new-tag "point_right")

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/typedef-ptr.c"
    :content "struct point {
  int x;
};

struct point_right {
  int z;
};

typedef struct point *pp_t;

typedef struct point_right *pp_t_0;

static struct point p;

static struct point_right p_0;

static pp_t q = &p;

static pp_t_0 q_0 = &p_0;

int main(void) {
  return q_0->z;
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A typedef chain: each typedef in the chain is split,
;; and the use of an earlier typedef in a later one is substituted.

(acl2::must-succeed*
  (c$::input-files :files '("typedef-chain.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "point"
                     :right-members ("z")
                     :new-tag "point_right")

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/typedef-chain.c"
    :content "struct point {
  int x;
};

struct point_right {
  int z;
};

typedef struct point pt_t;

typedef struct point_right pt_t_0;

typedef pt_t pt2_t;

typedef pt_t_0 pt2_t_0;

static pt2_t p;

static pt2_t_0 p_0;

int main(void) {
  p.x = 1;
  return p.x + p_0.z;
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  ;; Casting a pointer to the split struct type to void * exposes its
  ;; representation, so the safety check rejects the transformation.
  (c$::input-files :files '("pointer-cast.c")
                   :const *old*)

  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "point"
                       :right-members ("z")))

  :with-output-off nil)

(acl2::must-succeed*
  ;; An array of the split struct type, including field routing and
  ;; passing a pointer to an array element to a split function parameter.
  (c$::input-files :files '("array.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "point"
                     :right-members ("z")
                     :new-tag "point_right")

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/array.c"
    :content "struct point {
  int x;
};

struct point_right {
  int z;
};

static struct point arr[2];

static struct point_right arr_0[2];

static int get(struct point *p, struct point_right *p_0) {
  return p->x + p_0->z;
}

int main(void) {
  arr_0[1].z = arr[0].x;
  return get(&arr[1], &arr_0[1]);
}
")

  :with-output-off nil)

(acl2::must-succeed*
  ;; Multidimensional arrays, arrays of pointers, abstract array declarators,
  ;; ordinary and [*] parameter arrays, and VLAs with pure bounds.
  (c$::input-files :files '("array-declarators.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "point"
                     :right-members ("z")
                     :new-tag "point_right")

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/array-declarators.c"
    :content "struct point {
  int x;
};

struct point_right {
  int z;
};

static struct point matrix[2][3];

static struct point_right matrix_0[2][3];

static struct point *ptrs[2];

static struct point_right *ptrs_0[2];

static int first(struct point (*)[3], struct point_right (*)[3]);

static int sum(int, struct point [*][3], struct point_right [*][3]);

static int sum(int n, struct point a[n][3], struct point_right a_0[n][3]) {
  return a[1][2].x + a_0[1][2].z;
}

static int first(struct point (*p)[3], struct point_right (*p_0)[3]) {
  return (*p)[0].x + (*p_0)[0].z;
}

static int use_vla(int n) {
  struct point vla[n][2];
  struct point_right vla_0[n][2];
  vla[0][1].x = 1;
  vla_0[0][1].z = 2;
  return vla[0][1].x + vla_0[0][1].z;
}

int main(void) {
  ptrs[0] = &matrix[0][0];
  ptrs_0[0] = &matrix_0[0][0];
  return sum(2, matrix, matrix_0) + first(matrix, matrix_0) + ptrs[0]->x + use_vla(2);
}
")

  :with-output-off nil)

(acl2::must-succeed*
  ;; Whole-array member initializers, multidimensional designators, an inferred
  ;; extent whose maximum index routes right, and an array compound literal.
  (c$::input-files :files '("array-initializers.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "point"
                     :right-members ("z")
                     :new-tag "point_right")

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/array-initializers.c"
    :content "struct point {
  int x;
};

struct point_right {
  int z;
};

struct holder {
  struct point grid[2][3];
  struct point_right grid_0[2][3];
};

static struct holder h = {.grid = {[0][1] = {.x = 1}, [1][2].x = 3}, .grid_0 = {[0][1] = {.z = 2}, [1][2].z = 4}};

static struct point inferred[] = {[5] = {0}, [2].x = 5};

static struct point_right inferred_0[] = {[5].z = 6};

static int sum(struct point a[2], struct point_right a_0[2]) {
  return a[0].x + a_0[1].z;
}

int main(void) {
  return h.grid[0][1].x + h.grid_0[1][2].z + inferred[2].x + inferred_0[5].z + sum((struct point [2]) {[0] = {.x = 7}, [1] = {.x = 9}}, (struct point_right [2]) {[0] = {.z = 8}, [1] = {.z = 10}});
}
")

  :with-output-off nil)

(acl2::must-succeed*
  ;; A split array bound is duplicated into the left and right declarations,
  ;; so an effectful bound is rejected.
  (c$::input-files :files '("array-vla-effectful.c")
                   :const *old*)

  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "point"
                       :right-members ("z")
                       :new-tag "point_right"))

  :with-output-off nil)

(acl2::must-succeed*
  ;; A split array subscript duplicates the index expression,
  ;; so an effectful index is rejected.
  (c$::input-files :files '("array-index-effectful.c")
                   :const *old*)

  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "point"
                       :right-members ("z")
                       :new-tag "point_right"))

  :with-output-off nil)

(acl2::must-succeed*
  ;; After the first positional array initializer, the validator records the
  ;; remaining position as unknown because C types do not currently retain
  ;; array lengths.  Without an effective array designator, the transformation
  ;; cannot safely split the later initializer.
  (c$::input-files :files '("array-init-positional.c")
                   :const *old*)

  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "point"
                       :right-members ("z")
                       :new-tag "point_right"))

  :with-output-off nil)

(acl2::must-succeed*
  ;; Designated array initializers route through the array designator
  ;; and then through the split struct member designator.
  (c$::input-files :files '("array-init-designated.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "point"
                     :right-members ("z")
                     :new-tag "point_right")

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/array-init-designated.c"
    :content "struct point {
  int x;
};

struct point_right {
  int z;
};

static struct point arr[2] = {[0] = {.x = 1}, [1].x = 3};

static struct point_right arr_0[2] = {[0] = {.z = 2}, [1].z = 4};

int main(void) {
  return arr[0].x + arr_0[1].z;
}
")

  :with-output-off nil)

(acl2::must-succeed*
  ;; The largest explicitly initialized index determines the size of an array
  ;; of unknown size (C17 6.7.9/22).  Preserve that index in both initializer
  ;; partitions even when the initializers at that index all route left.
  (c$::input-files :files '("array-init-inferred-designated.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "point"
                     :right-members ("z")
                     :new-tag "point_right")

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/array-init-inferred-designated.c"
    :content "struct point {
  int x;
};

struct point_right {
  int z;
};

static struct point arr[] = {[5].x = 1, };

static struct point_right arr_0[] = {[5] = {0}, [2].z = 2, };

int main(void) {
  return arr[5].x + arr_0[2].z + arr_0[5].z;
}
")

  :with-output-off nil)

(acl2::must-succeed*
  ;; An array member of splittable element type is split in place.
  ;; Direct designators through the array route individual fields and split
  ;; whole designated elements.
  (c$::input-files :files '("array-member.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "point"
                     :right-members ("z")
                     :new-tag "point_right")

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/array-member.c"
    :content "struct point {
  int x;
};

struct point_right {
  int z;
};

struct outer {
  struct point arr[2];
  struct point_right arr_0[2];
  int w;
};

static struct outer o = {.arr[0].x = 1, .arr_0[0].z = 2, .arr[1] = {.x = 3}, .arr_0[1] = {.z = 4}, .w = 9};

int main(void) {
  return o.arr[0].x + o.arr_0[1].z;
}
")

  :with-output-off nil)

(acl2::must-succeed*
  ;; Splitting a flexible array member would create two flexible array
  ;; members, making the first one no longer the last member of the struct.
  (c$::input-files :files '("array-member-flexible.c")
                   :const *old*)

  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "point"
                       :right-members ("z")
                       :new-tag "point_right"))

  :with-output-off nil)

(acl2::must-succeed*
  ;; An anonymous struct may precede a direct flexible array member: its
  ;; promoted named members count toward the flexible-array constraint.
  ;; The direct flexible array member is still rejected.
  (c$::input-files :files '("array-member-flexible-after-anon.c")
                   :const *old*)

  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "point"
                       :right-members ("z")
                       :new-tag "point_right"))

  :with-output-off nil)

(acl2::must-succeed*
  ;; Standard C does not permit a struct containing a flexible array member
  ;; to be embedded in another struct, even as its final anonymous member.
  ;; If the validator or an extension admits this form, recursive processing
  ;; of the anonymous struct must still reject the flexible array member.
  (c$::input-files :files '("array-member-flexible-nested-anon.c")
                   :const *old*)

  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "point"
                       :right-members ("z")
                       :new-tag "point_right"))

  :with-output-off nil)

(acl2::must-succeed*
  ;; The validator does not retain array sizes, so conservatively reject an
  ;; array member whose size is hidden by a typedef: it may be flexible.
  (c$::input-files :files '("array-member-sized-typedef.c")
                   :const *old*)

  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "point"
                       :right-members ("z")
                       :new-tag "point_right"))

  :with-output-off nil)

(acl2::must-succeed*
  ;; A member of another struct type is split in place.
  (c$::input-files :files '("member.c")
                   :const *old*)


  (struct-type-split *old*
                     *new*
                     :struct-tag "point"
                     :right-members ("z")
                     :new-tag "point_right")

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/member.c"
    :content "struct point {
  int x;
};

struct point_right {
  int z;
};

struct outer {
  struct point inner;
  struct point_right inner_0;
};

static struct outer o;

int main(void) {
  return o.inner.x;
}
")

  :with-output-off nil)

(acl2::must-succeed*
  ;; A pointer member of another struct type is split in place,
  ;; including in the initializer of the containing object.
  (c$::input-files :files '("ptr-member.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "point"
                     :right-members ("z")
                     :new-tag "point_right")

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/ptr-member.c"
    :content "struct point {
  int x;
};

struct point_right {
  int z;
};

struct node {
  struct point *p;
  struct point_right *p_0;
};

static struct point pt;

static struct point_right pt_0;

static struct node n = {.p = &pt, .p_0 = &pt_0};

int main(void) {
  return n.p->x;
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  ;; By-value members of splittable type are split in place,
  ;; and their initializers are split accordingly.
  ;; The braced, brace-elided (flat), and designated forms are all supported;
  ;; in each case the split-apart member initializers are given explicit
  ;; designations, and any trailing positional initializer (here of w)
  ;; continues to designate the correct member.
  (c$::input-files :files '("member-init.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "point"
                     :right-members ("z")
                     :new-tag "point_right")

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/member-init.c"
    :content "struct point {
  int x;
};

struct point_right {
  int z;
};

struct outer {
  struct point inner;
  struct point_right inner_0;
  int w;
};

static struct outer braced = {.inner = {.x = 1}, .inner_0 = {.z = 2}, 9};

static struct outer flat = {.inner.x = 1, .inner_0.z = 2, 9};

static struct outer desig = {.inner = {.x = 1}, .inner_0 = {.z = 2}, .w = 9};

int main(void) {
  return braced.inner.x + flat.w + desig.inner_0.z;
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  ;; A struct type that transitively contains the split struct type
  ;; (here via a member of the directly containing struct type)
  ;; is left unchanged; the split member is still split in place
  ;; within the nested initializer, and member accesses are routed.
  (c$::input-files :files '("nested-init.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "point"
                     :right-members ("z")
                     :new-tag "point_right")

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/nested-init.c"
    :content "struct point {
  int x;
};

struct point_right {
  int z;
};

struct outer {
  struct point inner;
  struct point_right inner_0;
  int w;
};

struct wrapper {
  struct outer out;
  int tag;
};

static struct wrapper w = {{.inner = {.x = 1}, .inner_0 = {.z = 2}, 9}, 7};

int main(void) {
  return w.out.inner.x + w.out.inner_0.z;
}
")

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
  ;; A splittable member of an untagged (e.g. typedef'd) struct type
  ;; is split in place, like a member of a tagged struct type.
  (c$::input-files :files '("untagged-member.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "point"
                     :right-members ("z")
                     :new-tag "point_right")

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/untagged-member.c"
    :content "struct point {
  int x;
};

struct point_right {
  int z;
};

typedef struct {
  struct point inner;
  struct point_right inner_0;
  int w;
} container;

static container c = {.inner = {.x = 1}, .inner_0 = {.z = 2}, 9};

int main(void) {
  return c.inner.x + c.inner_0.z;
}
")

  :with-output-off nil)

(acl2::must-succeed*
  ;; A splittable member of an untagged struct type, accessed via a pointer.
  (c$::input-files :files '("untagged-ptr.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "point"
                     :right-members ("z")
                     :new-tag "point_right")

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/untagged-ptr.c"
    :content "struct point {
  int x;
};

struct point_right {
  int z;
};

typedef struct {
  struct point inner;
  struct point_right inner_0;
  int w;
} container;

static container c;

static container *p = &c;

int main(void) {
  return p->inner.x + p->inner_0.z;
}
")

  :with-output-off nil)

(acl2::must-succeed*
  ;; A splittable member of an anonymous (promoted) struct member is split
  ;; in place; the split members are registered under, and promoted into,
  ;; the enclosing struct type, so the promoted accesses are routed.
  (c$::input-files :files '("anon-struct.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "point"
                     :right-members ("z")
                     :new-tag "point_right")

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/anon-struct.c"
    :content "struct point {
  int x;
};

struct point_right {
  int z;
};

struct outer {
  struct { struct point inner; struct point_right inner_0; };
  int w;
};

static struct outer o;

int main(void) {
  return o.inner.x + o.inner_0.z;
}
")

  :with-output-off nil)

(acl2::must-succeed*
  ;; A splittable member of an anonymous union member is not supported,
  ;; since it is effectively a member of a union.
  (c$::input-files :files '("anon-union.c")
                   :const *old*)

  (must-fail
    (struct-type-split *old*
                       *new*
                       :struct-tag "point"
                       :right-members ("z")))

  :with-output-off nil)

(acl2::must-succeed*
  ;; A fresh right member name avoids the enclosing struct type's full
  ;; member namespace, including members promoted from anonymous members.
  ;; Here the right member of the promoted inner is named inner_1,
  ;; since inner_0 already names a member of outer.
  (c$::input-files :files '("blacklist.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "point"
                     :right-members ("z")
                     :new-tag "point_right")

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/blacklist.c"
    :content "struct point {
  int x;
};

struct point_right {
  int z;
};

struct outer {
  struct { struct point inner; struct point_right inner_1; };
  int inner_0;
};

static struct outer o;

int main(void) {
  return o.inner.x + o.inner_1.z + o.inner_0;
}
")

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The split struct type may occur as a member, possibly within arrays or
;; behind pointers, within a function parameter type.  The parameter type is
;; left unchanged
;; (the occurrence is split in the member's struct type),
;; and the accesses in the function body are routed.

(acl2::must-succeed*
  (c$::input-files :files '("fn-param-member.c")
                   :const *old*)

  (struct-type-split *old*
                     *new*
                     :struct-tag "point"
                     :right-members ("z")
                     :new-tag "point_right")

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/fn-param-member.c"
    :content "struct point {
  int x;
};

struct point_right {
  int z;
};

typedef struct {
  struct point inner;
  struct point_right inner_0;
  int w;
} container;

int get(container *c) {
  return c->inner.x + c->inner_0.z;
}

int main(void) {
  container c;
  return get(&c);
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This has a self-referential struct that is separate from the one being split,
;; but it exhibits the fact that, when checking the safety of a cast,
;; which involves traversing the self-referential struct type,
;; we need to avoid a loop that follows the self references.

(acl2::must-succeed*

 (c$::input-files :files '("self-ref-checks.c")
                  :const *old*)

 (struct-type-split *old*
                    *new*
                    :struct-tag "s"
                    :right-members ("b")
                    :new-tag "s2")

 (c$::output-files :const *new*
                   :base-dir "new")

 (assert-file-contents
  :file "new/self-ref-checks.c"
  :content "struct s {
  int a;
};

struct s2 {
  int b;
};

struct selfref {
  int x;
  struct selfref *y;
};

static struct selfref sr;

static struct s s;

static struct s2 s_0;

int main(void) {
  struct selfref *p = (struct selfref *) &sr;
  return s_0.b;
}
")

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This tests correct safety checks of incomplete structure types.

(acl2::must-succeed*

 (c$::input-files :files '("opaque.c")
                  :const *old*)

 (struct-type-split *old*
                    *new*
                    :struct-tag "target"
                    :right-members ("right")
                    :new-tag "target2")

 (c$::output-files :const *new*
                   :base-dir "new")

 (assert-file-contents
  :file "new/opaque.c"
  :content "struct opaque;

struct target {
  int left;
};

struct target2 {
  int right;
};
")

 :with-output-off nil)
