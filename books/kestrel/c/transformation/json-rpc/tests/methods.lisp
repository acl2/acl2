; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSONRPC")

(include-book "../top")
(include-book "../../tests/utilities")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We call the methods directly rather than via process-json-rpc-file,
; because the latter writes its JSON-RPC response with a non-bang output
; channel, which ACL2 forbids during make-event expansion.
; Over a live socket (run-jsonrpc-server) the full dispatch path is exercised.
; The methods run on a local code environment (see with-local-stobj below),
; so the tests do not depend on, or change, the global one.

(defun make-params-members (pairs)
  (declare (xargs :mode :program))
  (if (endp pairs)
      nil
    (cons (make-member :name (caar pairs) :value (cdar pairs))
          (make-params-members (cdr pairs)))))

(defun make-params (pairs)
  (declare (xargs :mode :program))
  (make-structured-object :members (make-params-members pairs)))

(defun strings-value (strings)
  (declare (xargs :mode :program))
  (value-array (if (endp strings)
                   nil
                 (cons (value-string (car strings))
                       (value-array->elements
                        (strings-value (cdr strings)))))))

(defun error-code-p (code erp)
  (declare (xargs :mode :program))
  (and (errorp erp)
       (equal (error->code erp) code)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A session of requests: read the file, attempt some bad requests, split the
;; struct, write the result, and manage the names.  The transformed file is
;; checked below.

(defun methods-session (c2c::code-env state)
  (declare (xargs :mode :program :stobjs (c2c::code-env state)))
  (b* (;; The environment starts empty.
       ((mv erp res) (list-ensembles c2c::code-env))
       ((unless (and (not erp) (equal res (strings-value nil))))
        (mv (msg "Initial list-ensembles: ~x0 ~x1" erp res) c2c::code-env state))
       ;; Read the file.
       (read-params
        (make-params
         (list (cons "output-ensemble" (value-string "orig"))
               (cons "base-dir" (value-string "input-files"))
               (cons "files" (strings-value (list "test1.c")))
               (cons "preprocess" (value-false)))))
       ((mv erp res c2c::code-env state)
        (input-files read-params c2c::code-env state))
       ((unless (and (not erp) (equal res (value-null))))
        (mv (msg "input-files: ~x0 ~x1" erp res) c2c::code-env state))
       ;; Reading into a bound name requires overwrite.
       ((mv erp & c2c::code-env state)
        (input-files read-params c2c::code-env state))
       ((unless (error-code-p -32602 erp))
        (mv (msg "input-files without overwrite: ~x0" erp) c2c::code-env state))
       ;; A duplicate parameter name is rejected.
       ((mv erp & c2c::code-env state)
        (input-files (make-params
                      (list (cons "output-ensemble" (value-string "dup"))
                            (cons "files" (strings-value (list "test1.c")))
                            (cons "files" (strings-value (list "test1.c")))))
                     c2c::code-env
                     state))
       ((unless (error-code-p -32602 erp))
        (mv (msg "duplicate parameter: ~x0" erp) c2c::code-env state))
       ;; An unbound source is rejected.
       ((mv erp & c2c::code-env)
        (struct-type-split (make-params
                            (list (cons "input-ensemble" (value-string "nope"))
                                  (cons "output-ensemble" (value-string "split"))
                                  (cons "struct-tag" (value-string "point"))
                                  (cons "right-members"
                                        (strings-value (list "z")))))
                           c2c::code-env))
       ((unless (error-code-p -32602 erp))
        (mv (msg "unbound source: ~x0" erp) c2c::code-env state))
       ;; A failing transformation leaves the environment unchanged.
       ((mv erp & c2c::code-env)
        (struct-type-split (make-params
                            (list (cons "input-ensemble" (value-string "orig"))
                                  (cons "output-ensemble" (value-string "bad"))
                                  (cons "struct-tag" (value-string "nosuchtag"))
                                  (cons "right-members"
                                        (strings-value (list "z")))))
                           c2c::code-env))
       ((unless (error-code-p -32603 erp))
        (mv (msg "failing transformation: ~x0" erp) c2c::code-env state))
       ;; Split the struct.
       ((mv erp res c2c::code-env)
        (struct-type-split (make-params
                            (list (cons "input-ensemble" (value-string "orig"))
                                  (cons "output-ensemble" (value-string "split"))
                                  (cons "struct-tag" (value-string "point"))
                                  (cons "right-members"
                                        (strings-value (list "z")))
                                  (cons "new-tag" (value-string "point_right"))
                                  (cons "safety-checks" (value-false))))
                           c2c::code-env))
       ((unless (and (not erp)
                     (equal res (value-object
                                 (list (make-member
                                        :name "warnings"
                                        :value (value-array nil)))))))
        (mv (msg "struct-type-split: ~x0 ~x1" erp res) c2c::code-env state))
       ;; Transforming in place requires overwrite.
       ((mv erp & c2c::code-env)
        (struct-type-split (make-params
                            (list (cons "input-ensemble" (value-string "split"))
                                  (cons "output-ensemble" (value-string "split"))
                                  (cons "struct-tag" (value-string "point"))
                                  (cons "right-members"
                                        (strings-value (list "y")))))
                           c2c::code-env))
       ((unless (error-code-p -32602 erp))
        (mv (msg "in-place without overwrite: ~x0" erp) c2c::code-env state))
       ;; Write the result.
       ((mv erp res state)
        (output-files (make-params
                       (list (cons "input-ensemble" (value-string "split"))
                             (cons "base-dir" (value-string "out"))))
                      c2c::code-env
                      state))
       ((unless (and (not erp) (equal res (value-null))))
        (mv (msg "output-files: ~x0 ~x1" erp res) c2c::code-env state))
       ;; The names, in sorted order; the failed transformation bound nothing.
       ((mv erp res) (list-ensembles c2c::code-env))
       ((unless (and (not erp)
                     (equal res (strings-value (list "orig" "split")))))
        (mv (msg "list-ensembles: ~x0 ~x1" erp res) c2c::code-env state))
       ;; Drop a name, which may then not be dropped again.
       ((mv erp & c2c::code-env)
        (drop-ensemble (make-params (list (cons "ensemble" (value-string "orig"))))
                       c2c::code-env))
       ((when erp)
        (mv (msg "drop-ensemble: ~x0" erp) c2c::code-env state))
       ((mv erp & c2c::code-env)
        (drop-ensemble (make-params (list (cons "ensemble" (value-string "orig"))))
                       c2c::code-env))
       ((unless (error-code-p -32602 erp))
        (mv (msg "drop of an unbound name: ~x0" erp) c2c::code-env state))
       ((mv erp res) (list-ensembles c2c::code-env))
       ((unless (and (not erp) (equal res (strings-value (list "split")))))
        (mv (msg "list-ensembles after drop: ~x0 ~x1" erp res)
            c2c::code-env
            state)))
    (mv nil c2c::code-env state)))

(defun run-methods-session (state)
  (declare (xargs :mode :program :stobjs state))
  (with-local-stobj c2c::code-env
    (mv-let (erp c2c::code-env state)
      (methods-session c2c::code-env state)
      (mv erp state))))

(make-event
 (b* (((mv erp state) (run-methods-session state))
      ((when erp) (mv erp nil state)))
   (mv nil '(value-triple :methods-session-passed) state)))

;; The transformed C file matches the expected split.

(c2c::assert-file-contents
  :file "out/test1.c"
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The preprocess-args parameter also accepts a per-file map.

(make-event
 (b* ((params
       (value-object
        (list (make-member :name "preprocess-args"
                           :value
                           (value-object
                            (list
                             (make-member
                              :name "test1.c"
                              :value (strings-value
                                      (list "-I include" "-DDEBUG")))
                             (make-member
                              :name "subdir/test2.c"
                              :value (strings-value
                                      (list "-I subdir/include")))))))))
      ((mv erp preprocess-args) (c2c::param->preprocess-args params))
      ((when erp)
       (mv (msg "preprocess-args parser failed: ~x0" erp) nil state))
      (expected (omap::update
                 "subdir/test2.c"
                 (list "-I subdir/include")
                 (omap::update
                  "test1.c"
                  (list "-I include" "-DDEBUG")
                  nil)))
      ((unless (equal preprocess-args expected))
       (mv (msg "Unexpected preprocess-args: ~x0" preprocess-args)
           nil state)))
   (mv nil '(value-triple :preprocess-args-map-parsed) state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The other transformations, on the inputs of the command-line tests
;; (see kestrel/c/transformation/command-line/tests).

(defun expect-result (what erp res expected)
  (declare (xargs :mode :program))
  (and (or erp (not (equal res expected)))
       (msg "~s0: ~x1 ~x2" what erp res)))

(defun read-test-files (name files c2c::code-env state)
  (declare (xargs :mode :program :stobjs (c2c::code-env state)))
  (b* (((mv erp res c2c::code-env state)
        (input-files (make-params
                      (list (cons "output-ensemble" (value-string name))
                            (cons "base-dir" (value-string "input-files"))
                            (cons "files" (strings-value files))
                            (cons "preprocess" (value-false))))
                     c2c::code-env
                     state)))
    (mv (expect-result name erp res (value-null)) c2c::code-env state)))

(defun write-test-files (name c2c::code-env state)
  (declare (xargs :mode :program :stobjs (c2c::code-env state)))
  (b* (((mv erp res state)
        (output-files (make-params
                       (list (cons "input-ensemble" (value-string name))
                             (cons "base-dir" (value-string "out"))))
                      c2c::code-env
                      state)))
    (mv (expect-result name erp res (value-null)) c2c::code-env state)))

(defun transformations-session (c2c::code-env state)
  (declare (xargs :mode :program :stobjs (c2c::code-env state)))
  (b* (;; split-gso
       ((mv erp c2c::code-env state)
        (read-test-files "gso" (list "file1.c" "file2.c") c2c::code-env state))
       ((when erp) (mv erp c2c::code-env state))
       ((mv erp res c2c::code-env)
        (split-gso (make-params
                    (list (cons "input-ensemble" (value-string "gso"))
                          (cons "output-ensemble" (value-string "gso-split"))
                          (cons "object-name" (value-string "foo_data"))
                          (cons "split-members"
                                (strings-value (list "a2" "a2_size")))))
                   c2c::code-env))
       (erp (expect-result "split-gso" erp res (value-null)))
       ((when erp) (mv erp c2c::code-env state))
       ;; simpadd0
       ((mv erp c2c::code-env state)
        (read-test-files "simp" (list "file3.c") c2c::code-env state))
       ((when erp) (mv erp c2c::code-env state))
       ((mv erp res c2c::code-env)
        (simpadd0 (make-params
                   (list (cons "input-ensemble" (value-string "simp"))
                         (cons "output-ensemble" (value-string "simp-done"))))
                  c2c::code-env))
       (erp (expect-result "simpadd0" erp res (value-null)))
       ((when erp) (mv erp c2c::code-env state))
       ;; split-fn, whose split point must be a natural number
       ((mv erp c2c::code-env state)
        (read-test-files "fn" (list "file4.c") c2c::code-env state))
       ((when erp) (mv erp c2c::code-env state))
       ((mv erp & c2c::code-env)
        (split-fn (make-params
                   (list (cons "input-ensemble" (value-string "fn"))
                         (cons "output-ensemble" (value-string "fn-split"))
                         (cons "target" (value-string "foo"))
                         (cons "new-fn" (value-string "foo_new"))
                         (cons "split-point" (value-number -1))))
                  c2c::code-env))
       ((unless (error-code-p -32602 erp))
        (mv (msg "split-fn with a negative split point: ~x0" erp)
            c2c::code-env
            state))
       ((mv erp res c2c::code-env)
        (split-fn (make-params
                   (list (cons "input-ensemble" (value-string "fn"))
                         (cons "output-ensemble" (value-string "fn-split"))
                         (cons "target" (value-string "foo"))
                         (cons "new-fn" (value-string "foo_new"))
                         (cons "split-point" (value-number 1))))
                  c2c::code-env))
       (erp (expect-result "split-fn" erp res (value-null)))
       ((when erp) (mv erp c2c::code-env state))
       ;; wrap-fn, with targets given as an object
       ((mv erp c2c::code-env state)
        (read-test-files "wrap" (list "file8.c") c2c::code-env state))
       ((when erp) (mv erp c2c::code-env state))
       ((mv erp & c2c::code-env)
        (wrap-fn (make-params
                  (list (cons "input-ensemble" (value-string "wrap"))
                        (cons "output-ensemble" (value-string "wrapped"))
                        (cons "targets"
                              (value-object
                               (list (make-member :name "foo"
                                                  :value (value-number 3)))))))
                 c2c::code-env))
       ((unless (error-code-p -32602 erp))
        (mv (msg "wrap-fn with a bad wrapper name: ~x0" erp)
            c2c::code-env
            state))
       ((mv erp res c2c::code-env)
        (wrap-fn (make-params
                  (list (cons "input-ensemble" (value-string "wrap"))
                        (cons "output-ensemble" (value-string "wrapped"))
                        (cons "targets"
                              (value-object
                               (list (make-member
                                      :name "foo"
                                      :value (value-string "foo_wrapper")))))))
                 c2c::code-env))
       (erp (expect-result "wrap-fn" erp res (value-null)))
       ((when erp) (mv erp c2c::code-env state))
       ;; add-section-attr, with and without a file path
       ((mv erp c2c::code-env state)
        (read-test-files "sect" (list "file9.c" "file10.c") c2c::code-env state))
       ((when erp) (mv erp c2c::code-env state))
       ((mv erp & c2c::code-env)
        (add-section-attr
         (make-params
          (list (cons "input-ensemble" (value-string "sect"))
                (cons "output-ensemble" (value-string "sectioned"))
                (cons "attrs"
                      (value-array
                       (list (value-object
                              (list (make-member
                                     :name "target"
                                     :value (value-object
                                             (list (make-member
                                                    :name "name"
                                                    :value (value-string
                                                            "foo")))))
                                    (make-member
                                     :name "section"
                                     :value (value-string "foosection")))))))))
         c2c::code-env))
       ((unless (error-code-p -32602 erp))
        (mv (msg "add-section-attr with a bad target member: ~x0" erp)
            c2c::code-env
            state))
       ((mv erp res c2c::code-env)
        (add-section-attr
         (make-params
          (list (cons "input-ensemble" (value-string "sect"))
                (cons "output-ensemble" (value-string "sectioned"))
                (cons "attrs"
                      (value-array
                       (list (value-object
                              (list (make-member
                                     :name "target"
                                     :value (value-object
                                             (list (make-member
                                                    :name "filepath"
                                                    :value (value-string
                                                            "file9.c"))
                                                   (make-member
                                                    :name "ident"
                                                    :value (value-string
                                                            "foo")))))
                                    (make-member
                                     :name "section"
                                     :value (value-string "foosection"))))
                             (value-object
                              (list (make-member
                                     :name "target"
                                     :value (value-object
                                             (list (make-member
                                                    :name "filepath"
                                                    :value (value-null))
                                                   (make-member
                                                    :name "ident"
                                                    :value (value-string
                                                            "bar")))))
                                    (make-member
                                     :name "section"
                                     :value (value-string
                                             "barsection")))))))))
         c2c::code-env))
       (erp (expect-result "add-section-attr" erp res (value-null)))
       ((when erp) (mv erp c2c::code-env state))
       ;; Write all the results.
       ((mv erp c2c::code-env state)
        (write-test-files "gso-split" c2c::code-env state))
       ((when erp) (mv erp c2c::code-env state))
       ((mv erp c2c::code-env state)
        (write-test-files "simp-done" c2c::code-env state))
       ((when erp) (mv erp c2c::code-env state))
       ((mv erp c2c::code-env state)
        (write-test-files "fn-split" c2c::code-env state))
       ((when erp) (mv erp c2c::code-env state))
       ((mv erp c2c::code-env state)
        (write-test-files "wrapped" c2c::code-env state))
       ((when erp) (mv erp c2c::code-env state)))
    (write-test-files "sectioned" c2c::code-env state)))

(defun run-transformations-session (state)
  (declare (xargs :mode :program :stobjs state))
  (with-local-stobj c2c::code-env
    (mv-let (erp c2c::code-env state)
      (transformations-session c2c::code-env state)
      (mv erp state))))

(make-event
 (b* (((mv erp state) (run-transformations-session state))
      ((when erp) (mv erp nil state)))
   (mv nil '(value-triple :transformations-session-passed) state)))

;; The transformed C files.

;; split-gso

(c2c::assert-file-contents
  :file "out/file1.c"
  :content "struct foo {
  char a1[20];
  int a1_size;
  char a2[30];
  int a2_size;
};

struct foo_0 {
  char a1[20];
  int a1_size;
};

struct foo_1 {
  char a2[30];
  int a2_size;
};

static struct foo_0 foo_data_0 = {.a1_size = 0};

static struct foo_1 foo_data_1 = {.a2_size = 0};

int bar() {
  return foo_data_0.a1_size;
}
")

;; simpadd0

(c2c::assert-file-contents
  :file "out/file3.c"
  :content "// This file is generated by 'simpadd0'.

int foo(int x) {
  return x;
}
")

;; split-fn

(c2c::assert-file-contents
  :file "out/file4.c"
  :content "int foo_new(int *x) {
  int y = 2;
  return (*x) + y;
}

int foo() {
  int x = 0;
  return foo_new(&x);
}
")

;; wrap-fn

(c2c::assert-file-contents
  :file "out/file8.c"
  :content "extern double foo(int x, int y);

static double foo_wrapper(int x, int y) {
  return foo(x, y);
}

int main(void) {
  foo_wrapper(0, 1);
}
")

;; add-section-attr (with a file path)

(c2c::assert-file-contents
  :file "out/file9.c"
  :content "__attribute__ ((section(\"foosection\"))) int foo(int y, int z) {
  int x = 5;
  return x + y - z;
}
")

;; add-section-attr (without a file path)

(c2c::assert-file-contents
  :file "out/file10.c"
  :content "__attribute__ ((section(\"barsection\"))) int bar(int y, int z) {
  int x = 5;
  return x + y - z;
}
")
