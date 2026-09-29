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
         (list (cons "target" (value-string "orig"))
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
                      (list (cons "target" (value-string "dup"))
                            (cons "files" (strings-value (list "test1.c")))
                            (cons "files" (strings-value (list "test1.c")))))
                     c2c::code-env
                     state))
       ((unless (error-code-p -32602 erp))
        (mv (msg "duplicate parameter: ~x0" erp) c2c::code-env state))
       ;; An unbound source is rejected.
       ((mv erp & c2c::code-env)
        (struct-type-split (make-params
                            (list (cons "source" (value-string "nope"))
                                  (cons "target" (value-string "split"))
                                  (cons "struct-tag" (value-string "point"))
                                  (cons "right-members"
                                        (strings-value (list "z")))))
                           c2c::code-env))
       ((unless (error-code-p -32602 erp))
        (mv (msg "unbound source: ~x0" erp) c2c::code-env state))
       ;; A failing transformation leaves the environment unchanged.
       ((mv erp & c2c::code-env)
        (struct-type-split (make-params
                            (list (cons "source" (value-string "orig"))
                                  (cons "target" (value-string "bad"))
                                  (cons "struct-tag" (value-string "nosuchtag"))
                                  (cons "right-members"
                                        (strings-value (list "z")))))
                           c2c::code-env))
       ((unless (error-code-p -32603 erp))
        (mv (msg "failing transformation: ~x0" erp) c2c::code-env state))
       ;; Split the struct.
       ((mv erp res c2c::code-env)
        (struct-type-split (make-params
                            (list (cons "source" (value-string "orig"))
                                  (cons "target" (value-string "split"))
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
                            (list (cons "source" (value-string "split"))
                                  (cons "target" (value-string "split"))
                                  (cons "struct-tag" (value-string "point"))
                                  (cons "right-members"
                                        (strings-value (list "y")))))
                           c2c::code-env))
       ((unless (error-code-p -32602 erp))
        (mv (msg "in-place without overwrite: ~x0" erp) c2c::code-env state))
       ;; Write the result.
       ((mv erp res state)
        (output-files (make-params
                       (list (cons "source" (value-string "split"))
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
        (drop-ensemble (make-params (list (cons "name" (value-string "orig"))))
                       c2c::code-env))
       ((when erp)
        (mv (msg "drop-ensemble: ~x0" erp) c2c::code-env state))
       ((mv erp & c2c::code-env)
        (drop-ensemble (make-params (list (cons "name" (value-string "orig"))))
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
