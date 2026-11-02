; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-eval-to-t" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

(include-book "../compilation-db")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Parsing.

(defconst *expected-db*
  (list
    (cons "foo.o"
          (make-comp-db-entry
            :exec "/usr/local/bin/gcc"
            :directory "/working-dir/c-project/"
            :file "foo.c"
            :arguments (list (make-comp-db-arg :name "-std"
                                               :separator "="
                                               :value "c17")
                             (make-comp-db-arg :name "-I"
                                               :separator ""
                                               :value "/usr/include/libfoo")
                             (make-comp-db-arg :name "-c"
                                               :separator "")
                             (make-comp-db-arg :name "foo.c"
                                               :separator ""))))
    (cons "/working-dir/c-project/bar/bar.o"
          (make-comp-db-entry
            :exec "/usr/local/bin/gcc"
            :directory "/working-dir/c-project/bar"
            :file "bar.c"
            :arguments (list (make-comp-db-arg :name "-ggdb"
                                               :separator "")
                             (make-comp-db-arg :name "-O"
                                               :separator ""
                                               :value "0")
                             (make-comp-db-arg :name "-W"
                                               :separator ""
                                               :value "all")
                             (make-comp-db-arg :name "-c"
                                               :separator "")
                             (make-comp-db-arg :name "bar.c"
                                               :separator "")
                             (make-comp-db-arg :name "-o"
                                               :separator " "
                                               :value "bar.o"))))))

(acl2::must-eval-to-t
  (b* (((mv erp db state)
        (parse-comp-db "compile_commands.json" state))
       ((when erp)
        (acl2::value (cw "Error: ~@0~%" erp))))
    (acl2::value (equal db *expected-db*)))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helpers to build entries, parsing their arguments as in a compilation
;; database.

(defun strings-to-json-values (strings)
  (declare (xargs :mode :program))
  (if (endp strings)
      nil
    (cons (json::value-string (first strings))
          (strings-to-json-values (rest strings)))))

(defun test-args (strings)
  (declare (xargs :mode :program))
  (b* (((mv erp args)
        (json-to-comp-db-arguments (strings-to-json-values strings))))
    (if erp
        (er hard? 'test-args "~@0" erp)
      args)))

(defun test-entry (directory file strings)
  (declare (xargs :mode :program))
  (make-comp-db-entry :exec "cc"
                      :directory directory
                      :file file
                      :arguments (test-args strings)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Outputs not recorded in the compilation database.

(acl2::assert-equal
  (comp-db-implicit-output "lib/foo.c" (test-args '("-c" "lib/foo.c")))
  "foo.o")

(acl2::assert-equal
  (comp-db-implicit-output "foo.c"
                           (test-args '("-c" "foo.c" "-o" "a.o" "-o" "b.o")))
  "b.o")

(acl2::assert-equal
  (comp-db-implicit-output "foo.tar.c" (test-args '("-S" "foo.tar.c")))
  "foo.tar.s")

(acl2::assert-equal
  (comp-db-implicit-output "foo.c" (test-args '("-E" "foo.c")))
  nil)

(acl2::assert-equal
  (comp-db-implicit-output "foo.c" (test-args '("-E" "foo.c" "-o" "foo.i")))
  "foo.i")

(acl2::assert-equal
  (comp-db-implicit-output
    "foo.c"
    (test-args '("-c" "-fsyntax-only" "foo.c" "-o" "foo.o")))
  nil)

(acl2::assert-equal
  (comp-db-implicit-output "foo.c" (test-args '("foo.c")))
  "a.out")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Paths.

(acl2::assert-equal
  (comp-db-absolute-path "/a/b" "c/d.c")
  "/a/b/c/d.c")

(acl2::assert-equal
  (comp-db-absolute-path "/a/b/" "../c/./d.c")
  "/a/c/d.c")

(acl2::assert-equal
  (comp-db-absolute-path "/a/b" "c/../../d.o")
  "/a/d.o")

(acl2::assert-equal
  (comp-db-absolute-path "/a/b" "/x//y.c")
  "/x/y.c")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Selection, on a compilation database whose paths are already absolute.

(defconst *select-db*
  (list (cons "/p/a.o" (test-entry "/p" "/p/a.c" '("-DA")))
        (cons "/p/b.o" (test-entry "/p" "/p/b1.c" nil))
        (cons "/p/b.o" (test-entry "/p" "/p/b2.c" nil))
        (cons "/p/c.o" (test-entry "/p" "/p/c.c" '("-DC")))
        (cons "/p/c.o" (test-entry "/p" "/p/c.c" '("-DC")))
        (cons "/p/c-pic.o" (test-entry "/p" "/p/c.c" '("-fPIC")))
        (cons "/p/d.o" (test-entry "/p" "/p/d.S" nil))))

;; Relative and repeated objects, and an object produced by agreeing entries.
(acl2::assert-equal
  (b* (((mv erp db warnings)
        (comp-db-select *select-db* '("a.o" "./a.o" "x/../c.o") "/p")))
    (list erp db warnings))
  (list nil
        (list (assoc-equal "/p/a.o" *select-db*)
              (assoc-equal "/p/c.o" *select-db*))
        nil))

;; An object produced by no entry.
(acl2::assert-equal
  (b* (((mv erp & &) (comp-db-select *select-db* '("a.o" "e.o") "/p")))
    (and erp t))
  t)

;; An object produced by entries with different source files.
(acl2::assert-equal
  (b* (((mv erp & &) (comp-db-select *select-db* '("b.o") "/p")))
    (and erp t))
  t)

;; An object compiled from an assembly file.
(acl2::assert-equal
  (b* (((mv erp db warnings)
        (comp-db-select *select-db* '("a.o" "d.o") "/p")))
    (list erp (strip-cars db) (len warnings)))
  '(nil ("/p/a.o") 1))

;; A source file compiled into more than one selected object.
(acl2::assert-equal
  (b* (((mv & db &) (comp-db-select *select-db* '("c.o" "c-pic.o") "/p")))
    (and (comp-db-check-unique-files db) t))
  t)

(acl2::assert-equal
  (b* (((mv & db &) (comp-db-select *select-db* '("a.o" "c.o") "/p")))
    (comp-db-check-unique-files db))
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The whole transformation, on a compilation database as parsed, with relative
;; paths. The project is in the "proj" subdirectory of the connected book
;; directory, but none of its files need to exist.

(defun proj-db (state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((dir (concatenate 'string (cbd) "proj/build")))
    (list (cons "a.o"
                (test-entry dir "../src/a.c"
                            '("-c" "../src/a.c" "-I../include" "-o" "a.o")))
          (cons "a-pic.o"
                (test-entry dir "../src/a.c"
                            '("-c" "../src/a.c" "-fPIC" "-o" "a-pic.o")))
          (cons "b.o"
                (test-entry dir "../src/b.c"
                            '("-c" "../src/b.c" "-o" "b.o")))
          (cons "x.o"
                (test-entry dir "/elsewhere/x.c"
                            '("-c" "/elsewhere/x.c" "-o" "x.o"))))))

(acl2::must-eval-to-t
  (b* (((mv erp map &)
        (to-preprocess-map (proj-db state)
                           "."
                           '("proj/build/a.o" "proj/build/b.o")
                           state)))
    (acl2::value
      (and (not erp)
           (equal map
                  (list (list "proj/src/a.c"
                              (concatenate
                                'string
                                "-I"
                                (string-escape-for-shell
                                  (concatenate 'string
                                               (cbd)
                                               "proj/include"))))
                        (list "proj/src/b.c")))))))

;; A source file compiled into more than one selected object.
(acl2::must-eval-to-t
  (b* (((mv erp & &)
        (to-preprocess-map (proj-db state)
                           "."
                           '("proj/build/a.o" "proj/build/a-pic.o")
                           state)))
    (acl2::value (and erp t))))

;; The same, when selecting all the entries.
(acl2::must-eval-to-t
  (b* (((mv erp & &)
        (to-preprocess-map (butlast (proj-db state) 1) "." :all state)))
    (acl2::value (and erp t))))

;; A source file which is not in the project directory.
(acl2::must-eval-to-t
  (b* (((mv erp & &)
        (to-preprocess-map (proj-db state) "." '("proj/build/x.o") state)))
    (acl2::value (and erp t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Inputs of defpreprocess-map.

(acl2::must-fail
  (defpreprocess-map *bad-objects*
    :file "compile_commands.json"
    :objects "foo.o"))

;; The source files of compile_commands.json are not in this directory.
(acl2::must-fail
  (defpreprocess-map *outside-path*
    :file "compile_commands.json"))
