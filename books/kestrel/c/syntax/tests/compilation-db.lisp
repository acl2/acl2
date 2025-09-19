; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "std/testing/must-eval-to-t" :dir :system)

(include-book "../compilation-db")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *expected-db*
  (list
    (cons "bar.c"
          (make-comp-db-entry
            :exec "/usr/local/bin/gcc"
            :directory "/working-dir/c-project/bar"
            :output "/working-dir/c-project/bar/bar.o"
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
                                               :value "bar.o"))))
    (cons "foo.c"
          (make-comp-db-entry
            :exec "/usr/local/bin/gcc"
            :directory "/working-dir/c-project/"
            :arguments (list (make-comp-db-arg :name "-std"
                                               :separator "="
                                               :value "c17")
                             (make-comp-db-arg :name "-I"
                                               :separator ""
                                               :value "/usr/include/libfoo")
                             (make-comp-db-arg :name "-c"
                                               :separator "")
                             (make-comp-db-arg :name "foo.c"
                                               :separator ""))))))

(acl2::must-eval-to-t
  (b* (((mv erp db - state)
        (parse-comp-db "compile_commands.json" nil nil state))
       ((when erp)
        (value (cw "Error: ~@0~%" erp))))
    (value (equal db *expected-db*)))

  :with-output-off nil)
