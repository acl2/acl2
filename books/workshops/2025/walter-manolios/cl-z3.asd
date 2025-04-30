(defsystem "cl-z3/ffi"
    :defsystem-depends-on ("cffi-grovel")
    :depends-on ("cffi")
    :serial t
    :pathname "src/ffi"
    :components
    ((:file "package")
     (:cffi-grovel-file "z3-grovel")
     (:file "z3-c-types")
     (:file "z3-c")
     (:file "z3-api")))

(defsystem "cl-z3/z3"
  :depends-on ("cl-z3/ffi" "trivia" "flexi-streams" "trivial-garbage" "parse-float")
  :serial t
  :pathname "src/z3"
  :components
  ((:file "package")
   (:file "match-extensions")
   (:file "util")
   (:file "types")
   (:file "globals")
   (:file "ast-vector")
   (:file "params")
   (:file "config")
   (:file "sorts")
   (:file "ast")
   (:file "func-decl")
   (:file "model")
   (:file "tactic")
   (:file "solver")
   (:file "api")))

(defsystem "cl-z3"
  :description "Common Lisp bindings for the Z3 SMT solver."
  :author "Andrew T. Walter <me@atwalter.com>"
  :license "MIT"
  :homepage "https://github.com/mister-walter/cl-z3/"
  :depends-on ("cl-z3/z3")
  :in-order-to ((test-op (test-op "cl-z3/tests"))))

(defsystem "cl-z3/tests"
    :depends-on ("cl-z3" "parachute")
    :pathname "test/"
    :components
    ((:file "package")
     (:file "tests" :depends-on ("package")))
    :perform (test-op (o c) (symbol-call :parachute :test :cl-z3/tests)))
