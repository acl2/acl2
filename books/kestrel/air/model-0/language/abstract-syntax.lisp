; AIR Library
; Model 0: Abstract Syntax
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributor: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "AIR-M0")

(include-book "../library-extensions")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/defprojection" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax
  :parents (model-0)
  :short "Abstract syntax of Model 0 ISA."
  :long
  (xdoc::topstring
   (xdoc::p
    "Model 0 has a minimal instruction set with three opcodes:
     @('INCR'), @('DECR'), and @('HALT').
     A program is simply a list of opcodes.")
   (xdoc::p
    "We do not define a concrete syntax (textual representation);
     programs are constructed directly as ACL2 data structures."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum opcode
  :short "Fixtype of Model 0 opcodes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The three opcodes are:")
   (xdoc::ul
    (xdoc::li "@(':incr') - increment the accumulator (with wrap-around)")
    (xdoc::li "@(':decr') - decrement the accumulator (with wrap-around)")
    (xdoc::li "@(':halt') - halt execution")))
  (:incr ())
  (:decr ())
  (:halt ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist program
  :short "Fixtype of Model 0 programs."
  :long
  (xdoc::topstring
   (xdoc::p
    "A program is a list of opcodes.
     Execution begins at position 0 and proceeds sequentially
     until a @('HALT') instruction is reached."))
  :elt-type opcode
  :true-listp t
  :elementp-of-nil nil
  :pred program-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fetch ((prog program-p) (pc natp))
  :returns (op opcode-p)
  :guard (< pc (len prog))
  :short "Fetch the opcode at the given program counter."
  (opcode-fix (nth pc prog))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection fetch-list ((prog program-p) (x nat-listp))
  :guard (all-< x (len prog))
  :returns (opcodes program-p)
  :short "Lift @(tsee fetch) to lists."
  (fetch prog x)
  ///
  (fty::deffixequiv fetch-list
    :args ((prog program-p) (x nat-listp))))
