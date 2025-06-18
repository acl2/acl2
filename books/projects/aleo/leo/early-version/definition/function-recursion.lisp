; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "files")

(include-book "centaur/depgraph/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ function-recursion
  :parents (static-semantics)
  :short "Function recursion checks in Leo."
  :long
  (xdoc::topstring
   (xdoc::p
    "Functions may call other functions,
     but currently any kind of (direct or indirect) recursion is prohibited.
     Some forms of bounded recursion may be allowed in the future,
     but for now that is not the case.")
   (xdoc::p
    "Thus, the Leo static semantics includes the requirement that
     there is no function recursion.
     Here we formalize this requirement,
     by constructing a dependency graph among the functions
     and ensuring that there are no circularities in the graph."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines expressions-callees
  :short "Functions called by expressions and lists of expressions."

  (define expression-callees ((expr expressionp))
    :returns (callees identifier-setp)
    :parents (function-recursion expressions-callees)
    :short "Functions called by an expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "If a non-static struct member function call is not resolved
       (i.e. it does not have the struct type name),
       we return @('nil').
       Thus, this is correct only if that struct type name is present,
       i.e. if the function recursion check is performed after type inference.
       We will enforce this by
       defining a predicate requiring the presence of the struct type name
       and using that as guard of this ACL2 function."))
    (expression-case
     expr
     :literal nil
     :var/const nil
     :assoc-const nil
     :unary (expression-callees expr.arg)
     :binary (set::union (expression-callees expr.arg1)
                         (expression-callees expr.arg2))
     :cond (set::union (expression-callees expr.test)
                       (set::union (expression-callees expr.then)
                                   (expression-callees expr.else)))
     :unit nil
     :tuple (expression-list-callees expr.components)
     :tuple-component (expression-callees expr.tuple)
     :struct (struct-init-list-callees expr.components)
     :struct-component (expression-callees expr.struct)
     :internal-call (set::insert expr.fun
                             (expression-list-callees expr.args))
     :external-call nil ; TODO
     :static-call nil) ; TODO
    :measure (expression-count expr))

  (define expression-list-callees ((exprs expression-listp))
    :returns (callees identifier-setp)
    :parents (function-recursion expressions-callees)
    :short "Functions called by a list of expressions."
    (cond ((endp exprs) nil)
          (t (set::union (expression-callees (car exprs))
                         (expression-list-callees (cdr exprs)))))
    :measure (expression-list-count exprs))

  (define struct-init-callees ((cinit struct-initp))
    :returns (callees identifier-setp)
    :parents (function-recursion expressions-callees)
    :short "Functions called by a struct component initializer."
    (expression-callees (struct-init->expr cinit))
    :measure (struct-init-count cinit))

  (define struct-init-list-callees ((cinits struct-init-listp))
    :returns (callees identifier-setp)
    :parents (function-recursion expressions-callees)
    :short "Functions called by a list of struct component initializers."
    (cond ((endp cinits) nil)
          (t (set::union (struct-init-callees (car cinits))
                         (struct-init-list-callees (cdr cinits)))))
    :measure (struct-init-list-count cinits))

  :verify-guards nil ; done below
  ///
  (verify-guards expression-callees)

  (fty::deffixequiv-mutual expressions-callees))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vardecl-callees ((decl vardeclp))
  :returns (callees identifier-setp)
  :short "Functions called by a variable declaration."
  (expression-callees (vardecl->init decl))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define constdecl-callees ((decl constdeclp))
  :returns (callees identifier-setp)
  :short "Functions called by a constant declaration."
  (expression-callees (constdecl->init decl))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define console-callees ((cnsl consolep))
  :returns (callees identifier-setp)
  :short "Functions called by a console call."
  (console-case
   cnsl
   :assert (expression-callees cnsl.arg)
   :error (expression-list-callees cnsl.exprs)
   :log (expression-list-callees cnsl.exprs))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines statements-callees
  :short "Functions called by
          statements,
          lists of statements,
          branches,
          and lists of branches."

  (define statement-callees ((stmt statementp))
    :returns (callees identifier-setp)
    :parents (function-recursion statements-callees)
    :short "Functions called by a statement."
    (statement-case
     stmt
     :let (vardecl-callees stmt.get)
     :const (constdecl-callees stmt.get)
     :assign (set::union (expression-callees stmt.left)
                         (expression-callees stmt.right))
     :return (expression-callees stmt.value)
     :for (set::union (set::union (expression-callees stmt.from)
                                  (expression-callees stmt.to))
                      (statement-list-callees stmt.body))
     :if (set::union (branch-list-callees stmt.branches)
                     (statement-list-callees stmt.else))
     :console (console-callees stmt.get)
     ;; TODO: the next three
     :finalize nil
     :increment nil
     :decrement nil
     :block (statement-list-callees stmt.get))
    :measure (statement-count stmt))

  (define statement-list-callees ((stmts statement-listp))
    :returns (callees identifier-setp)
    :parents (function-recursion statements-callees)
    :short "Functions called by a list of statements."
    (cond ((endp stmts) nil)
          (t (set::union (statement-callees (car stmts))
                         (statement-list-callees (cdr stmts)))))
    :measure (statement-list-count stmts))

  (define branch-callees ((branch branchp))
    :returns (callees identifier-setp)
    :parents (function-recursion statements-callees)
    :short "Functions called by a branch."
    (set::union (expression-callees (branch->test branch))
                (statement-list-callees (branch->body branch)))
    :measure (branch-count branch))

  (define branch-list-callees ((branches branch-listp))
    :returns (callees identifier-setp)
    :parents (function-recursion statements-callees)
    :short "Functions called by a list of branchess."
    (cond ((endp branches) nil)
          (t (set::union (branch-callees (car branches))
                         (branch-list-callees (cdr branches)))))
    :measure (branch-list-count branches))

  :verify-guards nil ; done below
  ///
  (verify-guards statement-callees)

  (fty::deffixequiv-mutual statements-callees))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fundecl-call-graph ((decl fundeclp))
  :returns (graph alistp)
  :short "Call graph induced by a function declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return a dependency graph expressing that
     the declared function depends on (i.e. calls)
     the functions directly called in its body.
     The format is that of an alist for the "
    (xdoc::seetopic "depgraph::depgraph" "dependency graph library")
    "."))
  (b* (((fundecl decl) decl)
       (caller decl.name)
       (callees (statement-list-callees decl.body)))
    (list (cons caller callees)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define topdecl-call-graph ((decl topdeclp))
  :returns (graph alistp)
  :short "Call graph induced by a top-level declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "A struct declaration induces no call graph."))
  (topdecl-case decl
                :function (fundecl-call-graph decl.get)
                :struct nil
                ;; TODO: make sure next is OK
                :mapping nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define topdecl-list-call-graph ((decls topdecl-listp))
  :returns (graph alistp)
  :short "Call graph induced by a list of top-level declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee topdecl-call-graph) to lists.
     We return the union of the graphs for each element of the list.
     Note that type checking ensures the absence of
     different declarations of the same function,
     ensuring that the unioned alists have disjoint keys."))
  (cond ((endp decls) nil)
        (t (append (topdecl-call-graph (car decls))
                   (topdecl-list-call-graph (cdr decls)))))
  :hooks (:fix)
  :prepwork ((local (include-book "std/alists/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define file-function-recursion-okp ((file filep))
  :returns (yes/no booleanp)
  :short "Check if a Leo file has no function recursion."
  :long
  (xdoc::topstring
   (xdoc::p
    "We build the call graph of the file,
     by going through all the top-level declarations that form the file.
     Then we attempt to topologically sort the graph.
     If that succeeds, the graph has no circularities
     and therefore there is no function recursion.
     If that fails, there is a recursion."))
  (b* ((graph (topdecl-list-call-graph (programdecl->items (file->program file))))
       ;; TODO: consider imports
       ((mv okp &) (depgraph::toposort graph)))
    okp)
  :hooks (:fix))
