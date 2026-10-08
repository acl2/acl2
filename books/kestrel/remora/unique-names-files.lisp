; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "unique-names")
(include-book "utility-transforms")

(include-book "portcullis")

(local (include-book "std/typed-lists/string-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Unique binder names in files.
;
; The declarations of a file are scoped like the bindings of one :LET (see
; DECL-LIST-TO-BINDS), so the notions of UNIQUE-NAMES carry over to files
; through that :LET: its binders are the declared names and the binders
; inside the declarations.

(define file-duplicate-names ((f filep))
  :returns (dup-names string-listp)
  :parents (unique-names)
  :short "List the names bound by more than one binder in a file."
  :long
  (xdoc::topstring
   (xdoc::p
    "The binders are the names declared by the file and the binders inside
     its declarations, i.e. those of the @(':let') whose bindings are the
     declarations (see @(tsee decl-list-to-binds)), as for @(tsee
     expr-duplicate-names).  Returns @('nil') if they are all distinct."))
  (b* ((binds (decl-list-to-binds (file->decls f))))
    (duplicated-names (append (bind-list-names binds)
                              (bind-list-binder-names binds)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule expr-kind-of-expr-uniquify-names-of-expr-let
  :parents (expr-uniquify-names)
  :short "Uniquifying a @(':let') yields a @(':let')."
  (equal (expr-kind (expr-uniquify-names (expr-let binds body)))
         :let)
  :enable expr-uniquify-names
  :expand ((:free (used r) (uniq-expr (expr-let binds body) used r))))

(define file-uniquify-names ((f filep))
  :returns (new-f filep)
  :parents (unique-names)
  :short "Rename binders so that all binder names in a file are distinct."
  :long
  (xdoc::topstring
   (xdoc::p
    "The declarations are turned into the bindings of one @(':let'), over a
     placeholder body that binds nothing; that is uniquified by @(tsee
     expr-uniquify-names); and the declarations are read back off the
     bindings of the result, which is a @(':let') too.  Afterwards @(tsee
     file-duplicate-names) returns @('nil'): see @(tsee
     file-duplicate-names-of-file-uniquify-names).  The imports are carried
     through unchanged, and a file with no declarations is returned as it
     is.")
   (xdoc::p
    "@(tsee expr-uniquify-names) keeps a name unless it has already been
     seen, as a free variable, a primitive operation, or the name of an
     earlier binder; so a declared name is kept unless it is also, for
     instance, the name of a parameter in an earlier declaration.  The
     entry points are recognized by their names in the input, as in @(tsee
     monomorphize-file), so an entry point that is renamed becomes a
     definition."))
  (b* (((file f) f)
       ((when (endp f.decls)) (file-fix f))
       (new-expr (expr-uniquify-names
                  (expr-let (decl-list-to-binds f.decls)
                            (make-expr-array-empty
                             :dims nil
                             :type (type-base (base-type-int))))))
       (entry-names (decl-list-entry-names f.decls)))
    (make-file :imports f.imports
               :decls (bind-list-to-decls (expr-let->binds new-expr)
                                          entry-names)))
  :guard-hints (("Goal" :expand ((decl-list-to-binds (file->decls f))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The binder names of the :LET that the declarations are read back from
; begin with those of its bindings, which are therefore distinct too.

(defruled no-duplicatesp-equal-of-append-prefix
  (implies (no-duplicatesp-equal (append x y z))
           (no-duplicatesp-equal (append x y)))
  :induct (len x)
  :enable (no-duplicatesp-equal append len))

(defruled duplicated-names-of-let-binds-when-no-expr-duplicate-names
  (implies (and (equal (expr-kind e) :let)
                (not (expr-duplicate-names e)))
           (not (duplicated-names
                 (append (bind-list-names (expr-let->binds e))
                         (bind-list-binder-names (expr-let->binds e))))))
  :enable expr-duplicate-names
  :disable (duplicated-names-when-no-duplicatesp-equal
            no-duplicatesp-equal-when-not-duplicated-names)
  :expand ((expr-binder-names e))
  :use ((:instance no-duplicatesp-equal-when-not-duplicated-names
                   (names (expr-binder-names e)))
        (:instance no-duplicatesp-equal-of-append-prefix
                   (x (bind-list-names (expr-let->binds e)))
                   (y (bind-list-binder-names (expr-let->binds e)))
                   (z (expr-binder-names (expr-let->body e))))
        (:instance duplicated-names-when-no-duplicatesp-equal
                   (names (append (bind-list-names (expr-let->binds e))
                                  (bind-list-binder-names
                                   (expr-let->binds e)))))))

; Turning the bindings back into declarations and those into bindings again
; gives the same bindings.

(defrule decl-list-to-binds-of-bind-list-to-decls
  :parents (bind-list-to-decls)
  (equal (decl-list-to-binds (bind-list-to-decls binds entry-names))
         (bind-list-fix binds))
  :induct (len binds)
  :enable (decl-list-to-binds
           bind-list-to-decls
           decl-to-bind
           bind-to-decl
           bind-list-fix
           len))

(defrule file-duplicate-names-of-file-uniquify-names
  :parents (file-uniquify-names file-duplicate-names)
  :short "After @(tsee file-uniquify-names), @(tsee file-duplicate-names)
          returns @('nil'): all binder names in the resulting file are
          distinct."
  (equal (file-duplicate-names (file-uniquify-names f))
         nil)
  :enable (file-duplicate-names file-uniquify-names)
  :disable (duplicated-names-when-no-duplicatesp-equal
            no-duplicatesp-equal-when-not-duplicated-names)
  :expand ((decl-list-to-binds (file->decls f)))
  :use ((:instance duplicated-names-of-let-binds-when-no-expr-duplicate-names
                   (e (expr-uniquify-names
                       (expr-let (decl-list-to-binds (file->decls f))
                                 (make-expr-array-empty
                                  :dims nil
                                  :type (type-base (base-type-int)))))))))
