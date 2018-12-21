(in-package "ACL2")

; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

;;ACL2 symbols that are imported by all packages:

(defmacro shared-symbols ()
  '(union-eq *acl2-exports*
    (union-eq *common-lisp-symbols-from-main-lisp-package*
     (union-eq (other-acl2-symbols)
      (union-eq (fp-symbols)
       (union-eq (rtl-symbols)
		 (nondet-symbols)))))))

;;Miscellaneous symbols that are not in *acl2-exports*:

(defmacro other-acl2-symbols ()
  ''(zp set-ignore-ok set-irrelevant-formals-ok disable enable defthm string-append))

;;Functions that are defioned in the FP library:

(defmacro fp-symbols () ; many omitted for this toy
  ''(fl cg))

;;RTL functions:

(defmacro rtl-symbols ()
  ''(?? log< log<= log> log>= log= log<> logand1 logior1 comp1 bitn bits shft cat mulcat bvecp))

;;Nondeterministic functions:

(defmacro nondet-symbols () ; many omitted for this toy
  ''(natp unknown))

(defpkg "*" (shared-symbols))

(defpkg "+" (shared-symbols))
