;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "ACL2")

;; load other packages needed to define our new packages...
(include-book "std/portcullis" :dir :system)
(include-book "centaur/fty/portcullis" :dir :system)
(include-book "centaur/sv/tutorial/support" :dir :system)

;; define our new packages
(defpkg "SMT"
  (set-difference-eq
   (union-eq
    *acl2-exports*
    *standard-acl2-imports*
    *common-lisp-symbols-from-main-lisp-package*
    ;; Things we want to export
    '()
    ;; Things we want to import
    '(b*
      define
      defconsts
      more-returns
      l<
      tshell-ensure
      tshell-call
      set-raw-mode-on
      defines
      defxdoc
      defsection
      def-join-thms
      termify-clause-set
      body
      lambda-formals
      lambda-body
      pseudo-lambdap
      conjoin-clauses
      conjoin
      conjoin2
      disjoin
      disjoin2
      disjoin-lst
      pseudo-term-list-listp
      iff-implies-equal-not
      split-keyword-alist
      dumb-negate-lit
      must-succeed
      prefixp
      symbol-fix
      symbol-list-fix
      with-fast-alists
      formals
      strip-cadrs
      bfix
      real/rationalp

      read-string

      str::cat
      str::natstr
      str::strtok
      str::count
      str::substrp
      str::isubstrp
      str::strpos
      str::firstn-chars
      str::strval
      str::search
      str::nat-to-hex-chars
      str::hex-digit-char-listp
      str::charlisteqv
      str::character-list-fix
      str::str-fix
      str::downcase-string

      std::defaggregate
      std::defval

      fty::defprod
      fty::deflist
      fty::deffixtype
      fty::defalist
      fty::defoption

      sv::def-saved-event
      sv::deftutorial
      sv::$
      )
    )
   ;; Things to remove
   '(true-list-fix ; removed by Matt K. 12/2018, when added to *acl2-exports*
     good-atom-listp)))
