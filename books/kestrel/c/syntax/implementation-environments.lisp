; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../language/implementation-environments")

(local (include-book "arithmetic/top" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ implementation-environments
  :parents (syntax-for-tools)
  :short "Implementation environments for the C syntax for tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our "
    (xdoc::seetopic "c::language"
                    "formalization of C")
    " includes a notion of "
    (xdoc::seetopic "c::implementation-environments"
                    "implementation environments")
    ", which we also need to use for our C syntax for tools,
     specifically for certain tools that operate on it.
     Currently the C syntax for tools only depends on
     some but not all aspects of implementation environments,
     namely the applicable inputs of @(tsee input-files).
     Here we provide a simplified constructor of implementation environments
     that only takes some of the parameters as choices,
     and hardwired the rest."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-simple ((short-bytes posp)
                     (int-bytes posp)
                     (long-bytes posp)
                     (llong-bytes posp)
                     (plain-chars-signed booleanp)
                     (gcc booleanp))
  :guard (and (>= short-bytes 2)
              (>= int-bytes 2)
              (>= long-bytes 4)
              (>= llong-bytes 8)
              (<= short-bytes int-bytes)
              (<= int-bytes long-bytes)
              (<= long-bytes llong-bytes))
  :returns (ienv ienvp)
  :short "Simplified constructor of implementation environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(see implementation-environments),
     this only depends on the applicable inputs of @(tsee input-files):
     see that documentation.")
   (xdoc::p
    "We set the rest of the implementation environment parameters as follows:")
   (xdoc::ul
    (xdoc::li
     "Characters (i.e. bytes) are 8 bits.")
    (xdoc::li
     "Signed integers are two's complement.")
    (xdoc::li
     "There are no padding bits.")
    (xdoc::li
     "There are no trap representations.")))
  (b* ((uchar-format (c::uchar-format-8))
       (schar-format (c::schar-format-8tcnt))
       (char-format (c::char-format plain-chars-signed))
       (short-format (c::integer-format-inc-sign-tcnpnt (* 8 short-bytes)))
       (int-format (c::integer-format-inc-sign-tcnpnt (* 8 int-bytes)))
       (long-format (c::integer-format-inc-sign-tcnpnt (* 8 long-bytes)))
       (llong-format (c::integer-format-inc-sign-tcnpnt (* 8 llong-bytes)))
       (char+short+int+long+llong-format
        (c::char+short+int+long+llong-format uchar-format
                                             schar-format
                                             char-format
                                             short-format
                                             int-format
                                             long-format
                                             llong-format)))
    (c::make-ienv
     :char+short+int+long+llong-format char+short+int+long+llong-format
     :gcc gcc))
  :guard-hints
  (("Goal"
    :in-theory
    (enable c::char+short+int+long+llong-format-wfp
            c::integer-format-short-wfp-of-integer-format-inc-sign-tcnpnt
            c::integer-format-int-wfp-of-integer-format-inc-sign-tcnpnt
            c::integer-format-long-wfp-of-integer-format-inc-sign-tcnpnt
            c::integer-format-llong-wfp-of-integer-format-inc-sign-tcnpnt
            fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-default ()
  :short "A default implementation environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This has no particular significance,
     but we set all the byte sizes to their minima,
     and the plain @('char') flag to @('nil') (i.e. unsigned);
     we also disable GCC extensions."))
  (ienv-simple 2 2 4 8 nil nil))
