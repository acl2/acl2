; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "kestrel/std/util/defmacro-plus" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ pack (&rest args)
  :parents (atc-implementation)
  :short "Build a symbol in the C package from a list of atoms."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a concise wrapper of the built-in @(tsee acl2::packn-pos),
     specialized for the C package.
     This macro takes any number of arguments,
     which are evaluated and put into a list passed to @(tsee acl2::packn-pos);
     thus, the arguments must be all atoms."))
  `(acl2::packn-pos (list ,@args) (pkg-witness "C")))
