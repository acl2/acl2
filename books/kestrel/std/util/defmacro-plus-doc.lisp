; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defmacro+
  :parents (std::std/util-extensions std/util defmacro)
  :short "An enhancement of @(tsee defmacro)
          with <see topic='@(url xdoc)'>XDOC</see> integration."
  :long
  "<p>This is like @(tsee defmacro),
      but it also allows the user to include keyword options
      @(':parents'), @(':short'), and @(':long').
      None, some, or all those keywords may be present,
      in any order, and anywhere after the macro arguments.</p>
   <p>Besides generating the @(tsee defmacro)
      obtained by removing those keyword options,
      @('defmacro+') also generates a @(tsee defsection) around the macro,
      with the specified parents, short string, and long string, if any.
      The long string is augmented with a @('@(def ...)') for the macro.</p>")
