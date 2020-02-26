; System Utilities -- Fresh Names
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/std/system/add-suffix-to-fn-or-const" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fresh-name-in-world-with-$s ((name (and (symbolp name)
                                                (not (keywordp name))))
                                     (names-to-avoid symbol-listp)
                                     (wrld plist-worldp))
  :returns (fresh-name "A @(tsee symbolp).")
  :mode :program
  :parents (system-utilities-non-built-in)
  :short "Append as many @('$') signs to a name
          as needed to make the name new in the world, i.e. not already in use,
          and not among a given list of names to avoid."
  :long
  "<p>
   The name returned by this function should be usable for
   a new function, theorem, constant, etc.
   </p>
   <p>
   Note that for a constant, the @('$') signs are appended before the final
   @('*') character.
   </p>
   <p>
   The input name must not be a keyword,
   because it would remain a keyword
   (which cannot be the name of a function, theorem, etc.)
   when @('$') signs are appended to it.
   </p>
   <p>
   Since symbols in the main Lisp package are not usable
   to name new functions, theorems, etc.,
   if the input name is in the main Lisp package,
   the output name is in the @('\"ACL2\"') package,
   and has at least one @('$') appended to it.
   </p>
   <p>
   If the input name is already new,
   not among the names to avoid,
   and not in the main Lisp package,
   it is returned unchanged.
   </p>"
  (if (or (logical-namep name wrld)
          (member name names-to-avoid)
          (equal (symbol-package-name name) *main-lisp-package-name*))
      (fresh-name-in-world-with-$s (add-suffix-to-fn-or-const name "$")
                                   names-to-avoid
                                   wrld)
    name)
  :no-function t)
