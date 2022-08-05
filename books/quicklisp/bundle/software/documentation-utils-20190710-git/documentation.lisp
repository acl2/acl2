#|
 This file is a part of documentation-utils
 (c) 2016 Shirakumo http://tymoon.eu (shinmera@tymoon.eu)
 Author: Nicolas Hafner <shinmera@tymoon.eu>
|#

(in-package #:org.shirakumo.documentation-utils)

(docs:define-docs
  (variable *documentation-tests*
    "Holds an alist of documentation types to test functions.

The function should take one argument, the specifier, and
return non-NIL if the symbol is bound for the given type.")

  (function documentation-test
    "Access the documentation test function for the given type.

See *DOCUMENTATION-TESTS*")
  
  (function remove-documentation-test
    "Remove the documentation test function for the given type.

See *DOCUMENTATION-TESTS*")

  (function define-documentation-test
    "Shorthand to define a documentation test function.

See *DOCUMENTATION-TESTS*")

  (variable *documentation-translators*
    "Holds an alist of documentation types to translator functions.

The function should take one argument, the specifier expression, and
return a documentation form suitable to access the documentation
for the given type.")

  (function documentation-translator
    "Access the documentation translator function for the given type.

See *DOCUMENTATION-TRANSLATORS*")

  (function remove-documentation-translator
    "Remove the documentation translator function for the given type.

See *DOCUMENTATION-TRANSLATORS*")

  (function define-documentation-translator
    "Shorthand to define a documentation translator function.

See *DOCUMENTATION-TRANSLATORS*")

  (function define-documentation-alias
    "Shorthand to define an alias to a translator.

This simply sets a delegating function that refers to the given type.

See *DOCUMENTATION-TRANSLATORS*")

  (function check
    "Checks whether all symbols have documentation for all known types.

If documentation is not set for a given symbol and type combination, a
warning is signalled.

See *DOCUMENTATION-TESTS*")

  (variable *default-formatter*
    "Variable for the default formatter to use.

This should be either a DOCUMENTATION-FORMATTER instance, or a symbol
naming the class of one.

By default this value is an instance of PLAIN-FORMATTER.

See DOCUMENTATION-FORMATTER
See PLAIN-FORMATTER
See DEFINE-DOCS")

  (type documentation-formatter
    "Base class for all documentation formatters.

A documentation formatter is responsible for translating user-defined
documentation expressions into docstrings usable by the underlying
documentation storage. This can also be used to hook it into other systems
that access documentation and may enrich it with further styling or
information.

The only relevant function for this class is FORMAT-DOCUMENTATION, which
is used to perform the translation.

See FORMAT-DOCUMENTATION")

  (function format-documentation
    "Processes the documentation string according to the formatter's rules.

Passed along are the three values that make up a documentation definition:

- The fundamental type of the definition as used in DOCUMENTATION.
- An additional set of variants used to distinguish more complicated
  definitions. For instance, for methods this would be the method qualifiers.
- The expression used for the actual documentation. This is always the last
  expression within a documentation definition expression.

The function should either error on an invalid documentation expression, or
return a string to be passed to the underlying documentation storage.

You may use this function to store the documentation expression elsewhere
so that it may be processed into different formats using additional markup
than is appropriate for plain strings.

See DOCUMENTATION-FORMATTER")

  (type plain-formatter
    "A formatter that only allows strings and emits them verbatim.

This is the default formatter.

See DOCUMENTATION-FORMATTER")

  (function split-body-options
    "Splits the body of expressions into two parts, a plist, and a body.

Returned are two values: a plist, and a body. The plist is composed of
all keyword-value pairs found at the beginning of the body. The returned
body is all the remaining expressions.")

  (function removef
    "Removes the given set of keys from the plist and returns a fresh copy.")

  (function define-docs
    "Allows you to comfortably and easily set the documentation for your library.

Each expression in the body can either take a two or many argument structure.
In the two argument structure, the type is implicitly assumed to be 
FUNCTION. The first argument is then the specifier, and the second the
documentation. In the many argument structure the first argument is the
type, the last is the documentation, and everything in between the specifier.

The expansion of the documentation accessor --and thus the structure of
the specifier-- is dependant on the applicable documentation translator.
By default, the expansion is simply (CL:DOCUMENTATION SPECIFIER TYPE).

In addition to the actual documentation expressions, the docs definition may
begin with a set of keyword-value pairs. These options supply initargs for
the documentation formatter. By default, the formatter is *DEFAULT-FORMATTER*,
but a formatter class of your own can be selected with the :FORMATTER option.
This formatter will then translate the documentation expression at compile time
to reduce it into a docstring as expected by the underlying documentation
storage. Note that the initarg values are used at macroexpansion time, and so
are used as literals. If the chosen formatter is already a formatter instance,
the initargs are used with REINITIALIZE-INSTANCE. Otherwise if the formatter
is a symbol, MAKE-INSTANCE Is used.

See *DOCUMENTATION-TRANSLATORS*
See FORMAT-DOCUMENTATION
See *DEFAULT-FORMATTER*"))
