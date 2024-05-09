## About documentation-utils
This is a small library to help you with managing the docstrings for your library.

## How To
The central element is the `define-docs` macro. It takes a body of expressions to define the documentation. In the simplest form, this looks like so:

    (docs:define-docs
      (my-function "Some documentation"))

If you need a different type of documentation, or want to be explicit, prepend its type to the expression.

    (docs:define-docs
      (function my-function "Some documentation")
      (variable *my-variable* "Something else"))

In order to make things look more homely, aliases exist that can be used instead:

    (docs:define-docs
      (defun my-function
        "Some documentation")
      (defvar *my-variable*
        "Something else"))

Aliases exist for most of the `def*` expressions. Some expressions can take multiple arguments for the specifier, but the last in the expression is always the docstring:

    (docs:define-docs
      (defmethod foo :append ((num integer) other)
        "stuff"))

You can also extend this system for your own documentation translators. If you need more complex behaviour than the default of `(documentation specifier type)`, see `define-documentation-translator`. If you are defining a new documentation type, you should also add a `documentation-test` to ensure that `check` can verify that you actually did set a documentation.

## Custom Documentation Syntax
In case you would like to use a richer markup than plaintext within your documentation, you can use the `formatter` facility. Formatters take the last expression in a documentation definition expression and translate it to a docstring. This means that, with the right formatter, you can use a format other than plain docstrings, or even hook this into another documentation processing system in order to emit richer text while staying compatible to the standard `cl:documentation` facility.

In order to switch the formatter, you can use the `define-docs` options like so:

    (docs:define-docs
      :formatter my-formatter
      (function my-function
        (:arguments (a "Something about this"
                     b "Something about that")
         :return-value "Nothing useful"
         :summary "This function does something, though I don't know what.")))

Aside from the `:formatter` option, you can pass an arbitrary number of other options as well, which will be used as initargs for the formatter instance. Note that this is all done at macroexpansion-time, and the initarg values are thus used as literals.

The formatter presented above is just an example and is not provided by documentation-utils. Since I can't anticipate people's overall preferences in documentation style, it is up to you to write something more complicated to extend documentation-utils capabilities. Doing so should just be a matter of subclassing `formatter` and adding a method to `format-documentation`, though. As an example, the above could be done as follows:

    (defclass my-formatter (formatter) ())
    
    (defmethod format-documentation ((formatter my-formatter) type var docs)
      (format NIL "~a~@[
    
    Arguments:~{
      ~a: ~a~}~]~@[
    
    Return value:
      ~a~]"
              (getf docs :summary)
              (getf docs :arguments)
              (getf docs :return-value)))

I'm sure you can imagine your own way of doing things.

## Multiple Language Support
If you would like to provide documentation for your system in multiple languages, you can use the `multilang-documentation-utils` system, which relies on [multilang-documentation](https://shinmera.github.io/multilang-documentation). You can then use a plist of languages and docstrings as the docstring in a definition.

Note that this uses the formatter mechanism to do its work. If you want to use a custom formatter in addition, you'll need to change it to output the appropriate docstrings to `multilang-documentation:documentation`.

    (docs:define-docs
      :formatter docs:multilang-formatter
      (function foo
        (:en "Does some fooey"
         :de "Macht einen Quatsch"
         :ja "出鱈目をします。")))
