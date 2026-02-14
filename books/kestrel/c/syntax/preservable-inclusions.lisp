; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc preservable-inclusions
  :parents (preprocessor)
  :short "Preservation of @('#include') directives in our preprocessor."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our preprocessor attempts to preserve @('#include') directives,
     instead of expanding them as done in typical preprocessors.
     This is not always possible,
     because the semantics of @('#include')
     is to replace the directive with the file and continue preprocessing:
     nothing prevents the replacement from referencing previous macros.")
   (xdoc::p
    "For instance, consider a file of the form")
   (xdoc::codeblock
    "..."
    "#define M ..."
    "..."
    "#include FILE"
    "...")
   (xdoc::p
    "Where we intentionally write @('FILE'),
     without double quotes or angle brackets, and without extensions,
     because those details do not matter here.")
   (xdoc::p
    "Since @('#include') is substitution in place,
     it is possible for @('FILE') to reference @('M').
     This means that @('FILE') could give a different result
     when preprocessed stand-alone vs. when processed within the including file.
     Indeed, the result of preprocessing @('#include FILE')
     depends on where that directive occurs;
     different occurrences may result in
     possibly very different replacements,
     e.g. if @('M') affects conditional inclusion [C17:6.10.1].")
   (xdoc::p
    "However, the situation above is not a common case.
     In particular, if @('FILE') is part of a library,
     it would not even know about @('M').
     Thus, the result of preprocessing @('FILE')
     should be normally independent from where it occurs,
     and should always result in the same replacement
     (but we discuss include guards below).
     In this case, we can avoid expanding the @('#include'),
     and separately preprocess @('FILE'),
     leaving the @('#include') as a reference to @('FILE');
     multiple @('#include')s of @('FILE') may reference the same @('FILE').")
   (xdoc::p
    "In such common cases,
     our preprocessor avoids expanding the inclusion in place,
     and instead adds the result of preprocessing @('FILE')
     to the file set returned as result of preprocessing a given list of files
     (see @(see preprocessor)).
     This is why, in addition to one element for each specified file,
     our preprocessor also returns zero or more additional elements,
     in the file set resulting from the preprocessor.")
   (xdoc::p
    "When we encounter a @('#include') directive,
     we find the file and we preprocess in the context of the including file,
     i.e. using the current macro table.
     Then, to see whether we can avoid expanding its @('#include'),
     we re-process the included file in a fresh context,
     i.e. in a macro table that only has the predefined macros.
     If we get the same results on the included file,
     we leave the @('#include') in place;
     otherwise, we expand it into the included file's content
     (the content generated when preprocessing the file
     in the context of the included file).")
   (xdoc::p
    "Whenever we re-process a file without non-predefined macros as above,
     we add the results to an alist (called @('preprocessed') in our code).
     Thus, if later we encounter another @('#include') for the same file,
     we do not need to re-process it afresh,
     but we can just obtain the result from the alist,
     and compare it with the result of preprocessing the included file
     in the context of the including file.
     So, depending on context,
     a @('#include') of a file may be preserved in one place,
     but it may be expanded in another place,
     although we expect that this should not happen in well-structured code.
     Indeed, one could force the expansion in place even of a library file,
     simply by preceding the @('#include') with a @('#define')
     that defines some identifier that occurs in the library file:
     this is contrived, and may rarely lead to compilable code,
     but it is perfectly possible as far as preprocessing is concerned.")
   (xdoc::p
    "Every @('#include') of the same file needs to be preprocessed
     in the context of the including file, at that place of the including file.
     This is because potentially any identifier that occurs in the included file
     could have or not have a macro definition at that point.")
   (xdoc::p
    "Header guards deserve some special consideration.
     Header guards are a well-known approach
     to avoid including the same file multiple times.
     The files to include have a form like")
   (xdoc::codeblock
    "+-F.h-----------+"
    "| #ifndef F     |"
    "| #define F     |"
    "| ...F stuff... |"
    "| #endif        |"
    "+---------------+")
   (xdoc::p
    "Consider additional files of the form")
   (xdoc::codeblock
    "+-G.h-----------+"
    "| #ifndef G     |"
    "| #define G     |"
    "| #include F.h  |"
    "| ...G stuff... |"
    "| #endif        |"
    "+---------------+")
   (xdoc::p
    "and")
   (xdoc::codeblock
    "+-A.c-----------+"
    "| #include F.h  |"
    "| #include G.h  |"
    "| ...A stuff... |"
    "+---------------+")
   (xdoc::p
    "where we intentionally omit
     angle brackes and double quotes from the @('#include')s
     because they are not relevant here.")
   (xdoc::p
    "We start preprocessing @('A.c').
     The @('#include F.h') can be preserved,
     because @('A.c') defines no macros before including @('F.h').
     We get the same result for @('F.h')
     whether we preprocess it from @('A.c') or stand-alone:")
   (xdoc::codeblock
    "+-F.h preprocessed from G.h----+"
    "| ...F stuff preprocessed...   |"
    "+------------------------------+"
    ""
    "+-F.h preprocessed stand-alone-+"
    "| ...F stuff preprocessed...   |"
    "+------------------------------+")
   (xdoc::p
    "As we move to the @('#include G.h'),
     we preprocess @('G.h') in the context from @('A.c'),
     which in particular has a definition for @('F'),
     coming from the included @('A.h').
     Thus, when we encounter the @('#include F.h') in @('G.h'),
     and we preprocess @('F.h') in that context,
     the result of preprocessing @('F.h') would be empty (i.e. no tokens):")
   (xdoc::codeblock
    "+-F.h preprocessed from G.h from A.c-+"
    "|                                    |"
    "+------------------------------------+")
   (xdoc::p
    "This differs from @('F.h') preprocessed stand-alone (see above),
     and so we need to expand the @('#include F.h') in @('G.h'),
     which amounts to removing the @('#include F.h') from @('g.h'):")
   (xdoc::codeblock
    "+-G.h preprocessed from A.c--+"
    "| ...G stuff preprocessed... |"
    "+----------------------------+")
   (xdoc::p
    "This is not bad so far,
     but after we finish preprocessing @('G.h')
     in the context of the including @('A.c'),
     in order to decide whether we can preserve the @('#include G.h'),
     we re-process @('G.h') with only the predefined macros,
     and in particular without @('F') being defined, obtaining:")
   (xdoc::codeblock
    "+-G.h preprocessed stand-alone-+"
    "| #include F.h                 |"
    "| ...G stuff preprocessed...   |"
    "+------------------------------+")
   (xdoc::p
    "Since the two results of preprocessing @('G.h') differ
     (even assuming the the preprocessed @('G') stuff is the same),
     we need to expand the @('#include G.h') in place, obtaining:")
   (xdoc::codeblock
    "+-A.c preprocessed-----------+"
    "| #include F.h               |"
    "| ...G stuff preprocessed... |"
    "| ...A stuff preprocessed... |"
    "+----------------------------+")
   (xdoc::p
    "This is correct, but unfortunate.
     The only difference in the two preprocessing results of @('G.h')
     is the presence vs. absence of @('#include F.h').
     However, in the result where it is missing,
     it would be harmless to leave,
     because, in that context, @('F') is defined,
     and thus @('#include F.h') would expand to nothing anyways.
     The file inclusion pattern above is very common,
     e.g. when @('F.h') and @('G.h') are library headers.")
   (xdoc::p
    "Thus, we treat files with header guards specially.
     First, when we preprocess a file, we recognize whether
     it has the header guard form, i.e. the form of @('F.h') and @('G.h') above.
     Currently we only accept exactly the form with @('#ifndef ...'),
     and not the equivalent @('#if !defined(...)'),
     but we plan to extend this.
     Thus, when an included file has the header guard form
     and its header guard symbol is defined,
     we leave its @('#include') in place:")
   (xdoc::codeblock
    "+-G.h preprocessed from A.c--+"
    "| #include F.h               |"
    "| ...G stuff preprocessed... |"
    "+----------------------------+")
   (xdoc::p
    "This is now the same result as when preprocessing @('G.h') stand-alone,
     and thus we can preserve @('#include G.h') in @('A.c'):")
   (xdoc::codeblock
    "+-A.c preprocessed-----------+"
    "| #include F.h               |"
    "| #include G.h               |"
    "| ...A stuff preprocessed... |"
    "+----------------------------+")
   (xdoc::p
    "However, if we leave the @('#include F.h') in @('G.h'),
     we need to retain somehow the information about the fact that
     @('F.h') should not duplicated.
     If we were to fully preprocess the resulting files,
     expanding all @('#include')s,
     we would get two copies of the @('F') stuff in @('A.c').
     Thus, we also need to preserve
     the @('#ifndef') and @('#define') directives for the header guards:")
   (xdoc::codeblock
    "+-F.h preprocessed-----------+"
    "| #ifndef F                  |"
    "| #define F                  |"
    "| ...F stuff preprocessed... |"
    "| #endif                     |"
    "+----------------------------+"
    ""
    "+-G.h preprocessed-------------+"
    "| #ifndef G                    |"
    "| #define G                    |"
    "| #include F.h                 |"
    "| ...G stuff preprocessed...   |"
    "| #endif                     |"
    "+------------------------------+"
    ""
    "+-A.c preprocessed-----------+"
    "| #include F.h               |"
    "| ...G stuff preprocessed... |"
    "| ...A stuff preprocessed... |"
    "+----------------------------+")
   (xdoc::p
    "This way, we preserve the information about
     conditional inclusion with respect to the header guard symbols,
     and their definitions.")
   (xdoc::p
    "In fact, nothing prevents the presence of @('#define')s
     for the header guards outside the normal place,
     i.e. not just after the @('#ifndef'),
     but instead in any random place;
     as well as the presence of random @('#undef')s for the same symbols.
     This should only occur in contrived code,
     but we need to handle things correctly in all possible cases.
     Thus, in general we need to preserve information about
     all the @('#define')s and @('#undef')s that may affect header guards.
     We are not quite doing that yet, but we plan to.
     We also need to extend our ASTs and @(see parser)
     to accept these additional directives
     (currently they only accept @('#include')s at the start of a file.")))
