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
     (but we discuss header guards below).
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
     A file with a header guard has a form like")
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
    "+-F.h preprocessed from A.c----+"
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
     which amounts to removing the @('#include F.h') from @('G.h'):")
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
    "The header guard form shown above is not the only possible one.
     An equivalent form (perhaps legacy) is")
   (xdoc::codeblock
    "+-F.h-------------+"
    "| #if !defined(F) |"
    "| #define F       |"
    "| ...F stuff...   |"
    "| #endif          |"
    "+-----------------+")
   (xdoc::p
    "or also (although contrived)")
   (xdoc::codeblock
    "+-F.h-----------+"
    "| #ifdef F      |"
    "| #else         |"
    "| #define F     |"
    "| ...F stuff... |"
    "| #endif        |"
    "+---------------+")
   (xdoc::p
    "and so on.
     Instead of attempting to recognize all the possible various forms,
     we use a more general mechanism,
     which applies to all conditional sections
     (i.e. the constructs captured by @('if-section') in the ABNF grammar).")
   (xdoc::p
    "When we preprocess a conditional section,
     as in any other C preprocessor,
     we need to find which branch is selected,
     i.e. its condition is true and no previous condition is true.
     Our preprocessor preserves the scaffolding of the conditional section,
     namely its @('#if'), @('#ifdef'), @('#ifndef'),
     @('#elif'), @('#else'), and @('#endif') directives,
     but only keeps the code in the selected branch,
     leaving all the other branches empty
     (in fact, this code is skipped as described in [C17:6.10.1/6]).
     Thus, the result of our preprocessing a conditional section
     is a conditional section with at most one branch non-empty.
     This applies to nested conditional sections as well.")
   (xdoc::p
    "The branch selected in a conditional varies with on the current macros.
     Preprocessing the same file in different contexts
     may select different branches.
     For instance, consider the first example @('F.h') above,
     the one that starts with @('#ifndef'),
     and the additional example files @('G.h') and @('A.c') above.
     The result of preprocessing @('F.h'), stand-alone or from @('A.c'),
     is the same in both case, i.e. the following:")
   (xdoc::codeblock
    "+-F.h preprocessed stand-alone-+"
    "| #ifndef F                    |"
    "| #define F                    |"
    "| ...F stuff preprocessed...   |"
    "| #endif                       |"
    "+------------------------------+"
    ""
    "+-F.h preprocessed from A.c----+"
    "| #ifndef F                    |"
    "| #define F                    |"
    "| ...F stuff preprocessed...   |"
    "| #endif                       |"
    "+------------------------------+")
   (xdoc::p
    "The scaffolding is preserved,
     and since @('F') is not defined when @('F.h') is preprocessed
     stand-alone or from @('A.c'),
     the (only branch) is selected, and its code is kept.")
   (xdoc::p
    "When instead we preprocess @('F.h') from @('G.h') from @('A.c'),
     the macro @('F') is defined, and thus no branch in @('F.h') is selected,
     producing the following result:")
   (xdoc::codeblock
    "+-F.h preprocessed from G.h from A.c-+"
    "| #ifndef F                          |"
    "| #endif                             |"
    "+------------------------------------+")
   (xdoc::p
    "In this case, the (only) branch is not selected, and thus it is empty.")
   (xdoc::p
    "Although this differs from the result when @('F') is defined,
     the two results do not differ
     if we take into account the definedness of @('F').
     The two results have identical scaffoldings,
     and, under the assumption of @('F') being defined,
     they are actually equivalent.
     Thus, we can preserve the @('#include F.h') in @('G.h')
     when the latter is preprocessed from @('A.c'):")
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
    "The mechanism works not only for scaffolding of the form in @('F.h') above,
     but in general for any kind of conditional section.")
   (xdoc::p
    "The preservation of the conditional section scaffolding
     is critical to this mechanism.
     Without it, if we were to fully preprocess
     the files resulting from our preserving preprocessing,
     expanding all @('#include')s,
     we would get two copies of the @('F') stuff in @('A.c').")
   (xdoc::p
    "It is also critical to preserve information about
     the definedness status of macros, which affects whether
     the code in a conditional branch of an included file
     is actually retained in the including file.
     This is the case not just for @('#ifdef') and @('#ifndef'),
     but also for the expressions in @('#if') and @('#elif').
     These expressions consist of some constants, some regular operators,
     and the preprocessor-specifie operator @('defined').
     The latter is the only one that can in fact vary,
     in the expressions of the conditional scaffoldings.")
   (xdoc::p
    "We preserve @('#undef') directives as they are.
     But preserving @('#define') directives as they are can cause problems.
     For example, in the code fragment")
   (xdoc::codeblock
    "#define x -x"
    "int y = x;")
   (xdoc::p
    "leaving the @('#define') as is after preprocessing the rest would yield")
   (xdoc::codeblock
    "#define x -x"
    "int y = -x;")
   (xdoc::p
    "where the @('x') in the initializer of @('y')
     has been appropriately replaced with @('-x'),
     with the @('x') in @('-x') not further replaced
     thanks to the preprocessor mechanism to prevent recursion.
     But if we were now to fully preprocess the resulting code,
     we would obtain")
   (xdoc::codeblock
    "int y = - -x;")
   (xdoc::p
    "which is different from the code that we would obtain
     by fully preprocessing the original code, i.e.")
   (xdoc::codeblock
    "int y = -x;")
   (xdoc::p
    "This violates the correctness criterion outlined in @(tsee preprocessor)
     for the preservation of preprocessing constructs.")
   (xdoc::p
    "One can imagine more complicated examples, with indirect recursion.
     The point is that, in general, leaving a @('#define') as is,
     after preprocessing subsequent code and already performing replacements,
     can lead to unwanted further replacements.")
   (xdoc::p
    "Given that the @('defined') operator
     only cares about whether a symbol is defined,
     but not its particular definition,
     we preserve @('#define') directive in modified form,
     namely by defining the symbol to be itself, e.g.")
   (xdoc::codeblock
    "#define x x")
   (xdoc::p
    "This way, any further replacement would be a no-op,
     but the definedness or not of the symbol is preserved.")
   (xdoc::p
    "In fact, in the example @('F.h') above,
     the actual form of the result of preprocessing that file is:")
   (xdoc::codeblock
    "+-F.h preprocessed-----------+"
    "| #ifndef F                  |"
    "| #define F F                |"
    "| ...F stuff preprocessed... |"
    "| #endif                     |"
    "+----------------------------+")))
