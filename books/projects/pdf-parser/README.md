# PDF Parser

As part of DARPA SafeDocs, we built an alternate version of a ABNF PDF parser. This parser serves as a proof-of-concept of a parser combinator library implemented in ACL2. Instead of automatic generation of parsers, this PDF parser is built bottom-up from parser primitives, and then combined with repetition, choice, and sequence operators to form the full PDF parser. This parser assumes newlines and spacing which may not exist in all PDF documents. We include an example hello.pdf from https://blog.idrsolutions.com/make-your-own-pdf-file-part-4-hello-world-pdf/ is of a size that ACL2 can handle and will parse correctly. 

In order for functions to be combinable, all parsing functions take in the same inputs and generate the same outputs. Inputs must be a character list, and outputs are a cons of an ast-obj containing the parse results, and a character list of the remainder of the list. To parse a string, it is necessarly to convert it into a character list with the 'explode' function. AST-objs have 2 parameters, a string 'type', and an object (any) value. 

Each parsing function takes in optional arguments, and the character-list 'contents'. The parsing function either returns the parse result and remainder if the parse succeeded, or (ast-obj "null" "") and the original contents if the parse could not be performed.

## Primitive Parsing functions

|     Function                            |     Description                                                                                             |     Arguments           |     Parsed AST-OBJ type                                         |
|-----------------------------------------|-------------------------------------------------------------------------------------------------------------|-------------------------|-----------------------------------------------------------------|
|     Parse-string                        |     Parses the given string from the start of the list                                                      |     String, Contents    |     “string” <string>                                           |
|     Parse-string-from-end               |     Parses the last instance of the given string                                                            |     String, Contents    |     “string” <string>                                           |
|     Parse-n-chars                       |     Parses n characters (if available)                                                                      |     N (natural), Contents         |     “charlist” <character-list>                                 |
|     Parse-char                          |     Parses the given character from the start of the list                                                   |     Char, Contents      |     “char” <character>                                          |
|     Parse-until-string                  |     Parse all characters until the string is reached,   returning the ast-obj up the the end of string      |     String, Contents    |     “before-string” <preceding chars including string>          |
|     Parse-until-string-non-inclusive    |     Same as parse-until-string, but returns the ast-obj of the   preceding characters                       |     String Contents     |     “before-string” <preceding chars not including   string>    |
|     Parse-number                        |     Parse until first non-digit, and return the contents as a   number                                      |     Contents            |     “number” <number>                                           |
|     Parse-word                          |     Same as parse-until-string “ “                                                                          |     Contents            |     (ast-obj “word” <output>)                                   |


## Composite functions

As ACL2 cannot take functions as arguments, we cannot create composite functions by passing in base functions as arguments. Instead, we build template composite functions, which can be filled in systematically to generate these composite functions.



|     Function                        |     Description                                                                                              |     AST Output                                                                     |   |
|-------------------------------------|--------------------------------------------------------------------------------------------------------------|------------------------------------------------------------------------------------|---|
|     Parse-<func1>-<func2>-option    |     Attempts   to parse with both func1 and func2, with priority for whichever returns a   shorter result    |     Output of   either func1 or func2, or (ast-obj “null”) if neither can parse    |   |
|     Parse-<func>-optional           |     Try to   parse with func, but don’t return null if it fails                                              |     Output of   func if parsing succeeds, otherwise (ast-obj “optional”)           |   |
|     Parse-<func>-repetition         |     Parse   with func until no longer possible                                                               |     (ast-obj “sequence”   (list <parse-results>)                                   |   |
|     Parse-sequence-<funccnames>     |     Parse   first function, pass result to second function, etc                                              |     (ast-obj   “sequence“ <list of ast-objs)                                       |   |

For faster admission into ACL2, we use guard-hints to not expand any sub-functions, which we already have verified.

## PDF Parser Walkthrough

This section walks through the code in pdf-parser.lisp, explaining how this PDF parser is generated. The code parses a non-linearizd PDF, with the sections 'header', 'objects', 'xref', and 'trailer'. 

### Helper functions

- ast-obj type definition
- ast-obj-null: checks if a parse result is null, or that the parse failed. This function will be used for parser theorems. 
- combine2-ast-objs: Given 2 ast-objs, generates a composite ast-obj of type "sequence", with the value as a list with both ast-obj values
- index-of-subseq: Given a list and object, returns the index of the list of that object's starting position, or NIL if not present
- index-of-subseq-from-end: Same as index-of-subseq, but searches from the end instead
- digit-charlist-p: Given character list, checks if all the characters are digits
- convert-charlist-to-natural: Given a character list (which must be a list of digits), convert it into a single natural. For example, (list '1' '2') is converted to '12'. 
- index-of-first-non-digit: Given a character list, finds the index of the first non-digit. This 

### Base Parsing Functions

Functions as listed in the table above, along with associated theorems for each that:
- The output is a cons
- The first element of the output is an ast-obj
- The second element of the ouput is a character list

### Composite Parsing Functions

This sections contains the composite functions used to generate the PDF parser from the base functions, from the bottom up, defining each of the different PDF sections: header, objects, xref table, and trailer.

The header grammar is: "%PDF-" number "." number Newline. 

Looking at the function 'parse-header', we can see how the sequence of terms is parsed. We use the 'let' operator to parse individual terms step-by-step, first saving the result of parsing the string "%PDF-" in res1, next parsing a number from the 2nd element of res1, the remaining character list, etc. The ast-obj elements of each parse result are then concatenated together with the helper function 'combine2-ast-objs', where ast1 is the combination of the ast-obj components of res1 and res2, etc. If any of the intermediate parsing functions fail, detected as any of the ast-objs are of type null, then the final parse result is an ast-obj of type null.

The xref table consists of the xref header, of the format: "xref" Newline "0" Space Number Newline, where the number indicates the number of xref entries, followed by xref entries of the format: Number Space Number Space choice("n", "f") Newline

The objects consist of individual object entries, defined as: Number Space Number Space "obj" Newline
... character contents .... "endobj"

There are optional Newline and Space characters after "obj". This definition is a simplification of the PDF object definition, as it doesn't parse the dictionary, stream object, etc. 

Finally, the trailer is defined as: "trailer" Space trailer-dictionary "startxref" Newline Number Newline "%%EOF".  

After defining each of the parser funcions for these sections, the final PDF parser is defined simply as a sequence of the individual section parser functions. It is possible to test this function, parse-pdf by reading the contents of a file, with "(parse-pdf (explode  (read-file-into-string "hello.pdf")))" 