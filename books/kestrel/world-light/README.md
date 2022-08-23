Some lightweight utilities for querying the world.

Design goals:
- lightweight
- preconditions expressed as guards (e.g., fn-logicp requires argument to be a function symbol)
- attempt to always get the right answer (subject to the guard), regardless of oddities

For a symbol SYM:
(function-symbolp SYM wrld) - Check whether SYM is a function (this is built-in)

For a function symbol, FN:
(fn-logicp fn wrld) - Check whether FN is in :logic mode
(fn-programp fn wrld) - Check whether FN is in :programp mode
(fn-definedp fn wrld) - Check whether FN is defined (has a body)

For a symbol SYM:
(defined-functionp SYM WRLD) - Check whether SYM is a function and is defined

Related functions:
(logicp fn wrld) - check whether FN is in :logic mode (built-in, weaker guard)
