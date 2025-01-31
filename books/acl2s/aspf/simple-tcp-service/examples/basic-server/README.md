# Example server

This directory contains an example service handler plus some Python
code that interfaces with it.

To provide more functionality, one can modify the `handle-request`
function in `handler.lsp` and add additional cases. This file will be
interpreted in Common Lisp rather than ACL2's `ld`.

## Building

Before running the demo, one should build the image for the ACL2 side
of the demo. This can be done by running `make` in this directory,
assuming that one has defined the `ACL2_SYSTEM_BOOKS` environment
variable to point to the `books` directory of the ACL2 repo, and one
has built an ACL2 image.

## Running

To run the demo, run `python demo.py` in this directory. It should
print something of the form:

```
('OK', 'Echo!')
('OK', 'HVnlX')
```

where the second line may have a different value for the second tuple
element.
