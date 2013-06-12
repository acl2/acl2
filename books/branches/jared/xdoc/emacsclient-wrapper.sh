#!/bin/sh

# This is a simple wrapper that can be used to launch emacsclient with 
# additional options.  A script like this may be useful for connecting
# your web browser to emacs for .xdoc-link files.

emacsclient --no-wait "$1"
