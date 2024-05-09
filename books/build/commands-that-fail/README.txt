This directory contains tools that intentionally fail and that
override the real tools with the same names.  This can be used to test
that tools that should not run during a build are never actually
invoked.

For example, say you have glucose installed but want to ensure that
the ACL2 books build on a machine without glucose (that is, you want
to ensure that all books that depend on glucose are tagged as such
with the appropriate cert_param).  You can simulate not having glucose
by including this directory at the start of your path.
