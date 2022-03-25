# Syntheto

This directory contains an ACL2 library for Syntheto.

Syntheto is a surface language for ACL2 and APT,
aimed at a wider range of users than typical ACL2 and APT experts.

Our implementation of Syntheto consists of a front-end and a back-end.
This directory contains the back-end (i.e. the ACL2 library for Syntheto),
while the front-end is in a
[separate repository](https://github.com/kestrelinstitute/syntheto-frontend).

The Syntheto back-end
takes Syntheto abstract syntax from the front-end,
produces ACL2 events,
and reports success or failure with explanation back to the front-end.
Syntheto transformations are implemented as one or more APT transformations;
the resulting functions are translated back into Syntheto abstract syntax
for the front-end to display.
