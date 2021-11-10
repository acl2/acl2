# Syntheto

The Syntheto language is a front-end language for ACL2 and APT,
aimed at a wider range of users than typical ACL2 and APT experts.

This directory contains an ACL2 library for Syntheto.
The syntheto front-end is in the process of being open-sourced.

This back-end takes syntheto abstract syntax from the front-end and produces ACL2
events, and reports success or failure with explanation back to the front-end.
Syntheto transformations are implemented as one or more APT transformations and
resulting functions are translated back into syntheto abstract syntax for the 
front-end to display.
