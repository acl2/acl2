#!/bin/bash

set -e

rm -f *.cert

A0="" A1="" cert.pl test2

rm *.cert

A0=1 A1="" cert.pl test2

rm *.cert

A0="" A1=1 cert.pl test2

rm *.cert

A0=1 A1=1 cert.pl test2

rm *.cert


