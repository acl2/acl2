/*
; XDOC Documentation System for ACL2
; Copyright (C) 2009-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>
*/

// XDOC Configuration
//
// Most users should not edit this file.


// XDATAGET -- You only need to change this if you are going to load your data
// on the fly via ajax queries and xdataget.pl.  In this case, you need to:
//
//   (1) Build the sqlite database using xdata2sql.pl
//   (2) Install xdata.db and xdataget.pl somewhere on your web server
//   (3) Point this at your xdataget.pl script.
//
// Example Syntax:
// var XDATAGET = "http://my-server/cgi-bin/my-manual/xdataget.pl";

var XDATAGET = "";

// XDOCTITLE -- You only need to change this if you want to customize the title
// that your web pages will display as.  By default pages will be shown as, e.g.,
//
//    XDOC --- Top
//    XDOC --- Arithmetic
//    XDOC --- Ihs
//
// And so forth.  You can replace the "XDOC" part of this by configuring this
// variable.  For example, writing:
//
//   var XDOCTITLE = "ACL2+Books Manual";
//
// Will result in page titles such as:
//
//   ACL2+Books Manual --- Top
//   ACL2+Books Manual --- Arithmetic
//   ACL2+Books Manual --- Ihs
//
// And so forth.  You could of course provide some alternate description for
// internal manuals at organizations, e.g., "Centaur FV Manual" or whatever.

var XDOCTITLE = "XDOC";
