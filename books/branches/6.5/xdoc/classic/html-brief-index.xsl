<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

<!--

; XDOC Documentation System for ACL2
; Copyright (C) 2009-2011 Centaur Technology
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

  html-brief-index.xsl

  Provides a compact view of the index for the three-frame html display.  You
  can compare/contrast with html-full-index.xsl which generates the more
  elaborate index.

-->

<xsl:include href="html-topic.xsl"/>

<xsl:template match="page">
  <html>
  <head>
    <title><xsl:value-of select="@name"/></title>
    <link rel="stylesheet" type="text/css" href="xdoc.css"/>
    <base target="detail"/>
  </head>
  <body class="body_brief">
<!--   <h4>Alphabetic Listing</h4> -->
  <xsl:apply-templates/>
  </body>
  </html>
</xsl:template>

<xsl:template match="index">
  <dl class="index_brief">
  <dt class="index_brief_dt"><a href="full-index.html">Full Index</a></dt>
  </dl>
  <dl class="index_brief">
  <xsl:for-each select="index_entry">
    <xsl:sort select="index_head/see" />
    <dt class="index_brief_dt"><xsl:apply-templates select="index_head"/></dt>
  </xsl:for-each>
  </dl>
</xsl:template>

</xsl:stylesheet>
