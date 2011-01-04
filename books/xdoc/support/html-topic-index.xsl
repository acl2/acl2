<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

<!--

; XDOC Documentation System for ACL2
; Copyright (C) 2009-2010 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

  html-topic-index.xsl

  This generates the hierarchical topic-navigator for both the two-frame and
  three-frame html versions.

-->

<xsl:include href="html-topic.xsl"/>

<xsl:template match="page">
  <html>
  <head>
    <title><xsl:value-of select="@name"/></title>
    <link rel="stylesheet" type="text/css" href="xdoc.css"/>
    <script type="text/javascript" src="xdoc.js"/>
    <base target="detail"/>
  </head>
  <body class="body_brief">
<!--   <h4>Organized Listing</h4> -->
  <dl class="index_brief">
  <dt class="index_brief_dt"><a href="full-index.html">Full Index</a></dt>
  </dl>
  <div class="hindex_fix">
  <xsl:apply-templates/>
  </div>
  </body>
  </html>
</xsl:template>

</xsl:stylesheet>
