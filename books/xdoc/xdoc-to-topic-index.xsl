<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

<!-- 

XDOC Documentation System for ACL2
Copyright (C) 2009 Centaur Technology

This program is free software; you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free Software
Foundation; either version 2 of the License, or (at your option) any later
version.  This program is distributed in the hope that it will be useful but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
details.  You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software Foundation, Inc.,
59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

  
  xdoc-to-topic-index.xsl
  Generate an index page with topic listings

-->

<xsl:include href="xdoc-to-static-html.xsl"/>

<xsl:template match="page">
  <html>
  <head>
    <title><xsl:value-of select="@name"/></title>
    <link rel="stylesheet" type="text/css" href="xdoc.css"/>
    <script type="text/javascript" src="xdoc.js"/>
    <base target="detail"/>
  </head>
  <body class="body_brief">
  <h4>Organized Listing</h4>
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
