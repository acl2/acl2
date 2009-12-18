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

  
  xdoc-to-full-index.xsl
  Generate the annotated index page.

-->

<xsl:include href="xdoc-to-static-html.xsl"/>

<xsl:template match="index">
  <h1>Full Index</h1>
  <dl class="index_dl">
  <xsl:for-each select="index_entry">
    <xsl:sort select="index_head/see" />
    <dt class="index_dt"><xsl:apply-templates select="index_head"/></dt>
    <dd class="index_dd"><xsl:apply-templates select="index_body"/></dd>
  </xsl:for-each>
  </dl>
</xsl:template>

</xsl:stylesheet>
