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

  xdoc-to-static-html.xsl
  Converts xdoc markup to static html pages

  Most of the work is done in xdoc-to-html-aux.xsl, which is shared between
  this file and xdoc-to-dynamic-html.xsl.  The only difference between the 
  static and dynamic versions is the file extension, e.g., .xml versus .html,
  which is needed for links.

-->

<xsl:include href="xdoc-to-html-aux.xsl"/>

<xsl:template match="parent">
  <p>Parent: <a href="{@topic}.html">
    <xsl:value-of select="."/>
  </a></p>
</xsl:template>

<xsl:template match="see">
  <a href="{@topic}.html">
    <xsl:value-of select="."/>
  </a>
</xsl:template>

<xsl:template match="hindex">
  <li><nobr><xsl:choose>
	<xsl:when test="@kind='leaf'">
           <img src="leaf.png"/>
        </xsl:when>

        <xsl:when test="@kind='show'">
           <a href="JavaScript:toggleVisible('{@id}')">
             <img id="img-{@id}" src="minus.png" border="0"/>
           </a>
        </xsl:when>

        <xsl:when test="@kind='hide'">
           <a href="JavaScript:toggleVisible('{@id}')">
             <img id="img-{@id}" src="plus.png" border="0"/>
           </a>
	</xsl:when>
      </xsl:choose>
      <a href="{@topic}.html" title="{hindex_short}">
	<xsl:value-of select="hindex_name"/>
     </a></nobr>
    <xsl:apply-templates/>
  </li>
</xsl:template>

</xsl:stylesheet>
