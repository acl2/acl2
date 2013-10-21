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

  html-topic.xsl

  Converts an xdoc topic page to a static html page.  This is basically
  html-core.xsl, with .html file extensions on <see> links.

-->

<xsl:include href="html-core.xsl"/>

<xsl:template match="parent">
  <p>Parent: <a href="{@topic}.html">
    <xsl:value-of select="."/>
  </a></p>
</xsl:template>

<xsl:template match="see">
  <a href="{@topic}.html">
    <xsl:apply-templates/>
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
