<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="2.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

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

-->

<xsl:template match="topic">
  <html>
  <head>
    <title><xsl:value-of select="@name"/></title>
    <link rel="stylesheet" type="text/css" href="xdoc.css"/>
  </head>
  <body>
  <h1><xsl:value-of select="@name"/></h1>
  <xsl:apply-templates/>
  </body>
  </html>
</xsl:template>

<xsl:template match="parent">
  <p>Parent: <a href="{@topic}">
    <xsl:value-of select="."/>
  </a></p>
</xsl:template>


<xsl:template match="see">
  <a href="{@topic}">
    <xsl:value-of select="."/>
  </a>
</xsl:template>

<xsl:template match="code">
  <pre class="code"><xsl:apply-templates/></pre>
</xsl:template>

<xsl:template match="box">
  <div class="box"><xsl:apply-templates/></div>
</xsl:template>


<!-- Support for various XHTML tags.  We just let you use things like 
  <b>, <ul>, <p>, etc., verbatim. -->

<xsl:template match="p">
  <p><xsl:apply-templates/></p>
</xsl:template>

<xsl:template match="a">
  <a href="{@href}">
    <xsl:value-of select="."/>
  </a>
</xsl:template>

<xsl:template match="b">
  <b><xsl:apply-templates/></b>
</xsl:template>

<xsl:template match="i">
  <i><xsl:apply-templates/></i>
</xsl:template>

<xsl:template match="color">
  <font color="{@rgb}"><xsl:apply-templates/></font>
</xsl:template>

<xsl:template match="sf">
  <span class="sf"><xsl:apply-templates/></span>
</xsl:template>

<xsl:template match="u">
  <u><xsl:apply-templates/></u>
</xsl:template>

<xsl:template match="tt">
  <tt><xsl:apply-templates/></tt>
</xsl:template>

<xsl:template match="ul">
  <ul><xsl:apply-templates/></ul>
</xsl:template>

<xsl:template match="ol">
  <ol><xsl:apply-templates/></ol>
</xsl:template>

<xsl:template match="li">
  <li><xsl:apply-templates/></li>
</xsl:template>

<xsl:template match="dl">
  <dl><xsl:apply-templates/></dl>
</xsl:template>

<xsl:template match="dt">
  <dt><xsl:apply-templates/></dt>
</xsl:template>

<xsl:template match="dd">
  <dd><xsl:apply-templates/></dd>
</xsl:template>

<xsl:template match="h1">
  <h1><xsl:apply-templates/></h1>
</xsl:template>

<xsl:template match="h2">
  <h2><xsl:apply-templates/></h2>
</xsl:template>

<xsl:template match="h3">
  <h3><xsl:apply-templates/></h3>
</xsl:template>

<xsl:template match="h4">
  <h4><xsl:apply-templates/></h4>
</xsl:template>

<xsl:template match="h5">
  <h5><xsl:apply-templates/></h5>
</xsl:template>

</xsl:stylesheet>
