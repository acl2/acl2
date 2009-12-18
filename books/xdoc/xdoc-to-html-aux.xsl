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

  
  xdoc-to-html-aux.xsl
  Main transformations to convert XDOC to HTML

-->

<xsl:template match="page">
  <html>
  <head>
    <title><xsl:value-of select="@name"/></title>
    <link rel="stylesheet" type="text/css" href="xdoc.css"/>
    <script type="text/javascript" src="xdoc.js"/>
  </head>
  <body class="body_normal">
  <xsl:apply-templates/>
  </body>
  </html>
</xsl:template>

<xsl:template match="index">
  <h1>Index</h1>
  <dl class="index_dl">
  <xsl:for-each select="index_entry">
    <xsl:sort select="head/see" />
    <dt class="index_dt"><xsl:apply-templates select="index_head"/></dt>
    <dd class="index_dd"><xsl:apply-templates select="index_body"/></dd>
  </xsl:for-each>
  </dl>
</xsl:template>

<xsl:template match="topic">
  <h1><xsl:value-of select="@name"/></h1>
  <xsl:apply-templates/>
</xsl:template>

<xsl:template match="hindex_root">
  <ul class="hindex"><xsl:apply-templates/></ul>
</xsl:template>

<xsl:template match="hindex_children">
  <xsl:choose>
    <xsl:when test="@kind='hide'">
	<ul class="hindex" id="{@id}" style="display: none">
	<xsl:apply-templates/>
	</ul>
    </xsl:when>

    <xsl:otherwise>
	<ul class="hindex" id="{@id}">
	<xsl:apply-templates/>
	</ul>
    </xsl:otherwise>
  </xsl:choose>
</xsl:template>

<xsl:template match="hindex_short">
</xsl:template>

<xsl:template match="hindex_name">
</xsl:template>

<xsl:template match="short">
  <p><xsl:apply-templates/></p>
</xsl:template>

<xsl:template match="srclink">
  <a href="{@file}" class="srclink" title="Find-Tag in Emacs">
    <xsl:apply-templates/>
  </a>
</xsl:template>

<xsl:template match="code">
  <pre class="code"><xsl:apply-templates/></pre>
</xsl:template>

<xsl:template match="box">
  <div class="box"><xsl:apply-templates/></div>
</xsl:template>

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
