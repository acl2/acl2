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

  xdoc-to-text.xsl
  Converts xdoc markup to plain text

  [Jared 10/21/09]:  I haven't put too much work into this.  Doing fancy
  things with XSLT seems rather difficult and I am not an expert.

     The main deficiency right now is that I do not know how to make links
  stand out. My word-wrapping code is copied from some web site, and to use it
  I seem to have to treat the contents of elements such as <p> and <li> as
  ordinary text.  This means that templates for <a> and <see> are never
  processed.  Maybe someone who knows XSLT will be able to provide a fix.

-->

<xsl:output method="text"/>
<xsl:strip-space elements="box ul ol dl p topic"/>

<xsl:template match="topic">
  <xsl:text>------------------------------------------------------------------------&#xA;&#xA;</xsl:text>
  <xsl:text>     </xsl:text>
  <xsl:value-of select="@name"/>
  <xsl:text>&#xA;&#xA;</xsl:text>
  <xsl:text>------------------------------------------------------------------------&#xA;&#xA;</xsl:text>
  <xsl:apply-templates/>
  <xsl:text>&#xA;------------------------------------------------------------------------&#xA;</xsl:text>
</xsl:template>

<xsl:template match="parent">
  <xsl:text>Parent Topic: </xsl:text>
  <xsl:value-of select="."/>
  <xsl:text> (</xsl:text>
  <xsl:value-of select="@topic"/>
  <xsl:text>)&#xA;&#xA;</xsl:text>
</xsl:template>

<xsl:template match="p">
  <!-- Word wrap paragraphs. -->
  <xsl:call-template name="wrap-string">
   <xsl:with-param name="str" select="normalize-space(.)"/>
   <xsl:with-param name="wrap-col" select="65"/>
   <xsl:with-param name="break-mark" select="'&#xA;'"/>
  </xsl:call-template>
  <xsl:text>&#xA;&#xA;</xsl:text>
</xsl:template>

<xsl:template match="ul">
  <xsl:apply-templates/>
  <xsl:text>&#xA;</xsl:text>
</xsl:template>

<xsl:template match="ol">
  <xsl:apply-templates/>
  <xsl:text>&#xA;</xsl:text>
</xsl:template>

<xsl:template match="dl">
  <xsl:apply-templates/>
  <xsl:text>&#xA;</xsl:text>
</xsl:template>

<xsl:template match="box">
  <!-- This isn't great. -->
  <xsl:apply-templates/>
</xsl:template>

<xsl:template match="li">
  <!-- Word wrap li elements and star them. -->
  <xsl:text>  * </xsl:text>
  <xsl:call-template name="wrap-string">
   <xsl:with-param name="str" select="normalize-space(.)"/>
   <xsl:with-param name="wrap-col" select="65"/>
   <xsl:with-param name="break-mark" select="'&#xA;'"/>
   <xsl:with-param name="pos" select="4"/>
  </xsl:call-template>
  <xsl:text>&#xA;</xsl:text>
</xsl:template>

<xsl:template match="dd">
  <!-- Word wrap dd elements and indent them. -->
  <xsl:text>      </xsl:text>
  <xsl:call-template name="wrap-string">
   <xsl:with-param name="str" select="normalize-space(.)"/>
   <xsl:with-param name="wrap-col" select="65"/>
   <xsl:with-param name="break-mark" select="'&#xA;'"/>
   <xsl:with-param name="pos" select="6"/>
  </xsl:call-template>
  <xsl:text>&#xA;</xsl:text>
</xsl:template>

<xsl:template match="dt">
  <!-- Word wrap dt elements and indent them. -->
  <xsl:text>  </xsl:text>
  <xsl:call-template name="wrap-string">
   <xsl:with-param name="str" select="normalize-space(.)"/>
   <xsl:with-param name="wrap-col" select="65"/>
   <xsl:with-param name="break-mark" select="'&#xA;'"/>
   <xsl:with-param name="pos" select="2"/>
  </xsl:call-template>
  <xsl:text>&#xA;</xsl:text>
</xsl:template>

<xsl:template match="short">
  <xsl:apply-templates/>
  <xsl:text>&#xA;</xsl:text>
</xsl:template>

<xsl:template match="h1">
  <xsl:text>&#xA;--- </xsl:text>
  <xsl:apply-templates/>
  <xsl:text> ---&#xA;&#xA;</xsl:text>
</xsl:template>

<xsl:template match="h2">
  <xsl:text>&#xA;--- </xsl:text>
  <xsl:apply-templates/>
  <xsl:text> ---&#xA;&#xA;</xsl:text>
</xsl:template>

<xsl:template match="h3">
  <xsl:text>&#xA;--- </xsl:text>
  <xsl:apply-templates/>
  <xsl:text> ---&#xA;&#xA;</xsl:text>
</xsl:template>

<xsl:template match="h4">
  <xsl:text>&#xA;</xsl:text>
  <xsl:apply-templates/>
  <xsl:text>&#xA;&#xA;</xsl:text>
</xsl:template>

<xsl:template match="h5">
  <xsl:text>&#xA;</xsl:text>
  <xsl:apply-templates/>
  <xsl:text>&#xA;&#xA;</xsl:text>
</xsl:template>

<xsl:template match="code">
  <xsl:value-of select="."/>
  <xsl:text>&#xA;&#xA;</xsl:text>
</xsl:template>

<xsl:template match="see">
  <!-- This doesn't work with word-wrapping tags like <p> and <li>. -->
  <xsl:value-of select="."/>
  <xsl:text> (Link: </xsl:text>
  <xsl:value-of select="@topic"/>
  <xsl:text>)</xsl:text>
</xsl:template>

<!-- I got this this word-wrapping code from http://plasmasturm.org/log/204/ -->
<xsl:template name="wrap-string">
    <xsl:param name="str" />
    <xsl:param name="wrap-col" />
    <xsl:param name="break-mark" />
    <xsl:param name="pos" select="0" />
    <xsl:choose>
        <xsl:when test="contains( $str, ' ' )">
            <xsl:variable name="before" select="substring-before( $str, ' ' )" />
            <xsl:variable name="pos-now" select="$pos + string-length( $before )" />

            <xsl:choose>
                <xsl:when test="$pos = 0" />
                <xsl:when test="floor( $pos div $wrap-col ) != floor( $pos-now div $wrap-col )">
                    <xsl:copy-of select="$break-mark" />
                </xsl:when>
                <xsl:otherwise>
                    <xsl:text> </xsl:text>
                </xsl:otherwise>
            </xsl:choose>

            <xsl:value-of select="$before" />

            <xsl:call-template name="wrap-string">
                <xsl:with-param name="str" select="substring-after( $str, ' ' )" />
                <xsl:with-param name="wrap-col" select="$wrap-col" />
                <xsl:with-param name="break-mark" select="$break-mark" />
                <xsl:with-param name="pos" select="$pos-now" />
            </xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
            <xsl:if test="$pos &gt; 0"><xsl:text> </xsl:text></xsl:if>
            <xsl:value-of select="$str" />
        </xsl:otherwise>
    </xsl:choose>
</xsl:template>

</xsl:stylesheet>
