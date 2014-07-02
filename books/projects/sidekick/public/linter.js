/*

ACL2 Sidekick
Copyright (C) 2014 Kookamara LLC

Contact:
  Kookamara LLC
  11410 Windermere Meadows, Austin TX, 78759, USA.
  http://www.kookamara.com/

This program is free software; you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free Software
Foundation; either version 2 of the License, or (at your option) any later
version.  This program is distributed in the hope that it will be useful but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
details.  You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software Foundation, Inc.,
51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

*/

function rule_to_string(x)
{
    console.assert(":RULE" in x, "Rule has no :RULE.");
    console.assert(":ORIGIN" in x, "Rule has no :ORIGIN.");
    console.assert(":BODY" in x, "Rule has no :BODY.");
    var name = x[":RULE"];
    var origin = x[":ORIGIN"];
    var body = x[":BODY"];

    var icon;

    if (origin instanceof Array) {
	origin = origin[origin.length-1];
	icon = "frombook.png";
    }
    else if (origin == ":BUILT-IN") {
	origin = "Built into ACL2";
	icon = "fromacl2.png";
    }
    else {
	origin = "Current session";
	icon = "fromsession.png";
    }

    var ret = "";
    ret += "<p>";
    ret += "<img src='icons/" + icon + "' align='left' style='padding-right: .3em;'/>";
    ret += "<span class='rulename'>" + htmlEncode(name.toLowerCase()) + "</span><br/>";
    ret += "<small><span class='from'>" + htmlEncode(origin) + "</span></small></p>"
    ret += "<pre>" + htmlEncode(body) + "</pre>";
    return ret;
}

function get_lint ()
{
    $.get("/lint", null, function(data,textStatus,jqXHR)
    {
	var err = data[":ERROR"];
	if (err != "NIL") {
	    $("#lint").html("<p>" + htmlEncode(err) + "</p>");
	    return;
	}
	console.log("Hello");
	var redundant = data[":REDUNDANT"];
	if (redundant == "NIL") {
	    $("#lint").html("<p>Nothing to report</p>");
	}
	console.assert(redundant instanceof Array, "thought redundant would be an array");
	var tbl = jQuery("<table class='redundant_table'></table>");
	for(var i = 0; i < redundant.length; ++i) {
	    var item = redundant[i];
	    console.assert(item[":TYPE"] == ":REDUNDANT", "Bad :TYPE for redundant entry.");
	    var entry = "";
	    entry += "<tr><td width='45%'>";
	    entry += rule_to_string(item[":RULE1"]);
	    entry += "</td><td class='vs' width='10%'>vs.</td><td width='45%'>";
	    entry += rule_to_string(item[":RULE2"]);
	    entry += "</td></tr>";
	    tbl.append(entry);
	}
	$("#lint").html("<h5>Redundant or Conflicting Rules</h5>");
	$("#lint").append(tbl);
 
    }).fail(function() {
	$("#lint").html("Error getting lint report.");
    });

}

$(document).ready(get_lint);

