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

var params = getPageParameters();
var what = params["lookup"];

console.log("Lookup parameter = " + what);

function count_lines (str)
{
    var n = 0;
    for(var i = 0; i < str.length; ++i)
	if (str[i] == '\n') n++;
    return n;
}

function get_disassembly (name)
{
   $.get("/disassemble", {"name":name}, function(data,textStatus,jqXHR)
   {
       var err = data[":ERROR"];
       var val = data[":VAL"];
       if (err != "NIL") {
	   $("#disassembly").html(err);
	   return;
       }
       console.log("Disassembly is " + val);
       var guts = "";
       guts += "<h4>Disassembly of " + htmlEncode(name) + "</h4>";
       guts += "<pre class='disassemble_out'>";
       guts += val;
       guts += "</pre>";
       $("#disassembly").html(guts);
    }).fail(function() {
	$("#disassembly").html("Error getting /disassemble result");
    });
}

function get_origin ()
{
    $.get("/origin", {"name":what}, function(data,textStatus,jqXHR)
    {
	var err = data[":ERROR"];
	if (err != "NIL") {
	    $("#origin").html("Error: " + htmlEncode(err));
	    return;
	}
	var origin = "";
	var val = data[":VAL"];
	if (val == "NIL"){
	    $("#origin").html("Origin not found.");
	    return;
	}
	if (val == ":BUILT-IN") {
	    origin = "<h4>Built into ACL2</h4>";
	}
	else if (val == ":TOP-LEVEL") {
	    origin = "<h4>From current session</h4>";
            origin += "<p>BOZO say which event number, ";
	    origin += "offer to undo through here.</p>";
	}
	else {
	    origin = "<h4 id='include_path_header'>From included book</h4>";
	    origin += "<ul id='include_path'>";
	    for(var i in val) {
   	       origin += "<li><tt>" + htmlEncode(val[i]) + "</tt></li>";
	    }
	    origin += "</ul>";
	}
	$("#origin").html(origin);
    }).fail(function() {
	$("#origin").html("Error getting origin");
    });
}

function get_props (name)
{
    $.get("/props", {"name":what}, function(data,textStatus,jqXHR)
    {
	var err = data[":ERROR"];
	if (err != "NIL") {
	    $("#props").html(htmlEncode(err));
	    return;
	}
	var props = data[":VAL"];
	if (props == "NIL") {
	    $("#props").html("No properties found.");
	    return;
	}

	var shortrows = "";
	var longrows = "";

	for(var key in props) {
	    var keystr = key.toLowerCase().upcaseFirst().replace(/-/g, " ");
	    var val = props[key];
	    var n = count_lines(val);
	    var row = "";
	    if (n == 0) {
		row += "<tr class='short'>";
		row += " <th width='200'>" + htmlEncode(keystr) + "</th>";
  	        row += " <td><pre>" + htmlEncode(val) + "</pre></td>";
		row += "</tr>";
		shortrows += row;
	    }
	    else {
		row += "<tr class='longhead'>";
  	        row += " <th colspan='2'>" + htmlEncode(keystr) + "</th>";
		row += "</tr>";
 	        row += "<tr class='longbody'>";
		row += " <td colspan='2' style='padding-left: 1em;'>";
		row += "  <pre>" + htmlEncode(val) + "</pre>";
                row += " </td>";
                row += "</tr>";
		longrows += row;
	    }
	}

	var acc = "";
	acc += "<h4 id='propshead'>Raw Properties</h4>";
	acc += "<div id='propswrap'>";
	acc += "<table class='propstable'>";
	acc += shortrows;
	acc += longrows;
	acc += "</table>";
	acc += "</div>";

	$("#props").html(acc);

	get_disassembly(what);
    }).fail(function() {
	$("#props").html("Error getting props.");
    });
}

function get_xdoc (what)
{
    $.get("/xdoc", {"name":what}, function(data,textStatus,jqXHR)
    {
	var err = data[":ERROR"];
	if (err != "NIL") {
	    $("#xdoc").html("<p>" + htmlEncode(err) + "</p>");
	    return;
	}

	var short_xml = data[":SHORT"];
	var long_xml = data[":LONG"];

	var div = jQuery("<div></div>");
	var shortpar = jQuery("<p></p>");
	shortpar.append(render_html(short_xml));
	div.append(shortpar);
	div.append(render_html(long_xml));

	$("#xdoc").html(div);



    }).fail(function() {
	$("#xdoc").html("Error getting /xdoc.");
    });
}

function do_lookup ()
{
    $("#what").html(htmlEncode(what));

    get_origin();
    get_props(what);
    get_xdoc(what);
}

$(document).ready(do_lookup);
