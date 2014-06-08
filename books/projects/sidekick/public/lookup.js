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

function count_lines (str)
{
    var n = 0;
    for(var i = 0; i < str.length; ++i)
	if (str[i] == '\n') n++;
    return n;
}

function do_lookup ()
{
    $.get("/props", {"name":what}, function(data,textStatus,jqXHR)
    {
        $("#props").html("Hello");
	var err = data[":ERROR"];
	if (err != "NIL") {
	    $("#props").html(htmlEncode(err));
	    return;
	}
	var props = data[":VAL"];
	var div = jQuery("<div></div>");

	var shortrows = "";
	var longrows = "";

	for(var key in props) {
	    var keystr = key.toLowerCase().upcaseFirst().replace(/-/g, " ");
	    var val = props[key];
	    var n = count_lines(val);
	    var row = "";
	    if (n == 0) {
		row += "<tr class='short'>";
		row += " <th width='30%'>" + htmlEncode(keystr) + "</th>";
  	        row += " <td width='70%'><pre>" + htmlEncode(val) + "</pre></td>";
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

	div += "<h4>Raw Properties</h4>";
	div += "<div id='propswrap'>";
	div += "<table class='propstable'>";
	div += shortrows;
	div += longrows;
	div += "</table>";
	div += "</div>";

	$("#props").html(div);

    }).fail(function() {
	$("#props").html("Error getting props.");
    });
}

$(document).ready(do_lookup);
