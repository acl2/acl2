/*

ACL2 Sidekick
Copyright (C) 2014 Kookamara LLC

Contact:

  Kookamara LLC
  11410 Windermere Meadows
  Austin, TX 78759, USA
  http://www.kookamara.com/

License: (An MIT/X11-style license)

  Permission is hereby granted, free of charge, to any person obtaining a
  copy of this software and associated documentation files (the "Software"),
  to deal in the Software without restriction, including without limitation
  the rights to use, copy, modify, merge, publish, distribute, sublicense,
  and/or sell copies of the Software, and to permit persons to whom the
  Software is furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in
  all copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
  FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
  DEALINGS IN THE SOFTWARE.

*/

function toolbar_item(name, internalname)
{
    if (typeof(internalname) === 'undefined')
	internalname = name.toLowerCase();

    var item = "<td class='toolbutton'>";
    item += "<a href='" + internalname + ".html'>";
    item += "<img src='icons/" + internalname + ".png'/><br/>";
    item += name;
    item += "</a>";
    item += "</td>";
    return item;
}

function toolbar_init()
{
    var form = jQuery("<form id='lookup_form' method='get' action='lookup.html'></form>");

    var toolbar = jQuery("<table></table>");
    var row = jQuery("<tr></tr>");
    row.append(toolbar_item(":home", "index"));
    row.append(toolbar_item(":session", "session"));
    row.append(toolbar_item("Profiler"));
    row.append(toolbar_item(":lint", "linter"));

    var lookup = "";
    lookup += "<label for='lookup'>:show </label>";
    lookup += "<input id='lookup' name='lookup' type='text' size='20' placeholder='append'></input>";
    lookup += "<input type='submit' style='position: absolute; left: -9999px; width: 1px; height: 1px;'";
    lookup += " hidefocus='true' tabindex='-1'></input>";
//    lookup += "<img src='icons/lookup.png' valign='top' />";
//    row.append("<td class='toolbutton' valign='middle' style='padding-top: 1em; text-align: right;' width='100%';>" + lookup + "</td>");
    row.append("<td class='toolbutton' valign='middle' style='text-align: right;' width='100%';>" + lookup + "</td>");
    toolbar.append(row);

    form.append(toolbar);
    $("#toolbar").html(form);
}

function footer_init()
{
    var footer = jQuery("<table class='kookamara' width='100%'></table>");
    var guts = "";
    guts += "<tr>";
    guts += "<td id='package'></td>";
    guts += "<td id='webcommand'></td>";
    guts += "<td id='status'></td>";
    guts += "<td align='right'>";
    guts += "<a href='http://www.kookamara.com/' target='_blank'><img src='icons/kookamara.png'/></a>";
    guts += "</td>";
    guts += "</tr>";
    guts += "</table>";
    footer.append(guts);
    $("#footer").html(footer);
    setTimeout(refresh_package, 10);
    setTimeout(refresh_status, 10);
    setTimeout(check_webcommands, 10);
}

var footer_package = "";

function refresh_package()
{
    $.get("/package", null, function(data,textStatus,jqXHR)
    {
	var new_pkg = data[":PACKAGE"];
	if (new_pkg != footer_package) {
	    $("#package").html(htmlEncode(new_pkg) + " !&gt;");
	    footer_package = new_pkg;
	}
	setTimeout(refresh_package, 1000);
    }).fail(function() {
	$("#package").html("??? !&gt;");
	setTimeout(refresh_package, 1000);
    });
}

var footer_status = "";

function refresh_status()
{
    var refresh_time = 1000;
    $.get("/pbtx", null, function(data,textStatus,jqXHR)
    {
	var ldd = data[":VAL"][0];
	var form = ldd[":FORM"];
	var n = ldd[":N"];
	var new_status = "<tt><b>" + n + "</b> : <tt>" + form + "</tt>";
	if (new_status != footer_status) {
	    $("#status").html(new_status);
	    footer_status = new_status;
	}
	setTimeout(refresh_status, refresh_time);
    }).fail(function() {
	$("#status").html("???");
	setTimeout(refresh_status, refresh_time);
    });
}

function check_webcommands()
{
    var check_time = 200;
    $.get("/webcommands", null, function(data,textStatus,jqXHR)
    {
	var commands = data[":COMMANDS"];
	if (commands != "NIL") {
	    //console.log("Commands = " + commands);
	    //console.log("Commands keys = " + Object.keys(commands));
	    process_webcommands(commands);
	}
	setTimeout(check_webcommands, check_time); // BOZO move to end

    }).fail(function() {
	$("#webcommand").html("Error getting webcommands");
	setTimeout(check_webcommands, check_time);
    });
}

function process_webcommands(commands)
{
    // It's a stack, so process it in reverse order
    var len = commands.length;
    console.log("Found " + len + " web commands.");
    for(var i = len-1; i >= 0; i--) {
	process_webcommand(commands[i]);
    }
}

function process_webcommand(command)
{
    var action = command[":ACTION"];
    if (!action) {
	console.log("Command doesn't have an :action field?" + Object.keys(command));
	return;
    }

    console.log("Processing web command: " + action);
    if (action == ":HOME") {
	window.location.href = "/index.html";
    }
    else if (action == ":LINT") {
	window.location.href = "/linter.html";
    }
    else if (action == ":SESSION") {
	window.location.href = "/session.html";
    }
    else if (action == ":SHOW") {
	var name = command[":NAME"];
	console.log("name is " + name);
	window.location.href = "/lookup.html?lookup=" + name;
    }


}

$(document).ready(function(){
    toolbar_init();
    footer_init();
});

