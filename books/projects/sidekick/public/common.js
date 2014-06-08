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

function htmlEncode(value)
{
    // copied from stackoverflow:1219860
    return $('<div/>').text(value).html();
}

String.prototype.upcaseFirst = function () {
    var str = this;
    return str.charAt(0).toUpperCase() + str.slice(1);
}

function getPageParameters ()
{
   var ret = {};
   if (!window.location.toString().match(/\?(.+)$/)) {
       return ret;
   }
   var param_strs = RegExp.$1.split("&");
   var param_arr = {};
   for(var i in param_strs)
   {
      var tmp = param_strs[i].split("=");
      var key = decodeURI(tmp[0]);
      var val = decodeURI(tmp[1]);
      param_arr[key] = val;
   }
   return param_arr;
}

function popup_disassemble(name) {
    var w = window.open("disassemble.html?name=" + name, "Disassembly_" + name,
	"height=600,width=640,toolbar=1,location=0,resizable=1,scrollbars=1,status=0");
}