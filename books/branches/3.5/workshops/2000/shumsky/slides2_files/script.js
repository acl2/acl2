
function LoadSld( slideId )
{
	if( !g_supportsPPTHTML ) return
	if( slideId )
		parent.SldUpdated(slideId)
	g_origSz=parseInt(SlideObj.style.fontSize)
	g_origH=SlideObj.style.posHeight
	g_origW=SlideObj.style.posWidth
	g_scaleHyperlinks=(document.all.tags("AREA").length>0)
	if( g_scaleHyperlinks )
		InitHLinkArray()
	if( g_scaleInFrame||(IsWin("PPTSld") && parent.IsFullScrMode() ) )
		document.body.scroll="no"
	_RSW()
	if( IsWin("PPTSld") && parent.IsFullScrMode() )	{
		document.oncontextmenu=parent._CM;
		self.focus()
	}
}
function MakeSldVis( fTrans ) 
{
	fTrans=fTrans && g_showAnimation
	if( fTrans )
	{
		if( g_bgSound ) {
			idx=g_bgSound.indexOf(",");
			pptSound.src=g_bgSound.substr( 0, idx );
			pptSound.loop= -(parseInt(g_bgSound.substr(idx+1)));
		}
		SlideObj.filters.revealtrans.Apply()
	}
	SlideObj.style.visibility="visible"
	if( fTrans )
		SlideObj.filters.revealtrans.Play()
}
function MakeNotesVis() 
{
	if( !IsNts() ) return false 
	SlideObj.style.display="none"
	nObj = document.all.item("NotesObj")
	parent.SetHasNts(0)
	if( nObj ) { 
		nObj.style.display=""
		parent.SetHasNts(1)
	}
	return 1
}
function Redirect( frmId,sId )
{
	var str=document.location.hash,idx=str.indexOf('#')
	if(idx>=0) str=str.substr(1);
	if( window.name != frmId && ( sId != str) ) {
		obj = document.all.item("Main-File")
		window.location.href=obj.href+"#"+sId
		return 1
	}
	return 0
}
function HideMenu() { if( frames["PPTSld"] && PPTSld.document.all.item("ctxtmenu") && PPTSld.ctxtmenu.style.display!="none" ) { PPTSld.ctxtmenu.style.display='none'; return true } return false }
function IsWin( name ) { return window.name == name }
function IsNts() { return IsWin("PPTNts") }
function IsSldOrNts() { return( IsWin("PPTSld")||IsWin("PPTNts") ) }
function SupportsPPTAnimation() { return( navigator.platform == "Win32" && navigator.appVersion.indexOf("Windows")>0 ) }
function SupportsPPTHTML()
{
	var appVer=navigator.appVersion, msie=appVer.indexOf("MSIE "), ver=0
	if( msie >= 0 )
		ver=parseFloat( appVer.substring( msie+5, appVer.indexOf(";",msie) ) )
	else
		ver=parseInt(appVer)

	return( ver >= 4 && msie >= 0 )
}
var MHTMLPrefix = CalculateMHTMLPrefix(); 
function CalculateMHTMLPrefix()
{
	if ( document.location.protocol == 'mhtml:') { 
		href=new String(document.location.href) 
		Start=href.indexOf('!')+1 
		End=href.lastIndexOf('/')+1 
		if (End < Start) 
			return href.substring(0, Start) 
		else 
		return href.substring(0, End) 
	}
	return '';
}

function _RSW()
{
	if( !g_supportsPPTHTML || IsNts() ||
	  ( !g_scaleInFrame && (( window.name != "PPTSld" ) || !parent.IsFullScrMode()) ) )
		return

	cltWidth=document.body.clientWidth
	cltHeight=document.body.clientHeight
	factor=(1.0*cltWidth)/g_origW
	if( cltHeight < g_origH*factor )
		factor=(1.0*cltHeight)/g_origH

	newSize = g_origSz * factor
	if( newSize < 1 ) newSize=1

	s=SlideObj.style
	s.fontSize=newSize+"px"
	s.posWidth=g_origW*factor
	s.posHeight=g_origH*factor
	s.posLeft=(cltWidth-s.posWidth)/2
	s.posTop=(cltHeight-s.posHeight)/2

	if( g_scaleHyperlinks )
		ScaleHyperlinks( factor )
}

function _KPH()
{ 
  if( IsNts() ) return;

  if( !parent.IsFramesMode() && event.keyCode == 27 && !parent.HideMenu() )
    parent.window.close( self );
  else if( event.keyCode == 32 )
  {
    if( window.name == "PPTSld" )
      parent.PPTSld.DocumentOnClick();
    else
      parent.GoToNextSld();
  }
}

function DocumentOnClick()
{
	if( IsNts() || parent.HideMenu() ) return;
	if( ( g_allowAdvOnClick && !parent.IsFramesMode() ) ||
	    (event && (event.keyCode==32) ) )
		parent.GoToNextSld();
}



var g_supportsPPTHTML = SupportsPPTHTML(), g_scaleInFrame = true, gId="", g_bgSound="",
    g_scaleHyperlinks = false, g_allowAdvOnClick = true, g_showInBrowser = false;
var g_showAnimation = g_supportsPPTHTML && SupportsPPTAnimation() && ( (window.name=="PPTSld" && !parent.IsFramesMode()) || g_showInBrowser );var g_hasTrans = false, g_autoTrans = false, g_transSecs = 0;
var g_animManager = null;

var ENDSHOW_MESG="End of slide show, click to exit.", SCREEN_MODE="Frames", gIsEndShow=0, NUM_VIS_SLDS=19, SCRIPT_HREF="script.js", FULLSCR_HREF="fullscreen.htm";
var gCurSld = gPrevSld = 1, g_offset = 0, gNtsOpen = gHasNts = gOtlTxtExp = gNarrationPaused = false, gOtlOpen = true
window.gPPTHTML=SupportsPPTHTML()

function UpdNtsPane(){ PPTNts.location.replace( MHTMLPrefix+GetHrefObj( gCurSld ).mNtsHref ) }
function UpdNavPane( sldIndex ){ if(gNavLoaded) PPTNav.UpdNav() }
function UpdOtNavPane(){ if(gOtlNavLoaded) PPTOtlNav.UpdOtlNav() }
function UpdOtlPane(){ if(gOtlLoaded) PPTOtl.UpdOtl() }
function SetHasNts( fVal )
{
	if( gHasNts != fVal ) {
		gHasNts=fVal
		UpdNavPane()
	}
}
function ToggleOtlText()
{
	gOtlTxtExp=!gOtlTxtExp
	UpdOtlPane()
}
function ToggleOtlPane()
{
	frmset=document.all("PPTHorizAdjust")
	frm=document.all("PPTOtl")

	if( gOtlOpen )
		frmset.cols="*,100%"
	else
		frmset.cols="20%,80%"

	gOtlOpen=!gOtlOpen
	frm.noResize=!frm.noResize
	UpdOtNavPane()
}
function ToggleNtsPane()
{
	frmset=document.all("PPTVertAdjust")
	frm=document.all("PPTNts")

	if( gNtsOpen )
		frmset.rows="100%,*"
	else
		frmset.rows="80%,20%"

	gNtsOpen=!gNtsOpen
	UpdNtsPane()
}
function FullScreen(){ window.open( MHTMLPrefix+FULLSCR_HREF,null,"fullscreen=yes" ) }
function ToggleVNarration()
{
	rObj=PPTSld.document.all("NSPlay")
	if( rObj ) {
		if( gNarrationPaused )
			rObj.Play()
		else
			rObj.Pause()

		gNarrationPaused=!gNarrationPaused
	}
}
function GetCurSldNum()
{   
	obj=GetHrefObj(gCurSld)
	if( obj.mOrigVis == 1 )
		return obj.mSldIdx
	else   
		return gCurSld
}
function GetNumSlds()
{   
	if( GetHrefObj(gCurSld).mOrigVis == 1 )
		return NUM_VIS_SLDS
	else
		return gDocTable.length
}
function GetSldNum( href )
{
	for(ii=0; ii<gDocTable.length; ii++) {
		if ( gDocTable[ii].mSldHref == href )
			return ii+1
	}
	return 1
}
function GetHrefObj( sldIdx ){ return gDocTable[sldIdx-1] }
function IsFramesMode(){ return ( SCREEN_MODE == "Frames" ) }
function IsFullScrMode(){ return ( SCREEN_MODE == "FullScreen" ) }
function GoToNextSld()
{   
	ii=gCurSld + 1
	if( GetHrefObj( ii-1 ).mOrigVis == 0 ) {
		if( ii<=gDocTable.length ) {
			obj=GetHrefObj(ii)
			obj.mVis=1
			GoToSld(obj.mSldHref)
			return
		}		
	}
	else {
		obj=GetHrefObj( ii )
		while ( obj && ( obj.mOrigVis == 0 ) )
			obj=GetHrefObj(ii++)
		if( obj && obj.mOrigVis ) {
			GoToSld(obj.mSldHref)	
			return
		}	
	}
	if( !IsFramesMode() ) EndShow()
}
function GoToPrevSld()
{
	ii=gCurSld-1
	if( ii > 0 ) {      
		obj=GetHrefObj(ii)
		while ( ( obj.mVis == 0 ) && ( ii>0 ) )
			obj=GetHrefObj(ii--)
		GoToSld(obj.mSldHref)
	}
}
function GoToFirst(){ GoToSld( GetHrefObj(1).mSldHref ) }
function GoToLast()
{
	ii=gDocTable.length
	if( ii != gCurSld )
		GoToSld( GetHrefObj(ii).mSldHref )
}
function GoToSld( href )
{
	if( PPTSld.event ) PPTSld.event.cancelBubble=true
	GetHrefObj( GetSldNum(href) ).mVis=1
	PPTSld.location.href=MHTMLPrefix+href
}
function SldUpdated( id )
{
	if( id == GetHrefObj(gCurSld).mSldHref ) return
	gPrevSld=gCurSld
	gCurSld=GetSldNum(id)
	if( IsFramesMode() ) {
		UpdNavPane(); UpdOtlPane(); UpdNtsPane()
	}
}

function PrevSldViewed(){ GoToSld( GetHrefObj(gPrevSld).mSldHref ) }
function HasPrevSld() { return ( gIsEndShow || ( gCurSld != 1 && GetHrefObj( gCurSld-1 ).mVis == 1 )||( GetCurSldNum() > 1 ) ) }
function HasNextSld() { return (GetCurSldNum() != GetNumSlds()) }
function EndShow()
{
	if( PPTSld.event ) PPTSld.event.cancelBubble=true

	doc=PPTSld.document
	doc.open()
	doc.writeln('<html><head><script defer>function CloseWindow(){ if( parent.HideMenu() ) return; if( !parent.IsFramesMode() && event && (event.keyCode==27 || event.keyCode==32 || event.type=="click" ) ) parent.window.close( self ); } function Unload() { parent.gIsEndShow=0; } function SetupEndShow() { parent.gIsEndShow=1; document.body.scroll="no"; document.onkeypress=CloseWindow; document.onclick=CloseWindow; document.oncontextmenu=parent._CM; }</script></head><body bgcolor=black onload=SetupEndShow() onunload=Unload()><center><p><font face=Tahoma color=white size=2><br><b>' + ENDSHOW_MESG + '</b></font></p></center></body></html>')
	doc.close()
}
function SetSldVisited(){ gDocTable[gCurSld-1].mVisited=true }
function IsSldVisited(){ return gDocTable[gCurSld-1].mVisited }
function hrefList( sldHref, visible, sldIdx )
{
	this.mSldHref= this.mNtsHref = sldHref
	this.mSldIdx = sldIdx
	this.mOrigVis= this.mVis = visible
	this.mVisited= false
}
var gDocTable = new Array(
   new hrefList("slide0001.htm", 1, 1),
   new hrefList("slide0003.htm", 1, 2),
   new hrefList("slide0004.htm", 1, 3),
   new hrefList("slide0020.htm", 1, 4),
   new hrefList("slide0005.htm", 1, 5),
   new hrefList("slide0021.htm", 1, 6),
   new hrefList("slide0032.htm", 1, 7),
   new hrefList("slide0033.htm", 1, 8),
   new hrefList("slide0026.htm", 1, 9),
   new hrefList("slide0027.htm", 1, 10),
   new hrefList("slide0028.htm", 1, 11),
   new hrefList("slide0009.htm", 1, 12),
   new hrefList("slide0010.htm", 1, 13),
   new hrefList("slide0013.htm", 1, 14),
   new hrefList("slide0029.htm", 1, 15),
   new hrefList("slide0030.htm", 1, 16),
   new hrefList("slide0015.htm", 1, 17),
   new hrefList("slide0016.htm", 1, 18),
   new hrefList("slide0017.htm", 1, 19)
);

function ImgBtn( oId,bId,w,action )
{
	var t=this
	t.Perform    = _IBP
	t.SetActive  = _IBSetA
	t.SetInactive= _IBSetI
	t.SetPressed = _IBSetP
	t.SetDisabled= _IBSetD
	t.Enabled    = _IBSetE
	t.ChangeIcon = null
	t.UserAction = action
	t.ChgState   = _IBUI
	t.mObjId   = oId
	t.mBorderId= bId
	t.mWidth   = w
	t.mIsOn    = t.mCurState = 0
}
function _IBSetA()
{
	if( this.mIsOn ) {
		obj=this.ChgState( gHiliteClr,gShadowClr,2 )
		obj.style.posTop=0
	}
}
function _IBSetI()
{
	if( this.mIsOn ) {
		obj=this.ChgState( gFaceClr,gFaceClr,1 )
		obj.style.posTop=0 
	}
}
function _IBSetP()
{
	if( this.mIsOn ) {
		obj=this.ChgState( gShadowClr,gHiliteClr,2 )
		obj.style.posLeft+=1; obj.style.posTop+=1
	}
}
function _IBSetD()
{  
	obj=this.ChgState( gFaceClr,gFaceClr,0 )
	obj.style.posTop=0 
}
function _IBSetE( state )
{
	var t=this
	GetObj( t.mBorderId ).style.visibility="visible"
	if( state != t.mIsOn ) {
		t.mIsOn=state
		if( state )
			t.SetInactive()
		else
			t.SetDisabled()
	}
}
function _IBP()
{
	var t=this
	if( t.mIsOn ) {
		if( t.UserAction != null )
			t.UserAction()
		if( t.ChangeIcon ) {
			obj=GetObj(t.mObjId)
			if( t.ChangeIcon() )
				obj.style.posLeft=obj.style.posLeft+(t.mCurState-4)*t.mWidth
			else
				obj.style.posLeft=obj.style.posLeft+(t.mCurState-0)*t.mWidth
		}
		t.SetActive()
	}  
}
function _IBUI( clr1,clr2,nextState )
{
	var t=this
	SetBorder( GetObj( t.mBorderId ),clr1,clr2 )
	obj=GetObj( t.mObjId )
	obj.style.posLeft=obj.style.posLeft+(t.mCurState-nextState)*t.mWidth-obj.style.posTop
	t.mCurState=nextState
	return obj
}
function TxtBtn( oId,oeId,action,chkState )
{
	var t=this
	t.Perform    = _TBP
	t.SetActive  = _TBSetA
	t.SetInactive= _TBSetI
	t.SetPressed = _TBSetP
	t.SetDisabled= _TBSetD
	t.SetEnabled = _TBSetE
	t.GetState   = chkState
	t.UserAction = action
	t.ChgState   = _TBUI
	t.mObjId      = oId
	t.m_elementsId= oeId
	t.mIsOn       = 1
}
function _TBSetA()
{
	var t=this
	if( t.mIsOn && !t.GetState() )
		t.ChgState( gHiliteClr,gShadowClr,0,0 )
}
function _TBSetI()
{
	var t=this
	if( t.mIsOn && !t.GetState() )
		t.ChgState( gFaceClr,gFaceClr,0,0 )
}
function _TBSetP()
{
	if( this.mIsOn )
		this.ChgState( gShadowClr,gHiliteClr,1,1 )
}
function _TBSetD()
{   
	this.ChgState( gFaceClr,gFaceClr,0,0 )
	this.mIsOn = 0
}
function _TBSetE()
{
	var t=this
	if( !t.GetState() )
		t.ChgState( gFaceClr,gFaceClr,0,0 )
	else
		t.ChgState( gShadowClr,gHiliteClr,1,1 )
	t.mIsOn = 1
}
function _TBP()
{
	var t=this
	if( t.mIsOn ) { 
		if( t.UserAction != null )
			t.UserAction()
		if( t.GetState() )
			t.SetPressed()
		else
			t.SetActive()
	}  
}
function _TBUI( clr1,clr2,lOffset,tOffset )
{
	SetBorder( GetObj( this.mObjId ),clr1,clr2 )
	Offset( GetObj( this.m_elementsId ),lOffset,tOffset )
}
function GetObj( objId ){ return document.all.item( objId ) }
function Offset( obj, top, left ){ obj.style.top=top; obj.style.left=left }
function SetBorder( obj, upperLeft, lowerRight )
{
	s=obj.style;
	s.borderStyle      = "solid"
	s.borderWidth      = 1 
	s.borderLeftColor  = s.borderTopColor = upperLeft
	s.borderBottomColor= s.borderRightColor = lowerRight
}
function GetBtnObj(){ return gBtnArr[window.event.srcElement.id] }
function BtnOnOver(){ b=GetBtnObj(); if( b != null ) b.SetActive() }
function BtnOnDown(){ b=GetBtnObj(); if( b != null ) b.SetPressed() }
function BtnOnOut(){ b=GetBtnObj(); if( b != null ) b.SetInactive() }
function BtnOnUp()
{
	b=GetBtnObj()
	if( b != null )
		b.Perform()
	else
		Upd()
}
function GetNtsState(){ return parent.gNtsOpen }
function GetOtlState(){ return parent.gOtlOpen }
function GetOtlTxtState(){ return parent.gOtlTxtExp }
function NtsBtnSetFlag( fVal )
{
	s=document.all.item( this.m_flagId ).style
	s.display="none"
	if( fVal )
		s.display=""
	else
		s.display="none"
}

var gHiliteClr="THREEDHIGHLIGHT",gShadowClr="THREEDSHADOW",gFaceClr="THREEDFACE"
var gBtnArr = new Array()
gBtnArr["nb_otl"] = new TxtBtn( "nb_otl","nb_otlElem",parent.ToggleOtlPane,GetOtlState )
gBtnArr["nb_nts"] = new TxtBtn( "nb_nts","nb_ntsElem",parent.ToggleNtsPane,GetNtsState )
gBtnArr["nb_prev"]= new ImgBtn( "nb_prev","nb_prevBorder",30,parent.GoToPrevSld )
gBtnArr["nb_next"]= new ImgBtn( "nb_next","nb_nextBorder",30,parent.GoToNextSld )
gBtnArr["nb_sldshw"]= new ImgBtn( "nb_sldshw","nb_sldshwBorder",18,parent.FullScreen )
gBtnArr["nb_voice"]  = new ImgBtn( "nb_voice","nb_voiceBorder",18,parent.ToggleVNarration )
gBtnArr["nb_otlTxt"]= new ImgBtn( "nb_otlTxt","nb_otlTxtBorder",23,parent.ToggleOtlText )
gBtnArr["nb_nts"].m_flagId= "notes_flag"
gBtnArr["nb_nts"].SetFlag = NtsBtnSetFlag
gBtnArr["nb_otlTxt"].ChangeIcon= GetOtlTxtState
var sNext="Next",sPrev="Previous",sEnd="End Show",sFont="Arial"
function ShowMenu()
{
	BuildMenu();
	var doc=PPTSld.document.body,x=PPTSld.event.clientX+doc.scrollLeft,y=PPTSld.event.clientY+doc.scrollTop

	m = PPTSld.document.all.item("ctxtmenu")
	m.style.pixelLeft=x
	if( (x+m.scrollWidth > doc.clientWidth)&&(x-m.scrollWidth > 0) )
		m.style.pixelLeft=x-m.scrollWidth

	m.style.pixelTop=y
	if( (y+m.scrollHeight > doc.clientHeight)&&(y-m.scrollHeight > 0) )
		m.style.pixelTop=y-m.scrollHeight

	m.style.display=""
}
function _CM()
{
	if( !parent.IsFullScrMode() ) return;
	if(!PPTSld.event.ctrlKey) {
		ShowMenu()
		return false
	} else
		HideMenu()
}
function BuildMenu()
{
	if( PPTSld.document.all.item("ctxtmenu") ) return

	var mObj=CreateItem( PPTSld.document.body )
	mObj.id="ctxtmenu"
	var s=mObj.style
	s.position="absolute"
	s.cursor="default"
	s.width="100px"
	SetCMBorder(mObj,"menu","black")

	var iObj=CreateItem( mObj )
	SetCMBorder( iObj, "threedhighlight","threedshadow" )
	iObj.style.padding=2
	CreateMenuItem( iObj,sNext,M_GoNextSld,M_True )
	CreateMenuItem( iObj,sPrev,M_GoPrevSld,M_HasPrevSld )
	var sObj=CreateItem( iObj )
	SetCMBorder(sObj,"menu","menu")
	var s=sObj.style
	s.borderTopColor="threedshadow"
	s.borderBottomColor="threedhighlight"
	s.height=1
	s.fontSize="0px"
	CreateMenuItem( iObj,sEnd,M_End,M_True )
}
function Highlight() { ChangeClr("activecaption","threedhighlight") }
function Deselect() { ChangeClr("threedface","menutext") }
function Perform()
{
	e=PPTSld.event.srcElement
	if( e.type=="menuitem" && e.IsActive() )
		e.Action()
	else
		PPTSld.event.cancelBubble=true
}
function ChangeClr( bg,clr )
{
	e=PPTSld.event.srcElement
	if( e.type=="menuitem" && e.IsActive() ) {
		e.style.backgroundColor=bg
		e.style.color=clr
	}
}

function M_HasPrevSld() { return( parent.HasPrevSld() ) }
function M_GoNextSld() { if( gIsEndShow ) M_End(); else GoToNextSld() }
function M_GoPrevSld() { if( gIsEndShow ) { history.back(); PPTSld.event.cancelBubble=true; } else GoToPrevSld() }
function M_True() { return true }
function M_End() { window.close( self ) }
function CreateMenuItem( node,text,action,eval )
{
	var e=CreateItem( node )
	e.type="menuitem"
	e.Action=action
	e.IsActive=eval
	e.innerHTML=text

	if( !e.IsActive() )
		e.style.color="threedshadow"
	e.onclick=Perform
	e.onmouseover=Highlight
	e.onmouseout=Deselect
	s=e.style;
	s.fontFamily=sFont
	s.fontSize="8pt"
	s.paddingLeft=2
}
function CreateItem( node )
{
	var elem=PPTSld.document.createElement("DIV")
	node.insertBefore( elem )
	return elem
}
function SetCMBorder( o,ltClr,rbClr )
{
	var s=o.style
	s.backgroundColor="menu"
	s.borderStyle="solid"
	s.borderWidth=1
	s.borderColor=ltClr+" "+rbClr+" "+rbClr+" "+ltClr
}