(in-package "ACL2S")

(include-book "xdoc/top" :dir :system)

(defxdoc acl2s-installation
  :parents (acl2::acl2-sedan)
  :short "Describes how to install ACL2s"
  :long
"
<h3>Installing ACL2s</h3>

<p>
For specific instructions on how to install ACL2s on your computer,
please select the appropriate topic below:
</p>

<ul>
<li>@(see acl2s-installation-windows)</li>
<li>@(see acl2s-installation-macos)</li>
<li>@(see acl2s-installation-linux)</li>
</ul>
")

(defxdoc acl2s-installation-windows
  :parents (acl2s-installation)
  :short "Installation instructions for ACL2s on Windows"
  :long
"
<h3>Description</h3>
<p>
To run ACL2s on Windows, we will use
<a href=\"https://docs.microsoft.com/en-us/windows/wsl/about\">WSL 
(the Windows Subsystem for Linux)</a>. This allows us to run the
Linux version of Eclipse and ACL2s on Windows machines.
</p>

<p>
If you run into any issues, check out the @(see acl2s-installation-faq)
topic.
</p>

<h3>Requirements</h3>
<ul>
  <li>at least 8GB of free hard drive space</li>
  <li>at least 4GB of RAM</li>
  <li>Windows 10 version 21H1 or greater. Windows 11 may also work.</li>
</ul>

<p>
Installation should take less than an hour, though installation time
will depend on your computer's specs and on the speed of your internet
connection. You can use your computer while the installation is
occurring.
</p>

<h3>Instructions</h3>
<ol>
<li>Install WSL
  <ol>
  <li>Open an administrator terminal (either CMD or Powershell). This
  can be done by opening the Windows menu at the bottom left hand
  side of the screen and searching for @('cmd'). Then, right click
  on the \"Command Prompt\" item and select \"Run as administrator\".</li>
  <li>Run @('dism.exe /online /enable-feature /featurename:Microsoft-Windows-Subsystem-Linux /all /norestart')</li>
  <li>Run @('dism.exe /online /enable-feature /featurename:VirtualMachinePlatform /all /norestart')</li>
  <li>Restart your computer. <b>Select \"Update and Restart\" in the power menu if it appears.</b></li>
  <li>Reopen an administrator terminal as you did previously and run @('wsl --update')</li>
  </ol>
</li>
<li>Download and set up the ACL2s WSL image
  <ol>
  <li>Download <a href=\"https://github.com/mister-walter/homebrew-acl2s/releases/download/acl2s-0.1.6/distro.tar.gz\">distro.tar.gz</a> to your Downloads folder.</li>
  <li>Open up a new <b>non-admininistrator</b> terminal by opening the Windows
      menu at the bottom left hand side of the screen and searching for
      @('cmd').
  </li>
  <li>Run @('mkdir C:\\wslDistroStorage')</li>
  <li>Run @('wsl --import acl2s C:\\wslDistroStorage\\acl2s Downloads\\distro.tar.gz'). <b>Note that this may take a while, somewhere between 5 and 15 minutes</b>. Disabling any virus scanners may significantly speed this up.</li>
  <li>Run @('wsl -d acl2s') and confirm that you get some output (e.g. not a blank line). If so, you can close the terminal. Note that this may take some time and you may see some errors about @('DISPLAY') first.</li>
  </ol>
</li>
<li>Install Xming and launch it
  <ol>
  <li>Download the installer
  <a href=\"https://cs2800.atwalter.com/cs2800/Xming-6-9-0-31-setup.exe\"><b>here</b></a>
  and run it.</li>
  <li><strong>Do not</strong> uncheck the option to associate .xlaunch files with
  Xming during installation! <strong>Do</strong> uncheck the option to launch
  Xming after the installation is complete.</li>
  <li>Download our Xming launch profile
  <a href=\"https://cs2800.atwalter.com/cs2800/ACL2sXming.xlaunch\"><b>here</b></a>
  and put it somewhere memorable. <b>You may need to right-click on
  the link and select \"Save As...\" if your browser doesn't
  download it automatically.</b></li>
  <li>Double click on our Xming launch profile to start Xming. If
  Windows asks you which networks you want to allow Xming to
  access, make sure you allow it to access both private and
  public networks.<b>Note that double clicking on ACL2sXming.xlaunch
  will not open a new window.</b> It will add an item to the system
  tray on the right-hand side of the task bar, and you may need to click
  on the up caret (^) to see it.
  </li>
  </ol>
</li>
<li>Create a folder for your CS2800 files on your @('C:') drive
<ol>
  <li>Open File Explorer, select \"This PC\" on the left, double click
  on \"Local Disk (C:)\", right-click on an empty area inside of
  that folder, and select \"New Folder\". Name the folder whatever
  you would like.</li>
</ol>
</li>
<li>Run Eclipse
<ol>
  <li>Download <a href=\"https://github.com/mister-walter/homebrew-acl2s/releases/download/acl2s-0.1.6/run-acl2s.bat\">run-acl2s.bat</a> and save it somewhere memorable. Note that depending on your browser, you might get a warning when you download this file, but you should click \"Keep\" or \"Download Anyways\".</li>
  <li>Double click on @('run-acl2s.bat') to launch a WSL terminal and Eclipse. A window titled \"Windows protected your PC\" may appear. If so, click on \"More info\" and then \"Run anyways\" at the bottom of the window.</li>
  <li>When Eclipse asks for a workspace, enter @('/mnt/c/<FOLDER>'),
  where @('<FOLDER>') should be replaced with the name of the folder
  that you just created.</li>
</ol>
</li>
<li>Get started with Eclipse by working through the @(see acl2s-tutorial). </li>
</ol>
")

(defxdoc acl2s-installation-macos
  :parents (acl2s-installation)
  :short "Installation instructions for ACL2s on macOS"
  :long
  "
<h3 id=\"requirements\">Requirements</h3>
<ul>
<li>at least 5GB of free hard drive space</li>
<li>at least 4GB of RAM</li>
<li>macOS Catalina (10.15), Big Sur (11), or Monterey (12)</li>
</ul>
<p>Installation should take less than an hour, though installation time
will depend on your computer's specs and on the speed of your internet
connection. You can use your computer while the installation is
occurring.</p>

<p>
If you run into any issues, check out the @(see acl2s-installation-faq)
topic.
</p>

<h3 id=\"instructions\">Instructions</h3>
<p>A video walking through installation is available
<a href=\"https://youtu.be/AFluHK99-A0\" target=\"_blank\">here</a>.</p>
<ol>
<li>Determine if your Mac uses an M1 processor and check your macOS version<ol>
<li>Click on the Apple icon at the top left of the screen and
select \"About This Mac\". On the screen that pops up, check the
text next to \"Processor\" or \"Chip\". If the text includes
\"Apple\", you have an M1 processor in your Mac. Otherwise, if
the text includes \"Intel\", you have an x86 Mac.</li>
<li>In the \"About This Mac\" window, double check that you are
running one of \"macOS Catalina\", \"macOS Big Sur\", or \"macOS
Monterey\". If you are using a different version of macOS, you
will likely need to use the Khoury Virtual Desktops
Infrastructure (VDI).</li></ol></li>
<li>Install Homebrew<ol>
<li>Open the Terminal app, either by searching for it or via
opening Finder and selecting Go -&gt; Utilities in the menu bar,
and opening Terminal in that folder.</li>
<li>Go to <a href=\"https://brew.sh\">brew.sh</a> and copy-paste the
command starting with @('/bin/bash') on the top of that page
into a Terminal window, then press enter. You only need to run that
single command, and can safely ignore the other instructions on
Homebrew's website. You may need to enter your password one or more
times throughout the process.</li>
</ol></li>
<li>Tap and install ACL2s<ol>
<li>Run <code>brew tap mister-walter/acl2s</code> and then <code>brew install acl2s --force-bottle</code> inside of Terminal.</li></ol></li>
<li>Install Java<ol>
<li>Download and install Java 17 or 18. The easiest way to do this is to go to <a href=\"https://www.oracle.com/java/technologies/downloads/#jdk17-mac\">this link</a>
and download either the Arm64 DMG installer (if you are on a M1
Mac) or the x64 DMG installer. Then, open the DMG and run the
installer inside of it.</li></ol></li>
<li>Install Eclipse<ol>
<li>Download the Eclipse version appropriate for your machine: <a href=\"https://www.eclipse.org/downloads/download.php?file=/eclipse/downloads/drops4/R-4.25-202208311800/eclipse-platform-4.25-macosx-cocoa-aarch64.dmg&amp;r=1\">M1
Mac</a>
or <a href=\"https://www.eclipse.org/downloads/download.php?file=/eclipse/downloads/drops4/R-4.25-202208311800/eclipse-platform-4.25-macosx-cocoa-x86_64.dmg&amp;r=1\">x86
Mac</a>.</li>
<li>Open the downloaded file and click and drag the Eclipse icon
  into your Applications folder.</li>
<li><b>If you already have Eclipse installed</b>, you should still
install the version of Eclipse we provide here. If you need your
existing Eclipse install for another class, you can install Eclipse
for this class by dragging the Eclipse icon into a different folder
(for example, a folder on your Desktop) rather than Applications.</li>
</ol></li>
<li>Install the ACL2s Eclipse Plugin<ol>
<li>Open Eclipse, either by searching for it or via opening Finder
and selecting Go &rarr; Applications in the menu bar, and opening
Eclipse in that folder.</li>
<li>Select the folder that you want to keep all of your CS2800 ACL2
files in. You can use the default choice if you like. You may
also want to check the box that says \"Use this as the default
and do not ask again\". Then, click \"Launch\".</li>
<li>In the menu bar, click on Help &rarr; Install New Software...</li>
<li>Click on \"Add...\" in the screen that comes up. In the resulting
window, enter @('ACL2s') next to \"Name:\" and
@('http://cs2800.atwalter.com/p2') next to \"Location\". Then, click
\"Add\", which will close the pop-up.</li>
<li>The middle of the window should now show \"ACL2s Plugin Update
Site\". Click on the checkbox to the left of it and click \"Next&gt;\"
at the bottom of the window.</li>
<li>In the next window, click \"Finish\" at the bottom right of the
screen. If a pop-up appears that says \"Trust\" at the top and has two entries in a table at the top, click \"Select All\" and then \"Trust Selected\" at the bottom.</li>
<li>After the installation is complete, Eclipse will ask you if you
would like to restart Eclipse. Select \"Restart
Now\". This will close Eclipse and reopen it.</li></ol></li>
<li>Get started with Eclipse by working through the @(see acl2s-tutorial). </li>
</ol>
")

(defxdoc acl2s-installation-linux
  :parents (acl2s-installation)
  :short "Installation instructions for ACL2s on Linux"
  :long
  "
<h3 id=\"requirements\">Requirements</h3>
<ul>
<li>At least 5GB of free hard drive space</li>
<li>At least 4GB of RAM</li>
<li>An Intel or AMD processor</li>
</ul>
<h3 id=\"instructions\">Instructions</h3>
<p>These instructions are known to work on Ubuntu 20.04, and may work on
other platforms as well. If you run into any issues, feel free to
reach out to Drew.</p>
<ol>
<li>Ensure the following software is installed on your machine. If not,
install using your Linux distribution's package manager.<ul>
<li>Java 11 or greater (OpenJDK is fine too) (@('openjdk-11-jre') or newer on Ubuntu)</li>
<li>@('git')</li>
<li>@('curl')</li>
<li>@('procps')</li>
<li>@('file')</li>
<li>\"Development tools\" (@('build-essential') on Ubuntu)</li></ul><ol>
<li>If you are on an older version of Ubuntu, you may need to install @('libswt-gtk-4-jni') and @('xutils-dev') as well.</li></ol></li>
<li>Install Homebrew<ol>
<li>Go to <a href=\"https://brew.sh\">brew.sh</a> and copy-paste the
command starting with @('/bin/bash') on the top of that page
into a terminal shell, then press enter. You only need to run that
single command, and can safely ignore the other instructions on
Homebrew's website. You may need to enter your password one or more
times throughout the process.</li>
</ol></li>
<li>Tap and install ACL2s<ol>
<li>Run <code>brew tap mister-walter/acl2s</code> and then <code>brew install acl2s --force-bottle</code> inside of a terminal. <b>Do not</b> follow any of Homebrew's suggestions regarding installing @('gcc').</li></ol></li>
<li>Install Eclipse<ol>
<li>Download <a href=\"https://www.eclipse.org/downloads/download.php?file=/eclipse/downloads/drops4/R-4.25-202208311800/eclipse-platform-4.25-linux-gtk-x86_64.tar.gz&amp;r=1\">Eclipse</a> and unpack it somewhere on your computer.</li>
<li>Run Eclipse by running <code>./eclipse/eclipse</code> from the directory
that you unpacked the Eclipse package inside of.</li>
<li>In the menu bar, click on Help &rarr; Install New Software...</li>
<li>Click on \"Add...\" in the screen that comes up. In the resulting
window, enter @('ACL2s') next to \"Name:\" and
@('http://cs2800.atwalter.com/p2') next to \"Location\". Then, click
\"Add\", which will close the pop-up.</li>
<li>The middle of the window should now show \"ACL2s Plugin Update
Site\". Click on the checkbox to the left of it and click \"Next&gt;\" 
at the bottom of the window.</li>
<li>In the next window, click \"Finish\" at the bottom right of the
screen. If a pop-up appears that says \"Trust\" at the top and has two entries in a table at the top, click \"Select All\" and then \"Trust Selected\" at the bottom.</li>
<li>After the installation is complete, Eclipse will ask you if you
would like to restart Eclipse. Select \"Restart
Now\". This will close Eclipse and reopen it.</li>
</ol></li>
<li>Get started with Eclipse by working through the @(see acl2s-tutorial). </li>
</ol>
")

(defxdoc acl2s-installation-faq
  :parents (acl2s-installation)
  :short "FAQ related to ACL2s installation"
  :long
  "
<h3>Running ACL2s on Khoury Virtual Desktops</h3>
If you're a Northeastern student, you can run ACL2s using the Khoury
Virtual Desktops Infrastructure (VDI). See the
<a href=\"https://www.khoury.northeastern.edu/systems/vdi/\" >
  documentation</a>. You have many options including using
an <a href=\"https://view.khoury.northeastern.edu/portal/webclient/index.html#/\"
> HTML client</a> that allows you to log into a virtual machine and
run ACL2s using a browser. Use your Khoury CS account credentials and
select \"CCIS-WINDOWS\"; then select \"Linux Lab\" and you will see a
Desktop. Use the file explorer and click on \"Other Locations\",
\"Computer\", \"bin\" and then \"acl2s\". Drap the acl2s icon to your
Desktop while holding \"Alt\" or \"Option\" (on Mac) and when you release
it, a menu will pop up;  select \"link here\" and you will have a direct
link to ACL2s in your Desktop. Double click on the acl2s icon in
your desktop and this will start ACL2s on your VM.


<h3>FAQ</h3>

If you are running into a problem on Windows that is not covered by
the below FAQ items, please try removing your WSL acl2s installation
and going back through the instructions, ensuring that the output that
you see matches that shown in the installation video linked to in the
installation instructions. <b>Note that this will remove all of the
data in the WSL installation, so be sure to backup any files inside it
that you want to keep.</b> You can remove your WSL Ubuntu installation
by running <code>wsl --unregister acl2s</code>. Then, follow the
installation instructions as normal, except that you do not need to
reinstall Xming if you already have it installed.

<h4>General FAQ</h4>
<ul class=\"morespace\">
  <li><span class=\"question\">Why can't I access the Khoury VDI system?</span><br/>Ensure that
    you are connected to the Northeastern network, or are using the
    Northeastern VPN. You cannot connect to the VDI system from
    outside of Northeastern's network without using the VPN.<br/>
    Check that you are using your Khoury account credentials to log
    in, which may be different from your Northeastern account
    credentials.
  </li>
  <li><span class=\"question\">I already have a version of Eclipse installed for another
    class, can I use that?</span><br/>  We do not support using an
    existing Eclipse installation. If you are using Windows, the
    version of Eclipse that we install will be kept separate from
    Eclipse that is installed directly on Windows (which is the
    typical configuration). If you are using macOS, then when
    installing Eclipse, you can drag and drop it to a different
    location than your existing Eclipse installation (for example,
    install Eclipse into a folder on your Desktop instead of to
    Applications). These two Eclipses will coexist peacefully, and
    will not interfere with each other.
  </li>
</ul>
<h4>Windows FAQ</h4>
<ul class=\"morespace\">
  <li><span class=\"question\"> Double-clicking on @('run-acl2s.bat')
      doesn't open a window, or just
      sits there forever without opening a window!</span><br/>  Ensure
      that Xming is open and running (check your system tray by
      clicking on the ^ button on the bottom right corner of your
      screen). If it is, try exiting it (by right-clicking on the X
      icon and selecting \"Exit\") and reopening it by running the
      ACL2sXming xlaunch file. If that does not work, then ensure that
      Xming has permissions to use both private and public
      networks. You can do this by opening the Windows menu and
      searching for \"Allow an app through Windows Firewall\". In the
      window that comes up, scroll down to \"Xming X Server\" and ensure
      that the checkbox to the left of it and the two checkboxes to
      the right of it are all checked. You may need to click on the
      \"Change settings\" button at the top right of the window to be
      able to check the boxes.
  </li>
  <li><span class=\"question\">Double-clicking on the ACL2sXming file doesn't do
      anything!</span><br/>  If you have no other issues, this is
      OK. Double-clicking on the file will add an icon to your system
      tray (click on the ^ button near the bottom-right corner of your
      screen), but will not open a new window. If you are having
      problems, or if no X icon is added to your system tray, try
      downloading the ACL2sXming xlaunch file again, by right-clicking
      on the \"here\" link in the Windows installation instructions and
      choosing \"Save Link As...\".
  </li>
  <li><span class=\"question\">When I try to start a session, Eclipse tells me that an error
    occurred and that it could not start a session!</span><br/>Ensure that
    you ran the wsl.sh script as a non-root user (see the Windows
    install instructions for more information)
  </li>
  <li><span class=\"question\">In Windows, I can't find the folder that
      corresponds to my Eclipse workspace!</span><br/>
    <ol>
      <li>Get the workspace path you chose for Eclipse (File &rarr; Switch
      Workspace &rarr; Other in Eclipse, and the path there will be
      whatever workspace you are currently using), which should look
        something like <code>/mnt/c/...</code>.</li>
      <li>Take that path and replace the @('/mnt/c/')
      with @('C:\\'), and replace all forward
        slashes @('/') with back-slashes @('\\').</li>
      <li>Open the Windows run dialog (Windows key + R) and enter the
        updated path, and then press enter.</li>
    </ol>
    This will open the Windows folder that corresponds to your Eclipse
    workspace. You can then create a shortcut to this folder so it is
    easier to get to next time.
  </li>
  <li><span class=\"question\">@('wsl') works in an administrator terminal
      but not in a non-administrator one!</span><br/>
      Check that @('C:\\Windows\\system32') is in your Windows PATH. See
      <a href=\"https://www.architectryan.com/2018/03/17/add-to-the-path-on-windows-10/\">this page</a>
      for instructions on how to do this. Note that you may need to restart
      your computer after you modify your PATH for Windows to pick it up.
  </li>
</ul>

<h4>macOS FAQ</h4>
<ul class=\"morespace\">
  <li><span class=\"question\">When I run <code>brew install acl2s --force-bottle</code>
    , Homebrew tells me there is no bottle available!</span><br/>  If
    you are on a M1 Mac and you are not running macOS Monterey, you
    can either update to macOS Monterey and re-run the command, or you
    can build ACL2s from scratch, which will take a fair amount of
    time (at least an hour). To build ACL2s from scratch, run
    <code>brew install acl2s</code>.<br/>If you are on an Intel Mac and
    are running macOS Mojave or earlier, you can either update to
    macOS Catalina or later (if that is supported on your computer),
    or build ACL2s from scratch using the instructions above.
  </li>
  <li><span class=\"question\">Eclipse is using the dark theme, and I can't read any of the
  text!</span><br/>Go to Eclipse &rarr; Preferences &rarr; General &rarr; Appearance
  and select \"Light\" in the dropdown next to \"Theme\".</li>
  <li><span class=\"question\">When I try to start a session, Eclipse tells me that an error
    occurred and that it could not start a session!</span><br/>Ensure that
    the <code>brew install acl2s --force-bottle</code> command
    succeeded. Try running it again to ensure that it worked.
  </li>
  <li><span class=\"question\">When I try to run any of the brew commands, I get a message
      saying \"command not found: brew\".</span><br/>  When you install
      brew, it sometimes will print out a message saying \"Run these
      two commands in your terminal to add Homebrew to your PATH\". If
      you don't run the two commands, Homebrew will not function
      correctly. Assuming you are on a M1 Mac, try running the command
      <code>echo 'eval $(/opt/homebrew/bin/brew shellenv)' &gt;&gt; ~/.zprofile</code>
      and opening a new Terminal window.
  </li>
  <li><span class=\"question\">When I double click on the Eclipse application, nothing happens!</span><br/>Ensure that you have Java installed. To check, open
  Terminal (e.g. by searching for it in Spotlight) and run @('java -version'). If
  a version number is printed, you have Java installed.
  </li>
</ul>

")
