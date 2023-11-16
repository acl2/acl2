package org.neu.acl2.handproof.ui.editor.handler;

import java.net.MalformedURLException;
import java.net.URL;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.browser.IWebBrowser;
import org.eclipse.ui.browser.IWorkbenchBrowserSupport;

public class FAQActionHandler extends AbstractHandler {

	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
//		try {
//			BrowserView browser = (BrowserView)HandlerUtil.getActiveWorkbenchWindow(event).getActivePage().showView("org.neu.acl2.handproof.ui.browser.BrowserView");
//			browser.goToURL("http://checker.atwalter.com/faq");
//		} catch (PartInitException e) {
//			throw new ExecutionException("Couldn't create a browser to display the FAQ in!", e);
//		}
		
//		IWorkbenchWindow window = HandlerUtil.getActiveWorkbenchWindow(event);
//		BrowserView browser = new BrowserView();
//		try {
//			window.openPage(browser);
//			browser.goToURL("http://checker.atwalter.com/faq");
//		} catch (WorkbenchException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		}
		
				
		try {
			IWebBrowser browser = PlatformUI.getWorkbench().getBrowserSupport()
					.createBrowser(IWorkbenchBrowserSupport.AS_VIEW, "faqbrowser", "faqbrowser", "Some FAQs about the proof checker");
			browser.openURL(new URL("http://checker.atwalter.com/faq"));
		} catch (PartInitException e) {
			PlatformUI.getWorkbench().getDisplay().asyncExec(new Runnable() {
			    public void run() {
			    	MessageDialog.openError(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell(), "Couldn't create a browser to display the FAQ in!", "You should ensure that you either have a web browser installed that Eclipse knows about, or Webkit + its GTK bindings. You can check both by going to Window -> Preferences and filtering by 'Web Browser'.");
			    }
			});
			throw new ExecutionException("Couldn't create a browser to display the FAQ in!", e);
		} catch (MalformedURLException e) {
			throw new ExecutionException("Couldn't navigate to the FAQ page!", e);
		}
		return this;
	}

}
