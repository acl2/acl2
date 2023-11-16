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

public class ProofFormatHelpActionHandler extends AbstractHandler {

	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {				
		try {
			IWebBrowser browser = PlatformUI.getWorkbench().getBrowserSupport()
					.createBrowser(IWorkbenchBrowserSupport.AS_VIEW, "formatbrowser", "formatbrowser", "A description of the proof format.");
			browser.openURL(new URL("http://checker.atwalter.com/proof_format"));
		} catch (PartInitException e) {
			PlatformUI.getWorkbench().getDisplay().asyncExec(new Runnable() {
			    public void run() {
			    	MessageDialog.openError(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell(), "Couldn't create a browser to display the proof format info in!", "You should ensure that you either have a web browser installed that Eclipse knows about, or Webkit + its GTK bindings. You can check both by going to Window -> Preferences and filtering by 'Web Browser'.");
			    }
			});
			throw new ExecutionException("Couldn't create a browser to display the proof format page in!", e);
		} catch (MalformedURLException e) {
			throw new ExecutionException("Couldn't navigate to the proof format page!", e);
		}
		return this;
	}

}
