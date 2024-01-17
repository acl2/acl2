package org.neu.acl2.handproof.ui.validation;

import org.apache.log4j.Logger;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.PlatformUI;
import org.neu.acl2.handproof.validation.IValidationMessageHandler;

import com.google.inject.Inject;

public class EclipseValidationMessageHandler implements IValidationMessageHandler {
	@Inject
	CheckerOutputStorage checkerOutput;
	
	@Override
	public void handleError(String title, String message) {
		checkerOutput.onOutput(title + "\n" + message);
		Logger.getLogger(this.getClass()).error(title + ": " + message);
		PlatformUI.getWorkbench().getDisplay().asyncExec(new Runnable() {
		    public void run() {
		    	MessageDialog.openError(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell(), title, message);
		    }
		});
	}

	@Override
	public void handleWarning(String title, String message) {
		Logger.getLogger(this.getClass()).warn(title + ": " + message);
	}

	@Override
	public void handleInfo(String title, String message) {
		Logger.getLogger(this.getClass()).info(title + ": " + message);
	}
	
	@Override
	public void handleOutput(String content) {
		checkerOutput.onOutput(content);
	}
}
