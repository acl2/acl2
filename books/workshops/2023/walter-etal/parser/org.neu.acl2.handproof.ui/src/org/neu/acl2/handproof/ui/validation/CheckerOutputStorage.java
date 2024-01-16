package org.neu.acl2.handproof.ui.validation;

import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.xtext.ui.editor.XtextEditor;
import org.neu.acl2.handproof.ui.views.ProofCheckerOutputView;

import com.google.inject.Singleton;

@Singleton
public class CheckerOutputStorage {
	
	private XtextEditor editor;
	
	public void setEditor(XtextEditor editor) {
		this.editor = editor;
	}
	
	public void startValidation() {
		IWorkbenchPage page = this.editor.getSite().getPage();
		Display.getDefault().asyncExec(() -> {
			if(this.editor != null) {
				try {
					ProofCheckerOutputView view = (ProofCheckerOutputView) page.showView("org.neu.acl2.handproof.ui.views.ProofCheckerOutputView");
					view.setContent("Validation in progress...");
				} catch (PartInitException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		});
	}
	
	public void onOutput(String output) {
		IWorkbenchPage page = this.editor.getSite().getPage();
		Display.getDefault().asyncExec(() -> {
			if(this.editor != null) {
				try {
					ProofCheckerOutputView view = (ProofCheckerOutputView) page.showView("org.neu.acl2.handproof.ui.views.ProofCheckerOutputView");
					view.setContent(output);
				} catch (PartInitException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		});
	}

}
