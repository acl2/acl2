package org.neu.acl2.handproof.ui.wizards;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.dialogs.WizardNewFileCreationPage;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.wizards.newresource.BasicNewResourceWizard;

public class NewProofFileWizard extends Wizard implements INewWizard {
	
	private IWorkbench workbench;
	private IStructuredSelection selection;
	private WizardNewFileCreationPage mainPage;
	
	@Override
	public void addPages() {
		super.addPages();
		mainPage = new WizardNewFileCreationPage("newFilePage1", this.selection);
		mainPage.setFileExtension("proof");
		mainPage.setTitle("New proof file");
		mainPage.setDescription("Create a new proof file. The .proof file extension will automatically be added.");
		super.addPage(mainPage);		
	}

	@Override
	public void init(IWorkbench workbench, IStructuredSelection selection) {
		this.workbench = workbench;
		this.selection = selection;
	}

	@Override
	public boolean performFinish() {
		IFile file = mainPage.createNewFile();
		if (file == null) {
			return false;
		}
		
		IWorkbenchWindow activeWorkbenchWindow = this.workbench.getActiveWorkbenchWindow();
		BasicNewResourceWizard.selectAndReveal(file, activeWorkbenchWindow);
		try {
			if(activeWorkbenchWindow != null) {
				IWorkbenchPage activePage = activeWorkbenchWindow.getActivePage();
				if(activePage != null) {
					IDE.openEditor(activePage, file, true);
				}
			}
		} catch(PartInitException e) {
			MessageDialog.openError(getShell(), "Error opening new file in editor", e.getMessage());
		}
		
		return true;
	}

}
