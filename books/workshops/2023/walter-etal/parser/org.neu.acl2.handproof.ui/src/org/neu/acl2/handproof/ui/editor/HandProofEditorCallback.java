package org.neu.acl2.handproof.ui.editor;

import org.eclipse.xtext.ui.editor.IXtextEditorCallback;
import org.eclipse.xtext.ui.editor.XtextEditor;
import org.neu.acl2.handproof.ui.validation.CheckerOutputStorage;

import com.google.inject.Inject;

public class HandProofEditorCallback implements IXtextEditorCallback {
	
	@Inject
	CheckerOutputStorage checkerOutput;

	@Override
	public void beforeSetInput(XtextEditor xtextEditor) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void afterSetInput(XtextEditor xtextEditor) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void afterCreatePartControl(XtextEditor editor) {
		// TODO Auto-generated method stub
		checkerOutput.setEditor(editor);
		
	}

	@Override
	public void afterSave(XtextEditor editor) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void beforeDispose(XtextEditor editor) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public boolean onValidateEditorInputState(XtextEditor editor) {
		// TODO Auto-generated method stub
		return true;
	}

}
