package org.neu.acl2.handproof.ui.editor.handler;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.xtext.ui.editor.XtextEditor;
import org.eclipse.xtext.ui.editor.handler.ValidateActionHandler;
import org.eclipse.xtext.ui.editor.utils.EditorUtils;
import org.neu.acl2.handproof.ui.validation.CheckerOutputStorage;
import org.neu.acl2.handproof.validation.IValidationFilePathProvider;

import com.google.inject.Inject;

public class MyValidateActionHandler extends ValidateActionHandler {
	@Inject
	private CheckerOutputStorage checkerOutput;
	
	@Inject
	private IValidationFilePathProvider validationFilePathProvider;
	
	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		checkerOutput.startValidation();
		XtextEditor xtextEditor = EditorUtils.getActiveXtextEditor(event);
		validationFilePathProvider.setPath(xtextEditor.getResource().getParent().getLocation().toOSString());
		return super.execute(event);
	}
}
