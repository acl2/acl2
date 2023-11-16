package org.neu.acl2.handproof.ui.preferences;

import org.eclipse.jface.preference.FileFieldEditor;
import org.eclipse.xtext.ui.editor.preferences.LanguageRootPreferencePage;
import org.neu.acl2.handproof.ui.validation.ValidationPreferenceAccess;

public class HandProofRootPreferencePage extends LanguageRootPreferencePage {
	@Override
	protected void createFieldEditors() {
		super.createFieldEditors();
		addField(new FileFieldEditor(ValidationPreferenceAccess.PREF_PROVE_FILE_SH_PATH, "The path to the prove-file-sh script.", getFieldEditorParent()));
	}
	
}
