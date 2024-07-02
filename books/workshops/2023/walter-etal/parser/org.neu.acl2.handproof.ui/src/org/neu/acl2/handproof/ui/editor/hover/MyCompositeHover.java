package org.neu.acl2.handproof.ui.editor.hover;

import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.xtext.ui.editor.hover.DefaultCompositeHover;
import org.neu.acl2.handproof.validation.HandProofValidator;

import com.google.inject.Inject;

public class MyCompositeHover extends DefaultCompositeHover {
	
	@Inject
	private HandProofValidator validator;
	
	@Override
	public IRegion getHoverRegion(ITextViewer textViewer, int offset) {
		if(validator.isRunning()) {
			return null;
		}
		return super.getHoverRegion(textViewer, offset);
	}
}
