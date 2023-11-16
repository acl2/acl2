package org.neu.acl2.handproof.ui.folding;

import java.util.Collection;

import org.eclipse.jface.text.IRegion;
import org.eclipse.xtext.ui.editor.folding.DefaultFoldingRegionAcceptor;
import org.eclipse.xtext.ui.editor.folding.FoldedPosition;
import org.eclipse.xtext.ui.editor.model.IXtextDocument;
import org.eclipse.xtext.util.ITextRegion;

public class HandProofFoldingRegionAcceptor extends DefaultFoldingRegionAcceptor {

	public HandProofFoldingRegionAcceptor(IXtextDocument document, Collection<FoldedPosition> result) {
		super(document, result);
		// TODO Auto-generated constructor stub
	}
	
	@Override
	protected FoldedPosition newFoldedPosition(IRegion region, ITextRegion significantRegion) {
		if (region == null)
			return null;
		if (significantRegion != null)
			return new HandProofFoldedPosition(region.getOffset(), region.getLength(), significantRegion.getOffset() - region.getOffset(), significantRegion.getLength());
		return new HandProofFoldedPosition(region.getOffset(), region.getLength(), HandProofFoldedPosition.UNSET, HandProofFoldedPosition.UNSET);
	}

}
