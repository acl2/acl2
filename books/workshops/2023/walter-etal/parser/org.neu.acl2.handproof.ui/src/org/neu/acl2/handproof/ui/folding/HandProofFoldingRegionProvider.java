package org.neu.acl2.handproof.ui.folding;

import java.util.Collection;

import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.xtext.ui.editor.folding.DefaultFoldingRegionProvider;
import org.eclipse.xtext.ui.editor.folding.FoldedPosition;
import org.eclipse.xtext.ui.editor.folding.IFoldingRegionAcceptor;
import org.eclipse.xtext.ui.editor.model.IXtextDocument;
import org.eclipse.xtext.util.ITextRegion;
import org.eclipse.xtext.util.PolymorphicDispatcher;
import org.neu.acl2.handproof.handProof.OptionallyDottedSExpList;
import org.neu.acl2.handproof.handProof.OptionallyDottedSExpListExpr;
import org.neu.acl2.handproof.handProof.SExpList;
import org.neu.acl2.handproof.handProof.SExpression;
import org.neu.acl2.handproof.handProof.Symbol;

public class HandProofFoldingRegionProvider extends DefaultFoldingRegionProvider {
	
	private final PolymorphicDispatcher<Void> handProofComputeObjectFoldingDispatcher = PolymorphicDispatcher.createForSingleTarget("handProofComputeObjectFolding", 3, 3, this);
	private final PolymorphicDispatcher<Boolean> handProofShouldProcessContentDispatcher = PolymorphicDispatcher.createForSingleTarget("handProofShouldProcessContent", 1, 1, this);

	@Override
	protected IFoldingRegionAcceptor<ITextRegion> createAcceptor(IXtextDocument xtextDocument,
			Collection<FoldedPosition> foldedPositions) {
		return new HandProofFoldingRegionAcceptor(xtextDocument, foldedPositions);
	}

	@Override
	protected void computeObjectFolding(EObject eObject, IFoldingRegionAcceptor<ITextRegion> foldingRegionAcceptor,
			boolean initiallyFolded) {
		this.handProofComputeObjectFoldingDispatcher.invoke(eObject, foldingRegionAcceptor, initiallyFolded);
	}
	
	protected void handProofComputeObjectFolding(EObject eObject, IFoldingRegionAcceptor<ITextRegion> foldingRegionAcceptor,
			boolean initiallyFolded) {
		super.computeObjectFolding(eObject, foldingRegionAcceptor, initiallyFolded);
	}
	
	@Override
	protected boolean shouldProcessContent(EObject object) {
		return this.handProofShouldProcessContentDispatcher.invoke(object);
	}
		
	protected boolean handProofShouldProcessContent(EObject object) {
		return true;
	}
	
	private boolean isImplicationSymbol(SExpression expr) {
		if(expr instanceof Symbol) {
			String value = ((Symbol)expr).getValue();
			return "=>".equals(value) || "implies".equals(value);
		}
		return false;
	}
	
	private boolean bodyIsImplication(EList<SExpression> body) {
		if(!body.isEmpty() && isImplicationSymbol(body.get(0))) {
			return true;
		}
		return false;
	}
	
	protected boolean handProofShouldProcessContent(SExpList object) {
		return bodyIsImplication(object.getBody());
	}
	
	protected boolean handProofShouldProcessContent(OptionallyDottedSExpList object) {
		return bodyIsImplication(object.getBody());
	}
	
	protected boolean handProofShouldProcessContent(OptionallyDottedSExpListExpr object) {
		return handProofShouldProcessContent(object.getList());
	}
	
	protected boolean handProofShouldProcessContent(SExpression object) {
		return false;
	}


}
