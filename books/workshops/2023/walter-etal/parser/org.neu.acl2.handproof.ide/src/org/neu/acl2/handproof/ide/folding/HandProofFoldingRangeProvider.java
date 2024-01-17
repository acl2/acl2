package org.neu.acl2.handproof.ide.folding;

import org.eclipse.emf.common.util.TreeIterator;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.xtext.ide.editor.folding.DefaultFoldingRangeProvider;
import org.eclipse.xtext.ide.editor.folding.IFoldingRangeAcceptor;
import org.eclipse.xtext.parser.IParseResult;
import org.eclipse.xtext.resource.ILocationInFileProvider;
import org.eclipse.xtext.resource.XtextResource;
import org.eclipse.xtext.util.CancelIndicator;
import org.eclipse.xtext.util.ITextRegion;
import org.eclipse.xtext.util.PolymorphicDispatcher;
import org.neu.acl2.handproof.handProof.ContractCompletionSection;
import org.neu.acl2.handproof.handProof.DefineC;
import org.neu.acl2.handproof.handProof.ExportationSection;
import org.neu.acl2.handproof.handProof.Goal;
import org.neu.acl2.handproof.handProof.Proof;
import org.neu.acl2.handproof.handProof.ProofBody;
import org.neu.acl2.handproof.handProof.ProofDocument;
import org.neu.acl2.handproof.handProof.ProofList;
import org.neu.acl2.handproof.handProof.SExpression;

import com.google.inject.Inject;

public class HandProofFoldingRangeProvider extends DefaultFoldingRangeProvider {
	@Inject
	private ILocationInFileProvider locationInFileProvider;
	
//	private final PolymorphicDispatcher<Boolean> shouldProcessContentDispatcher = PolymorphicDispatcher.createForSingleTarget("shouldProcessContent2", this);
	private final PolymorphicDispatcher<Void> processContentDispatcher = PolymorphicDispatcher.createForSingleTarget("processContent", 3, 3, this);

	@Override
	protected void computeObjectFolding(XtextResource resource, IFoldingRangeAcceptor foldingRangeAcceptor,
			CancelIndicator cancelIndicator) {
		IParseResult parseResult = resource.getParseResult();
		if (parseResult != null) {
			EObject rootASTElement = parseResult.getRootASTElement();
			if (rootASTElement != null && rootASTElement instanceof ProofDocument) {
				if (cancelIndicator.isCanceled())
					return;
				ProofDocument doc = (ProofDocument) rootASTElement;
				for(EObject elt : doc.getProofsAndStatements()) {
					if (cancelIndicator.isCanceled())
						return;
					processContentDispatcher.invoke(elt, foldingRangeAcceptor, cancelIndicator);
				}
			}
		}
	}
	
	protected void processContent(EObject object, IFoldingRangeAcceptor acc, CancelIndicator ci) {
		foldFullText(object, acc, ci);
	}
	
	protected void processContent(Proof proof, IFoldingRangeAcceptor acc, CancelIndicator ci) {
		foldFullText(proof, acc, ci);
		if(proof.getExportation() != null) {
			foldFullText(proof.getExportation(), acc, ci);
		}
		if(proof.getCompletion() != null) {
			foldFullText(proof.getCompletion(), acc, ci);
		}
		if(proof.getContext() != null) {
			foldFullText(proof.getContext(), acc, ci);
			// TODO
		}
		if(proof.getDerivedContext() != null) {
			foldFullText(proof.getDerivedContext(), acc, ci);
			// TODO
		}
		if(proof.getGoal() != null) {
			foldFullText(proof.getGoal(), acc, ci);
		}
		if(proof.getBody() != null) {
			processContentDispatcher.invoke(proof.getBody(), acc, ci);
		}
	}
	
	protected void processContent(ProofList proofList, IFoldingRangeAcceptor acc, CancelIndicator ci) {
		for(Proof proof : proofList.getProofs()) {
			if (ci.isCanceled())
				return;
			processContentDispatcher.invoke(proof, acc, ci);
		}
	}
	
	protected void processContent(ProofBody proofBody, IFoldingRangeAcceptor acc, CancelIndicator ci) {
		// TODO
	}
	
	protected void foldFullText(EObject object, IFoldingRangeAcceptor acc, CancelIndicator ci) {
		ITextRegion region = locationInFileProvider.getFullTextRegion(object);
		acc.accept(region.getOffset(), region.getLength(), locationInFileProvider.getSignificantTextRegion(object));
	}
	
//	@Override
//	protected boolean shouldProcessContent(EObject object) {
//		return this.shouldProcessContentDispatcher.invoke(object);
//	}
//	
//	protected boolean shouldProcessContent2(EObject object) {
//		return true;
//	}
//	
//	protected boolean shouldProcessContent2(DefineC object) {
//		return false;
//	}
//	
//	protected boolean shouldProcessContent2(SExpression object) {
//		return false;
//	}
//	
//	protected boolean shouldProcessContent2(ExportationSection o) {
//		return false;
//	}
//	
//	protected boolean shouldProcessContent2(ContractCompletionSection o) {
//		return false;
//	}
//	
//	protected boolean shouldProcessContent2(Goal o) {
//		return false;
//	}

}
