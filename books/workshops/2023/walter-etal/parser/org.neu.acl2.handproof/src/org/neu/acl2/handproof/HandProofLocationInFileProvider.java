package org.neu.acl2.handproof;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.xtext.nodemodel.ICompositeNode;
import org.eclipse.xtext.nodemodel.INode;
import org.eclipse.xtext.nodemodel.impl.InternalNodeModelUtils;
import org.eclipse.xtext.nodemodel.util.NodeModelUtils;
import org.eclipse.xtext.resource.DefaultLocationInFileProvider;
import org.eclipse.xtext.util.ITextRegion;
import org.eclipse.xtext.util.PolymorphicDispatcher;
import org.eclipse.xtext.util.TextRegion;
import org.neu.acl2.handproof.handProof.Goal;
import org.neu.acl2.handproof.handProof.OptionallyDottedSExpList;
import org.neu.acl2.handproof.handProof.Proof;
import org.neu.acl2.handproof.handProof.SExpList;
import org.neu.acl2.handproof.handProof.SExpression;

/**
 * We provide a custom override of this class because we want to control:
 * - what XText shows when a region is folded
 * - what XText highlights when something is clicked on in the outline view
 * Both of these are determined by the output of getSignificantTextRegion, so we can just override that!
 * @author drew
 *
 */
public class HandProofLocationInFileProvider extends DefaultLocationInFileProvider {
	private static class MyNodeModelUtils extends InternalNodeModelUtils {
		public static int[] myComputeLineBreaks(String str) {
			return computeLineBreaks(str);
		}
	}
	private final PolymorphicDispatcher<ITextRegion> significantTextRegionDispatcher = PolymorphicDispatcher.createForSingleTarget("significantTextRegion", this);

	@Override
	public ITextRegion getSignificantTextRegion(EObject obj) {
		return significantTextRegionDispatcher.invoke(obj);
	}
	
	public ITextRegion significantTextRegion(EObject obj) {
		return super.getSignificantTextRegion(obj);
	}

	// The significantTextRegion for an S-expression should just be its first line.
	public ITextRegion significantTextRegion(SExpression obj) {
		ICompositeNode actualNode = NodeModelUtils.findActualNodeFor(obj);
		int[] lineBreaks = MyNodeModelUtils.myComputeLineBreaks(actualNode.getText());
		if(lineBreaks.length > 0) {
			return new TextRegion(actualNode.getOffset(), lineBreaks[0] > 0 ? lineBreaks[0] - 1 : lineBreaks[0]);
		}
		return super.getSignificantTextRegion(obj);
	}

	public ITextRegion significantTextRegion(SExpList obj) {
		ICompositeNode actualNode = NodeModelUtils.findActualNodeFor(obj);
		int[] lineBreaks = MyNodeModelUtils.myComputeLineBreaks(actualNode.getText());
		if(lineBreaks.length > 0) {
			return new TextRegion(actualNode.getOffset(), lineBreaks[0] > 0 ? lineBreaks[0] - 1 : lineBreaks[0]);
		}
		return super.getSignificantTextRegion(obj);
	}
	
	public ITextRegion significantTextRegion(Proof proof) {
		return significantTextRegion(proof.getHeader());
	}
	
	public ITextRegion significantTextRegion(Goal goal) {
		ICompositeNode actualNode = NodeModelUtils.findActualNodeFor(goal);
		INode child = actualNode.getFirstChild();
		// TODO: null checks for the above
		return new TextRegion(child.getOffset(), child.getLength());
	}
}
