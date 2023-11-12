package org.neu.acl2.handproof.web;

import java.util.List;
import java.util.stream.Collectors;

import org.eclipse.xtext.ide.editor.folding.FoldingRange;
import org.eclipse.xtext.ide.editor.folding.IFoldingRangeProvider;
import org.eclipse.xtext.util.CancelIndicator;
import org.eclipse.xtext.web.server.model.AbstractCachedService;
import org.eclipse.xtext.web.server.model.IXtextWebDocument;

import com.google.inject.Inject;

// Heavily inspired by org.eclipse.xtext.ide.server.folding.FoldingRangeService
public class CodeFoldingService extends AbstractCachedService<CodeFoldingResult>{
	@Inject
	private IFoldingRangeProvider foldingRangeProvider;

	@Override
	public CodeFoldingResult compute(IXtextWebDocument doc, CancelIndicator cancelIndicator) {
		CodeFoldingResult result = new CodeFoldingResult();
		List<CodeFoldingResult.Region> regions = foldingRangeProvider.getFoldingRanges(doc.getResource(), cancelIndicator).stream()
			.map(range -> toFoldingRange(doc, range)).filter(range -> range.getOffset() > 0)
			.collect(Collectors.toList());
		result.getRegions().addAll(regions);
		return result;
	}
	
	protected CodeFoldingResult.Region toFoldingRange(IXtextWebDocument doc, FoldingRange range) {
		return new CodeFoldingResult.Region(
				range.getOffset(),
				range.getLength(),
				range.getVisualPlaceholderRegion().getOffset(),
				range.getVisualPlaceholderRegion().getLength());
	}

}
