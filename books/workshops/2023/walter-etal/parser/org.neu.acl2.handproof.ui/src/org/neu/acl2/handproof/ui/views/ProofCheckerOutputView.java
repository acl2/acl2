package org.neu.acl2.handproof.ui.views;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.swt.SWT;
import javax.inject.Inject;

import org.eclipse.jface.text.TextViewer;

public class ProofCheckerOutputView extends ViewPart {

	/**
	 * The ID of the view as specified by the extension.
	 */
	public static final String ID = "org.neu.acl2.handproof.ui.views.ProofCheckerOutputView";

	@Inject IWorkbench workbench;
	
	private TextViewer viewer;
	
	private AsciiColorizer asciiColorizer = new AsciiColorizer();
	 

//	class ViewLabelProvider extends LabelProvider implements ITableLabelProvider {
//		@Override
//		public String getColumnText(Object obj, int index) {
//			return getText(obj);
//		}
//		@Override
//		public Image getColumnImage(Object obj, int index) {
//			return getImage(obj);
//		}
//		@Override
//		public Image getImage(Object obj) {
//			return workbench.getSharedImages().getImage(ISharedImages.IMG_OBJ_ELEMENT);
//		}
//	}

	@Override
	public void createPartControl(Composite parent) {
		viewer = new TextViewer(parent, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);

//	    viewer.setLabelProvider(new ViewLabelProvider());

		// Create the help context id for the viewer's control
		workbench.getHelpSystem().setHelp(viewer.getControl(), "org.neu.acl2.handproof.ui.viewer");
		getSite().setSelectionProvider(viewer);
	}
	
	public void setContent(String content) {
		asciiColorizer.process(content);
		this.viewer.getTextWidget().setText(asciiColorizer.getProcessedContent());
		this.viewer.getTextWidget().setStyleRanges(asciiColorizer.getStyles());
	}

	@Override
	public void setFocus() {
		viewer.getControl().setFocus();
	}
}
