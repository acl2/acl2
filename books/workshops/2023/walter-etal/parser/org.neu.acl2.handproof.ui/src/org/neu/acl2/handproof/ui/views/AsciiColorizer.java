package org.neu.acl2.handproof.ui.views;

import java.nio.charset.StandardCharsets;
import java.util.LinkedList;

import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.widgets.Display;

import com.google.common.base.Ascii;

public class AsciiColorizer {
	
	private StyleRange[] styles;
	private String processedContent;
	
	private static Color[] colorMap = new Color[] {
		Display.getCurrent().getSystemColor(SWT.COLOR_BLACK),
		Display.getCurrent().getSystemColor(SWT.COLOR_RED),
		Display.getCurrent().getSystemColor(SWT.COLOR_GREEN),
		Display.getCurrent().getSystemColor(SWT.COLOR_DARK_YELLOW), // regular yellow is typically hard to see
		Display.getCurrent().getSystemColor(SWT.COLOR_BLUE),
		Display.getCurrent().getSystemColor(SWT.COLOR_MAGENTA),
		Display.getCurrent().getSystemColor(SWT.COLOR_CYAN),
		Display.getCurrent().getSystemColor(SWT.COLOR_WHITE)
	};
	
	private Color getColor(byte b1, byte b2) {
		if(b2 >= 0x30 && b2 <= 0x37) {
			return colorMap[b2-0x30];
		} else {
			return colorMap[0];
		}
	}
	
	public void process(String content) {
		int i = 0;
		int j = 0;
		byte[] bytes = content.getBytes();
		int len = bytes.length;
		byte[] outputBytes = new byte[len];
		int currentRangeStart = 0;
		Color currentRangeColor = colorMap[0];
		int controlCharsSeen = 0;
		LinkedList<StyleRange> range = new LinkedList<>();
		while(i < len) {
			switch(bytes[i]) {
				case Ascii.ESC:
					if(bytes[i+2] == 0x30) {
						range.add(new StyleRange(currentRangeStart-controlCharsSeen, i-currentRangeStart, currentRangeColor, null));
						i += 3;
						controlCharsSeen += 4;
					} else {
						currentRangeColor = getColor(bytes[i+2], bytes[i+3]);
						controlCharsSeen += 5;
						i += 4;
						currentRangeStart = i;
					}
					break;
				default:
					outputBytes[j] = bytes[i];
					j++;
					break;
			}
			i++;
		}
		
		this.styles = (StyleRange[]) range.toArray(new StyleRange[range.size()]);
		this.processedContent = new String(outputBytes, StandardCharsets.UTF_8);
	}
	
	public StyleRange[] getStyles() {
		return this.styles;
	}
	
	public String getProcessedContent() {
		return this.processedContent;
	}

}
