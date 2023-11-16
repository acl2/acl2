package org.neu.acl2.handproof.web;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.xtext.web.server.IServiceResult;
import org.eclipse.xtext.xbase.lib.util.ToStringBuilder;

public class CodeFoldingResult implements IServiceResult {
	public static class Region {
		private final int offset;

		private final int length;
		
		private final int placeholderRegionOffset;
		
		private final int placeholderRegionLength;
		

		public Region(int offset, int length, int placeholderRegionOffset, int placeholderRegionLength) {
			this.offset = offset;
			this.length = length;
			this.placeholderRegionOffset = placeholderRegionOffset;
			this.placeholderRegionLength = placeholderRegionLength;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + this.offset;
			result = prime * result + this.length;
			result = prime * result + this.placeholderRegionOffset;
			return prime * result + this.placeholderRegionLength;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			CodeFoldingResult.Region other = (CodeFoldingResult.Region) obj;
			if (other.offset != this.offset)
				return false;
			if (other.length != this.length)
				return false;
			if (other.placeholderRegionOffset != this.placeholderRegionOffset)
				return false;
			if (other.placeholderRegionLength != this.placeholderRegionLength)
				return false;
			return true;
		}

		@Override
		public String toString() {
			ToStringBuilder b = new ToStringBuilder(this);
			b.singleLine();
			b.add("offset", this.offset);
			b.add("length", this.length);
			b.add("replacement offset", this.placeholderRegionOffset);
			b.add("replacement length", this.placeholderRegionLength);
			return b.toString();
		}

		public int getOffset() {
			return offset;
		}

		public int getLength() {
			return length;
		}
		
		public int getplaceholderRegionOffset() {
			return placeholderRegionOffset;
		}

		public int getplaceholderRegionLength() {
			return placeholderRegionLength;
		}
	}

	private final List<CodeFoldingResult.Region> regions = new ArrayList<>();

	@Override
	public int hashCode() {
		return 31 * 1 + ((this.regions == null) ? 0 : this.regions.hashCode());
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		CodeFoldingResult other = (CodeFoldingResult) obj;
		if (this.regions == null) {
			if (other.regions != null)
				return false;
		} else if (!this.regions.equals(other.regions))
			return false;
		return true;
	}

	@Override
	public String toString() {
		ToStringBuilder b = new ToStringBuilder(this);
		b.add("regions", this.regions);
		return b.toString();
	}

	public List<CodeFoldingResult.Region> getRegions() {
		return regions;
	}
}
