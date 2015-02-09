.PHONY: all clean clean-all

all: parser.pdf parser-4up.pdf

parser.pdf: parser.tex
	pdflatex $< $@

parser-4up.ps: parser.ps
	psnup -nup 4 -l parser.ps > parser-4up.ps

parser-4up.pdf: parser-4up.ps
	ps2pdf parser-4up.ps parser-4up.pdf

parser.ps: parser.pdf
	pdf2ps parser.pdf parser.temp.ps
	psnup -1 -W128mm -H96mm -pletter parser.temp.ps parser.ps
	rm -f parser.temp.ps

clean:
	rm -f *.log *.dvi *.aux *.temp.* *.nav *.snm *.out *.toc *.vrb *~

clean-all: clean
	rm -f parser.pdf parser.ps parser-4up.ps parser-4up.pdf

