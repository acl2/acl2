.PHONY: all clean clean-all

all: translator.pdf translator-4up.pdf

translator.pdf: translator.tex
	pdflatex $< $@

translator-4up.ps: translator.ps
	psnup -nup 4 -l translator.ps > translator-4up.ps

translator-4up.pdf: translator-4up.ps
	ps2pdf translator-4up.ps translator-4up.pdf

translator.ps: translator.pdf
	pdf2ps translator.pdf translator.temp.ps
	psnup -1 -W128mm -H96mm -pletter translator.temp.ps translator.ps
	rm -f translator.temp.ps

clean:
	rm -f *.log *.dvi *.aux *.temp.* *.nav *.snm *.out *.toc *.vrb *~

clean-all: clean
	rm -f translator.pdf translator.ps translator-4up.ps translator-4up.pdf

