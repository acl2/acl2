.PHONY: all clean clean-all

all: ubdds.pdf ubdds-4up.pdf

ubdds.pdf: ubdds.tex
	pdflatex $< $@

ubdds-4up.ps: ubdds.ps
	psnup -nup 4 -l ubdds.ps > ubdds-4up.ps

ubdds-4up.pdf: ubdds-4up.ps
	ps2pdf ubdds-4up.ps ubdds-4up.pdf

ubdds.ps: ubdds.pdf
	pdf2ps ubdds.pdf ubdds.temp.ps
	psnup -1 -W128mm -H96mm -pletter ubdds.temp.ps ubdds.ps
	rm -f ubdds.temp.ps

clean:
	rm -f *.log *.dvi *.aux *.temp.* *.nav *.snm *.out *.toc *.vrb *~

clean-all: clean
	rm -f ubdds.pdf ubdds.ps ubdds-4up.ps ubdds-4up.pdf

