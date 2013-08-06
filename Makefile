default : notes.pdf

notes.tex : notes.lagda Vec.lagda STLC.lagda
	lhs2TeX --agda notes.lagda > notes.tex

notes.aux : notes.tex
	latex notes

notes.blg : notes.aux notes.bib
	bibtex notes

notes.dvi : notes.tex notes.blg
	latex notes
	latex notes

notes.pdf : notes.tex notes.blg
	latex notes
	pdflatex notes
