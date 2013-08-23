default : notes.pdf

chap1 : Vec.lagda Normal.lagda Proving.lagda NormT.lagda NormF.lagda

chap5 : IR.lagda IRDS.lagda IRIF.lagda

notes.tex : notes.lagda chap1 STLC.lagda Containers.lagda IxCon.lagda chap5 OTT.lagda
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
