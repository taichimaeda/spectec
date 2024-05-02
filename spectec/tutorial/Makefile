PAPER = tutorial
TEX = $(wildcard *.tex)

.PHONY: all clean

all: $(PAPER).pdf

$(PAPER).pdf: $(TEX)
	pdflatex $(PAPER)
	pdflatex $(PAPER)

clean:
	rm -f *.aux *.bbl *.blg *.log *.out $(PAPER).pdf

