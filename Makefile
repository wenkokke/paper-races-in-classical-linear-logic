MAINTEX := $(realpath doc/coordination2019/main.tex)
MAINDIR := $(realpath $(dir $(MAINTEX)))
MAINPDF := $(MAINTEX:.tex=.pdf)
SOURCES := $(realpath $(shell find $(MAINDIR) -type f -and \( -name '*.tex' -or -name '*.bib' \)))

default: build

.PHONY: build
build: $(MAINPDF)

.PHONY: watch
watch:
	@fswatch -o $(SOURCES) | xargs -n1 -I{} make

.PHONY: clean
clean:
	@cd $(dir $(MAINTEX)) && latexmk -C $(notdir $(MAINTEX))

$(MAINPDF): $(SOURCES)
	@cd $(dir $(MAINTEX)) && latexmk -pdf $(notdir $(MAINTEX)) -halt-on-error
