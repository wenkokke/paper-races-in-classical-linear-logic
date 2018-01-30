TEXLIVEONFLY := $(shell command -v texliveonfly 2> /dev/null)

DOC := $(foreach dir,$(dir $(wildcard doc/*/main.tex)),$(shell gbasename $(dir)))
PDF := $(addprefix _build/,$(addsuffix .pdf,$(DOC)))

all: _build/release.zip

_build/release.zip: $(PDF)
	zip $@ $^

_build/:
	mkdir -p _build/

define DOC_template
_build/$(1).pdf: _build/
	cd doc/$(1);\
		$(TEXLIVEONFLY)                             \
			-c latexmk                                \
			-a "-pdflatex=lualatex                    \
			    -pdf                                  \
				  -outdir=../../_build                  \
	        -latexoption=-interaction=nonstopmode \
	        -latexoption=-halt-on-error           \
	        -jobname=$(1)"                        \
			main.tex

.phony: _build/$(1).pdf
endef

$(foreach doc,$(DOC),$(eval $(call DOC_template,$(doc))))

setup:
ifndef TEXLIVEONFLY
	curl -L http://mirror.ctan.org/systems/texlive/tlnet/install-tl-unx.tar.gz | tar xz -C $(HOME)
	cd $(HOME)/install-tl-*;\
		yes i | ./install-tl --profile=$(TRAVIS_BUILD_DIR)/texlive.profile
	tlmgr install \
		luatex      \
		biber       \
		latexmk     \
		texliveonfly
endif

.phony: setup
