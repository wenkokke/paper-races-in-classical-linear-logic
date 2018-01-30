TEXLIVEONFLY := $(shell command -v texliveonfly 2> /dev/null)
LATEXOPTIONS := "-pdflatex=lualatex -pdf -outdir=../../_build -latexoption=-interaction=nonstopmode -latexoption=-halt-on-error"


setup:
ifndef TEXLIVEONFLY
# install texlive basic
	curl -L http://mirror.ctan.org/systems/texlive/tlnet/install-tl-unx.tar.gz | tar xz -C $(HOME)
	cd $(HOME)/install-tl-*;\
		yes i | ./install-tl --profile=$(TRAVIS_BUILD_DIR)/texlive.profile

# install texliveonfly, luatex, and latexmk
	tlmgr install \
		luatex      \
		latexmk     \
		texliveonfly
endif

.phony: setup
