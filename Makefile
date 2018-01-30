TEXLIVEONFLY := $(shell command -v texliveonfly 2> /dev/null)

DOC := $(foreach dir,$(dir $(wildcard doc/*/main.tex)),$(shell basename $(dir)))
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
			-a "-pdflatex=pdflatex                    \
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
	tlmgr install   \
		luatex        \
		biber         \
		latexmk       \
		texliveonfly  \
		greek-fontenc \
		textgreek     \
		babel         \
		babel-greek   \
		babel-english
endif

fira-sans:
	wget https://github.com/carrois/Fira/archive/master.zip
	unzip master.zip
	sudo mkdir -p /usr/share/fonts/opentype/fira_code
	sudo mkdir -p /usr/share/fonts/opentype/fira_mono
	sudo mkdir -p /usr/share/fonts/opentype/fira_sans
	sudo cp Fira-master/Fira_Code_3_2/Fonts/FiraCode_OTF_32/* /usr/share/fonts/opentype/fira_code
	sudo cp Fira-master/Fira_Mono_3_2/Fonts/FiraMono_OTF_32/* /usr/share/fonts/opentype/fira_mono
	sudo cp Fira-master/Fira_Sans_4_2/Fonts/FiraSans_OTF_4203/Normal/Roman/* /usr/share/fonts/opentype/fira_sans
	sudo cp Fira-master/Fira_Sans_4_2/Fonts/FiraSans_OTF_4203/Normal/Italic/* /usr/share/fonts/opentype/fira_sans

.phony: setup fira-sans
