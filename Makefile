setup: $(HOME)/texlive

.phony: setup

$(HOME)/texlive:
	curl -L http://mirror.ctan.org/systems/texlive/tlnet/install-tl-unx.tar.gz | tar xz -C $HOME
	cd $HOME/install-tl-*;\
		yes i | ./install-tl --profile=$(TRAVIS_BUILD_DIR)/texlive.profile
