
.PHONY: default
default:
	make homebrew
	make npm
	make macos-setup
	make agda2html


.PHONY: homebrew
homebrew :
	/usr/bin/ruby --version && gem install bundler jekyll
	/usr/bin/ruby -e "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install)"

.PHONY: npm
npm:
	brew install npm
	npm install --global gulp
	cd blog && bundle install


.PHONY: macos-setup
macos-setup: homebrew
	brew install ghc
	brew install agda
	brew install stack
  brew install cask
  brew cask install ipe
	pip3 install agda-pkg && apkg install standard-library

.PHONY: agda2html
agda2html:
	curl -L https://github.com/wenkokke/agda2html/archive/master.zip -o $(HOME)/agda2html-master.zip
	unzip -qq $(HOME)/agda2html-master.zip -d $(HOME)
	cd $(HOME)/agda2html-master && stack install

.PHONY: build
build :
  cd blog && bundle install
	cd blog && gulp build

.PHONY: run
run :
	cd blog && make run

.PHONY: commit
commit :
	cd blog && make commit

.PHONY: init-master
init-master :
	cd blog && make init-master

.PHONY: push-sources
push-sources :
	cd blog && make push-sources
