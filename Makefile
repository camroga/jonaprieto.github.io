agda := $(wildcard src/*.lagda)
agdai := $(wildcard src/*.agdai)
originalmd := $(wildcard src/*.md)
images := $(wildcard src/images/*.ipe)

markdownOrig := $(subst src/,_posts/,$(originalmd))
markdownAgda := $(subst src/,_posts/,$(subst .lagda,.md,$(agda)))
imagesPNG    := $(subst src/images/,assets/images/,$(subst .ipe,.png,$(images)))

#
all: _posts/ $(markdownOrig) $(markdownAgda) $(imagesPNG)

_posts/ :
	rm -Rf -d _post
	mkdir -p _posts

_posts/%.md : src/%.md
	cp $< $@

_posts/%.md : src/%.lagda
	agda2html --verbose --link-to-agda-stdlib --jekyll-root=_posts/ -i $< -o $@

assets/images/%.png : src/images/%.ipe
	iperender -png -resolution 200 $< $@

observr:
	observr .observr
# serve website using jekyll
serve:
	ruby -S bundle exec jekyll liveserve --watch

.phony: serve


# remove all auxiliary files
clean:
ifneq ($(strip $(agdai)),)
	rm $(agdai)
endif

.phony: clean


# remove all generated files
clobber: clean
	ruby -S bundle exec jekyll clean
ifneq ($(strip $(markdown)),)
	rm $(markdown)
endif
	rm -Rf _posts/

.phony: clobber


# install bundler, and gem dependencies
setup:
	ruby -S gem install bundler --no-ri --no-rdoc
	ruby -S bundle install

.phony: setup


# install agda, agda-stdlib, and agda2html
travis-setup:\
	$(HOME)/agda-master/\
	$(HOME)/agda-stdlib-master/\
	$(HOME)/agda2html-master/

.phony: travis-setup

$(HOME)/agda-master/:
	curl -L https://github.com/agda/agda/archive/master.zip -o $(HOME)/agda-master.zip
	unzip -qq $(HOME)/agda-master.zip -d $(HOME)
	cd $(HOME)/agda-master;\
		stack install --stack-yaml=stack-8.2.2.yaml

$(HOME)/agda-stdlib-master/:
	curl -L https://github.com/agda/agda-stdlib/archive/master.zip -o $(HOME)/agda-stdlib-master.zip
	unzip -qq $(HOME)/agda-stdlib-master.zip -d $(HOME)
	mkdir $(HOME)/.agda
	echo "standard-library" > $(HOME)/.agda/defaults
	echo "$(HOME)/agda-stdlib-master/standard-library.agda-lib" > $(HOME)/.agda/libraries

$(HOME)/agda2html-master/:
	curl -L https://github.com/wenkokke/agda2html/archive/master.zip -o $(HOME)/agda2html-master.zip
	unzip -qq $(HOME)/agda2html-master.zip -d $(HOME)
	cd $(HOME)/agda2html-master;\
		stack install


.PHONY : deploy
deploy :
	- jekyll algolia
	- make clobber
	- make
	- make serve

.phony : push
push :
	- jekyll algolia
	- make clobber
	- make
	- @git add .
	- @git commit -am "[ notes ] changes on $(shell date +"%Y-%m-%d time:%H:%M.%S")."
	- @git push origin master
