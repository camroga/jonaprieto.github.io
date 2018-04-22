agda := $(wildcard src/*.lagda)
agdai := $(wildcard src/*.agdai)
originalmd := $(wildcard src/*.md)
ipeImages := $(wildcard src/ipe-images/*.ipe)
latexitImages := $(wildcard src/latexit-images/*.png)

markdownOrig := $(subst src/,_posts/,$(originalmd))
markdownAgda := $(subst src/,_posts/,$(subst .lagda,.md,$(agda)))
ipeImagesPNG     := $(subst src/ipe-images/,assets/ipe-images/,$(subst .ipe,.png,$(ipeImages)))
latexitImagesPNG := $(subst src/latexit-images/,assets/latexit-images/,$(latexitImages))

#
all: _posts/ $(markdownOrig) $(markdownAgda) $(ipeImagesPNG) $(latexitImagesPNG)

_posts/ :
	rm -Rf -d _posts
	mkdir -p _posts

_posts/%.md : src/%.md
	cp $< $@

_posts/%.md : src/%.lagda
	agda2html --verbose --link-to-agda-stdlib --jekyll-root=_posts/ -i $< -o $@

assets/ipe-images/%.png : src/ipe-images/%.ipe
	iperender -png -resolution 400 $< $@

assets/latexit-images/%.png : src/latexit-images/%.png
	cp $< $@

observr:
	observr .observr
# serve website using jekyll

serve:
	ruby -S bundle exec jekyll liveserve --force_polling --watch --verbose

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


.phony : push-sources
push-sources :
	- @jekyll build
	- @git checkout sources
	- @git add .
	- @git commit -am "[ notes ] changes on $(shell date +"%Y-%m-%d time:%H:%M.%S")."
	- @git push origin sources

.phony : push-master
push-master :
	- git checkout sources
	- jekyll build
	- $(eval MSG := $(shell bash -c 'read -p "Commit msg: " pwd; echo $$pwd'))
	- cd _site && \
		git checkout master\
		git add .\
		git commit -m "$(MSG)"\
		git push origin master


.phony : push
push :
	- make clobber
	- make
	- make just-push
	- jekyll algolia
