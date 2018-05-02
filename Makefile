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
	rm -f $@
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

.phony: serve
serve:
	ruby -S bundle exec jekyll liveserve --force_polling --watch --incremental

# remove all auxiliary files
.phony: clean
clean:
ifneq ($(strip $(agdai)),)
	rm $(agdai)
endif



# remove all generated files
.phony: clobber
clobber: clean
	ruby -S bundle exec jekyll clean
ifneq ($(strip $(markdown)),)
	rm $(markdown)
endif
	rm -Rf _posts/

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

.PHONY : references
references : _bibliography/library.bib
	- @echo "==================================================================="
	-	@echo "====================== Generating References ======================"
	-	@echo "==================================================================="
	- @rm _bibliography/ref.bib
	- @cp  _bibliography/library.bib  _bibliography/library-temp.bib
	- sh _bibliography/fix-references.sh
	- biber --tool --output_align --output_indent=2 \
		--output_fieldcase=lower -w \
		--output-encoding=UTF-8 \
		--input-encoding=UTF-8 \
		--sortupper=true\
		--output-format=bibtex\
		--debug \
		-O=_bibliography/library-temp.bib _bibliography/library-temp.bib
		- sh _bibliography/fix-references.sh
	- @mv _bibliography/library-temp.bib _bibliography/ref.bib
	- @rm -f _bibliography/library-temp.bib.blg
	- @rm -f _bibliography/library-temp.bib-r
	-	@echo "========================== END ==================================="

.phony : push-sources
push-sources :
	- @git checkout sources
	- @git add --all
	- $(eval MSG := $(shell bash -c 'read -p "Commit msg: " pwd; echo $$pwd'))
	- @echo "==================================================================="
	-	@echo "======================= Pushing on SOURCES ========================"
	-	@echo "==================================================================="
	- @git commit -am "$(MSG)"
	- @git push origin sources

.phony: init-master
 init-master :
	- rm -Rf _site
	- mkdir  _site
	- cd _site && \
		git init && \
		git remote add origin http://github.com/jonaprieto/jonaprieto.github.io.git && \
		git pull origin master

.phony : push
push :
	- make push-sources
	- @echo "==================================================================="
	-	@echo "========================= Jekyll Building ========================="
	-	@echo "==================================================================="
	- @jekyll build
	- @if [[ -d "_site/.git" ]]; then \
			echo "===================================================================" &&\
	    echo "================ STATICS FILES: Pushing on MASTER =================" &&\
	    echo "===================================================================" &&\
	    cd _site && \
			git add --all && \
			git commit -m "[ notes ] changes on $(shell date +"%Y-%m-%d time:%H:%M.%S")." && \
			git push origin master;\
			cd .. && jekyll algolia; \
		else \
			echo "[!] run first:\n\t $$ make init-master"; \
		fi
