srcNotesAgda := $(wildcard _src/notes/*.lagda)
srcNotesMd   := $(wildcard _src/notes/*.md)

mdNotesAgda  := $(subst _src/notes,_posts,$(subst .lagda,.md,$(srcNotesAgda)))
mdNotesMd    := $(subst _src/notes,_posts,$(srcNotesMd))

ipeImages    := $(wildcard _src/ipe-images/*.ipe)
ipeImagesPNG := $(subst _src/ipe-images/,assets/ipe-images/,$(subst .ipe,.png,$(ipeImages)))

all:  $(mdNotesAgda) \
      $(mdNotesMd) \
      $(ipeImagesPNG) \
      _posts/

_posts/ :
	- rm -Rf -d _posts
	- mkdir -p _posts

_posts/%.md : _src/notes/%.md
	- cp $< $@
  - @echo "==================================================================="

_posts/%.md : _src/notes/%.lagda
	- time agda2html --version
	- time agda2html --verbose --link-to-agda-stdlib --use-jekyll=_posts/ -i $< -o $@
	- gulp reload
  - @echo "==================================================================="

assets/ipe-images/%.png : _src/ipe-images/%.ipe
	iperender -png -resolution 400 $< $@

assets/latexit-images/%.png : _src/latexit-images/%.png
	cp $< $@

assets/%.png : _src/assets/%.png
	cp $< $@

# .phony: serve
# serve:
# 	ruby -S bundle exec jekyll liveserve -l --force_polling --watch --incremental --trace --verbose --future

.PHONY: run
run:
	gulp default --silent

# remove all auxiliary files
.phony: clean
clean:
	rm -Rf _posts/
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
.phony: setup
setup:
	ruby -S gem install bundler --no-ri --no-rdoc
	ruby -S bundle install

.PHONY : _bibliography/reb.bib
_bibliography/reb.bib : _bibliography/library.bib
	- @echo "==================================================================="
	-	@echo "====================== Generating References ======================"
	-	@echo "==================================================================="
	- @rm _bibliography/ref.bib
	- @cp  _bibliography/library.bib  _bibliography/library-temp.bib
	- @sh _bibliography/fix-references.sh
	- @biber --tool --output_align --output_indent=2 \
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
	- @git add .
	- $(eval MSG := $(shell bash -c 'read -p "Commit msg: " pwd; echo $$pwd'))
	- @echo "==================================================================="
	-	@echo "======================= Pushing on SOURCES ========================"
	-	@echo "==================================================================="
	- @git commit -am "$(MSG)"
	- @git push origin sources
	-	@echo "========================== END ==================================="

.phony: init-master
 init-master :
	- rm -Rf _site
	- mkdir  _site
	- cd _site && \
		git init && \
		git remote add origin http://github.com/jonaprieto/jonaprieto.github.io.git && \
		git pull origin master

.phony : commit
commit :
	- @echo "==================================================================="
	-	@echo "======================= Preparing to Publish ======================"
	-	@echo "==================================================================="
	- @make
	- @make _bibliography/ref.bib
	- @git checkout sources
	- @git add .
	- $(eval MSG := $(shell bash -c 'read -p "Message: " pwd; echo $$pwd'))
	- @git commit -am "$(MSG)"
	- @git push origin sources
	- @echo "==================================================================="
	-	@echo "========================= Jekyll Building ========================="
	-	@echo "==================================================================="
	- @gulp build
	- @if [[ -d "_site/.git" ]]; then \
			echo "===================================================================" &&\
	    echo "================ STATICS FILES: Pushing on MASTER =================" &&\
	    echo "===================================================================" &&\
	    cd _site && git checkout master && \
			git add --all && \
			git commit -m "[ notes ] changes on $(shell date +"%Y-%m-%d time:%H:%M.%S")." && \
			git push origin master;\
		else \
			echo "[!] run first:\n\t $$ make init-master"; \
		fi
	-	@echo "========================== END ==================================="
