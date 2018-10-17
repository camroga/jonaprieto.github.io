The blog [![Build Status](https://travis-ci.org/jonaprieto/jonaprieto.github.io.svg?branch=sources)](https://travis-ci.org/jonaprieto/jonaprieto.github.io)
========

<img src="https://github.com/jonaprieto/assets/raw/master/blog.gif"
 alt="Jonaprieto blog" height=400 align="right" />

This blog is intended to be an academic blog which means the blog posts try to
follow the same structure as an academic paper including the references. You
can print them out and they will look like an authentic paper, one of the
major advantages is the version controlling, the integration with `git`.

This blog is on Github and it has two branches:

  - `sources` : mainly to save all the codes.
  - `master` : static files for rendering on Github pages.

## Clone this repository

```
$ git clone -b sources --single-branch http://github.com/jonaprieto/jonaprieto.github.io
$ cd jonaprieto.github.io
```

The workflow is to push your changes to the branch `sources`.

If you have everything installed (read below), run this site locally by running

```
$ make run
```

The posts are in the folder `blog/_src/notes`.

Any error? follow the instructions below to check everything is right.
I also recommend to check the Makefile.

### Local testing

To run this site locally, we need to have installed some tools.

- `ruby` ( the prog. language, it should be installed by default )

```
$ ruby -v
2.3.3
```

- `jekyll` ( to generate the blog from markdown files )

```
$ gem install bundler jekyll
```

- `homebrew` (The missing package manager for Mac OSX)

```
/usr/bin/ruby -e "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install)"
```

- `agda v2.5.4+` ( to compile the Agda codes )

```
$ brew install ghc
$ brew install agda
```

- `stack` ( to install safety `agda2html`)

```
$ brew install stack
```

- `agda2html` ( run `make agda2html`, you will need `ghc` and `stack` )

- `ipe` ( to render the ipe figures, great tool )

```
$ brew install cask
$ brew cask install ipe
```

- `npm` ( the package manager of javascript )

```
$ brew install npm
```

- `gulp` ( to deploy the site )

```
$ npm install --global gulp
```

- `biber` ( to format the bibliography, this is a latex requirement )

```
$ tlmgr install biber
```

- Install any missing dependency (ruby gems)

```
$ bundle install
```

Once you have **all** these programs installed, to generate the site
run the following command:

```
$ make run
...
--------------------------------------
      Local: http://localhost:4000
--------------------------------------
...
```

Now, we should to see the site locally and expect reloads
after changing any file.

# The files

- `blog/_src/notes` is there all the content is.
- `blog/_bibliography/library.bib` is where I put all my references
- `blog/assets` is where I put all the images but if they are `ipe` files, they are in
the folder `blog/_src/ipe-images` because I convert them to png automatically.

### Writing Posts

In addition to the Jekyll tradition of writing blog post, a post can use the
following variables in its preamble to have some extra features.

For example:

- `author: "author1" ` ( for the printed version )
- `author_affiliation: "info"` ( for the printed version )
- `coauthor: "info" ` ( for the printed version )
- `coauthor_affiliation: "info"` ( for the printed version )
- `references: true` ( to include references at the end by using the tag `{% cite bibTag %}` )
- `toc: true` ( to include a nice table of contents on your right )
- `agda: true` ( if the file contains Agda code )
- `gallery: true` ( if you want to have zoom for your pictures, it's really cool )
- `latex: true` ( to render formulas between the symbols `$$...$$` and center equations if they are inside `{: .eq }` environment )
- `linkify: true` ( to convert any text link to a real anchor link, that is, clickable )
- `showcitation: true` ( to show at the end how we should cite the current entry in Bibtex format )
- `bibtexauthors: "strings"` ( used as the author info in the generation the bibtex citation )
- `bibtextag: latexTag` ( used as the tag in the generation of the bibtex citation )

## Pushing changes

If you just cloned this repository, you may need to run `make init-master`.
To push the changes, just run `make commit` and provide a good message.
