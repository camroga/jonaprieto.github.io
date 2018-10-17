The blog [![Build Status](https://travis-ci.org/jonaprieto/jonaprieto.github.io.svg?branch=sources)](https://travis-ci.org/jonaprieto/jonaprieto.github.io)
========

<img src="https://github.com/jonaprieto/jonaprieto.github.io/raw/sources/assets/blog.gif"
 alt="Jonaprieto blog" height=400 align="right" />

This blog is intended to be an academic blog which means the blog posts try to
follow the same structure as an academic paper including the references. You
can print them out and they will look like an authentic paper, one of the
major advantages is the version controlling, the integration with `git`.


This blog is on Github and it has two branches:

  - `sources` : mainly to save all the codes.
  - `master` : static files for rendering on Github pages.

The workflow is to push your changes to the branch `sources`. Using the Makefile,
we run `make commit` and the command will make a commit on the sources branches,
generate all the HTML files and push the changes in the master branch.

If you have everything installed, run this site locally by running

```
$ make run
```

Check the post in the folder `blog/_src/notes`.

Any error? follow the instructions below to check everything is right.

### Local testing

If you want to run this site on your machine, run the following command.

```
$ make run
```

To run this command, we need to have installed `gulp` and of course all the
following requirements (omit any if you already had it):

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

- `agda2html` ( run `make agda2html`, you will need `ghc` and `stack` of Haskell)

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

- `biber` ( to format the bibliography )

```
$ tlmgr install biber
```

Once you have all these programs installed, to generate the site
run the following commands:

- Install any missing dependency (ruby gems)

```
$ bundle install
```

To run locally the site:

```
$ make run
...
--------------------------------------
      Local: http://localhost:4000
--------------------------------------
...
```

After all of this, you should be able to run the site locally and expect reloads
after changing any file which it's very cool. :)

# Where are the important files (the posts)

- The main folder is `blog/_src/notes`.
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

To push the changes, just run `make commit` and provide a good message.
