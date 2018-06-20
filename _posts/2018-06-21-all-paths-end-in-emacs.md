---
layout: "post"
title: "Emacs militant"
date: "2018-06-15"
categories: utilities
---

I'm not dogmatic about which editor is the best. I use at least three different
text editor depending on what I'm working on: sublime text 3, atom, and emacs.
This post is about emacs but I must confess that I'm a complete beginner using
emacs. I've never touched my own configuration scripts and the kind of things an
expert user probably do. My goal in this post is that, becoming a better user of
this amazing tool/text editor that  many people claim it is. Since I don't have
too much time to spend in this kind of task, I will try to learn on the top of
another configuration. Spacemacs is the first option here. I tested, it works
pretty well, but I want to have something more humble without too much
customisation, something with enough space of freedom to play with.


I'm a OSX user using `brew` to install almost everything that I need.
My version of emacs at this moment:

```
GNU Emacs 26.1 (build 1, x86_64-apple-darwin17.5.0)
 of 2018-05-28
```

## [Cask](http://github.com/cask/cask)

Cask is a project management tool for Emacs that helps automate the package development cycle; development, dependencies, testing, building, packaging and more.

Cask can also be used to manage dependencies for your local Emacs configuration.

```
brew install cask
```

From graphene repository: https://github.com/rdallasgray/graphene

Anyway -- your default initialisation file is in (old-school) ~/.emacs or (new-school, and where it should be) ~/.emacs.d/init.el. First, you need to set up the Emacs package system and tell it about Melpa, so create one of those files if it doesn't already exist, and add these lines to the file:

```
;; Require Emacs' package functionality
(require 'package)

;; Add the Melpa repository to the list of package sources
(add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/") t)

;; Initialise the package system.
(package-initialize)
```

Then either select those lines and do M-x eval-region, or restart Emacs. After that, do M-x list-packages, search for 'graphene' (either manually or using C-s), mark it for installation by pressing 'i', and install it by pressing 'x'.


## [Agda](http://gitub.com/agda/agda)

Run in the command line `agda-mode compile` and `agda-mode setup`.

## [Proof-General](https://proofgeneral.github.io/)

In the home directory run this:

```
git clone https://github.com/ProofGeneral/PG ~/.emacs.d/lisp/PG
cd ~/.emacs.d/lisp/PG
make
```

## Look&feel

I think the spacemacs did it very good in this aspect. I searched and
there its theme available without the need to install all the spacemacs.

- https://github.com/nashamri/spacemacs-theme

Add this in the `init.el` file:

```
(load-theme 'spacemacs-light t)
```

## Markdown

Use `M-x package-install which-key`

## Keybindings

For keybindings beginner and learners I totally recommend to install the package:
[`which-key`](https://github.com/justbur/emacs-which-key): `M-x package-install
which-key` and add these lines in the `init.el`:

```
(require 'which-key)
(which-key-mode)
```

To visualize all the commands, I set up this package to show me on the right
side the frame with all the commands (add this `(which-key-setup-side-window-right)` in the `init.el`)

- C-h C-h : help
- C-g : quit
- C-x b : switch buffers
- C-x k always kills the active buffer, rather than asking you which one you want to kill

- C-x 1 : close all windows except the active window
- C-x 0 : close the active window
- C-x 2 : split the active window vertically into two horizontal windows
- C-x 3 : split the active window horizontally into two vertical windows

### Files

- C-x C-f : open file
- C-x C-s : save file
- C-x C-w : save file as



### Writing

- C-space : set region mark
- C-w : kill region
- C-k : kill region between point and end of current line
- C-y : yank region from kill ring

- C-_ : undo

- C-s : search forwards
- C-r : search backwards
- M-% : query replace (‘space’ to replace, ‘n’ to skip, ‘!’ to replace all)
- M-q : **wrap text**


### Graphene

Graphene creates some new keybindings, and alters some existing ones:

- C-x C-k kills the default buffer and closes its window
- C-c n creates a new buffer
- C-c N creates a new instance of Emacs

(Not working for unknown reason):

- C-; adds a semicolon at the end of the line
- M-RET creates a newline below the current line and moves to it
- C-M-; comments or uncomments the current line
- C-> increases the height of the current window
- C-< decreases it
- C-. increases the width of the current window
- C-, decreases it
- C-c s selects the Speedbar window


## Projects

project-persist uses the following keybindings:

- C-c P n to create a new project
- C-c P f to find an existing project
- C-c P k to close the current project
- C-c P d to delete an existing project
