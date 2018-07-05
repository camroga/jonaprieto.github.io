---
layout: "post"
title: "Emacs"
date: "2018-06-21"
categories: text-editors
---

I’m not dogmatic about which editor is the best. I use at least three different
text editor depending on what I’m working on: sublime text 3, atom, and emacs.
This post is about emacs but I must confess that I’m a complete beginner using
emacs. I’ve never touched my own configuration scripts and the kind of things an
expert user probably do. My goal in this post is that, becoming a real user of
this amazing tool/text editor that many people claim it is. Since I don’t have
too much time to spend on this kind of task, I will try to learn on the top of
another configuration. Spacemacs is the first option here. I tested, it works
pretty well, but I want to have something more humble without too much
customization, something with enough space of freedom to play with.

My version of emacs at this moment in OSX:

```
GNU Emacs 26.1 (build 1, x86_64-apple-darwin17.5.0)
 of 2018-05-28
```

## [Cask](http://github.com/cask/cask)

Cask is a project management tool for Emacs that helps automate the package
development cycle; development, dependencies, testing, building, packaging and
more.

Cask can also be used to manage dependencies for your local Emacs configuration.

```
brew install cask
```


* [Graphene starting kit](https://github.com/rdallasgray/graphene)

Good ideas but I prefer to not use it.

  - your default initialisation file is ~/.emacs.d/init.el.
  - packages repo:

    ```
    ;; Require Emacs' package functionality
    (require 'package)

    ;; Add the Melpa repository to the list of package sources
    (add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/") t)

    ;; Initialise the package system.
    (package-initialize)
    ```

Then either select those lines and do `M-x eval-region`, or restart Emacs. After
that, do `M-x list-packages`, search for 'graphene' (either manually or using
`C-s`), mark it for installation by pressing 'i', and install it by pressing 'x'.

## Completation

```
(require 'company)
(add-hook 'after-init-hook 'global-company-mode)

; (bind-key "\e\e\e" 'company-abort)
; (bind-key "\C-g" 'company-abort)
; (bind-key "" 'company-select-next)
; (bind-key "" 'company-select-previous)
; (bind-key "" 'company-select-next-or-abort)
; (bind-key "" 'company-select-previous-or-abort)
; (bind-key "" 'company-next-page)
; (bind-key "" 'company-previous-page)
; (bind-key "" 'company-complete-mouse)
; (bind-key "" 'company-select-mouse)
; (bind-key "" 'company-complete-selection)
(bind-key "TAB" 'company-complete-common)
; (bind-key "" 'company-show-doc-buffer)
; (bind-key "" 'company-show-location)
; (bind-key "" 'company-search-candidates)
; (bind-key "" 'company-filter-candidates)
```

## [Agda](http://gitub.com/agda/agda)

Run in the command line `agda-mode compile` and `agda-mode setup`.
Since I prefer to maintain the keybindings explicit, this goes in the `init.el` file:


```
(load-file (let ((coding-system-for-read 'utf-8))
                (shell-command-to-string "agda-mode locate")))

(require 'bind-key)
(bind-key "C-c ,"     'agda2-goal-and-context                 )
(bind-key "C-c ."     'agda2-goal-and-context-and-inferred    )
(bind-key "C-c ;"     'agda2-goal-and-context-and-checked     )
(bind-key "C-c ="     'agda2-show-constraints                 )
(bind-key "C-c ?"     'agda2-show-goals                       )
(bind-key "C-c C-a"   'agda2-abort                            )
(bind-key "C-c C-a"   'agda2-auto                             )
(bind-key "C-c C-b"   'agda2-previous-goal                    )
(bind-key "C-c C-d"   'agda2-infer-type-maybe-toplevel        )
(bind-key "C-c C-d"   'agda2-remove-annotations               )
(bind-key "C-c C-e"   'agda2-show-context                     )
(bind-key "C-c C-f"   'agda2-next-goal                        )
(bind-key "C-c C-r"   'agda2-refine                           )
(bind-key "C-c C-s"   'agda2-solve-maybe-all                  )
(bind-key "C-c C-w"   'agda2-why-in-scope-maybe-toplevel      )
(bind-key "C-c C-z"   'agda2-search-about-toplevel            )
(bind-key "C-c SPC"   'agda2-give                             )
(bind-key "C-c c"     'agda2-make-case                        )
(bind-key "C-c h"     'agda2-helper-function-type             )
(bind-key "C-c l"     'agda2-load                             )
(bind-key "C-c n"     'agda2-compute-normalised-maybe-toplevel)
(bind-key "C-c o"     'agda2-module-contents-maybe-toplevel   )
(bind-key "C-c t"     'agda2-goal-type                        )
(bind-key "C-c C-g"   'agda2-go-back                          )
; (bind-key "C-x c"   'agda2-compile                          )
(bind-key "C-x C-h"   'agda2-display-implicit-argurments      )
(bind-key "C-x C-q"   'agda2-quit                             )
(bind-key "C-x C-r"   'agda2-restart                          )
(bind-key "C-x d"     'agda2-remove-annotations               )
; (bind-key "C-c C-s"     'agda2-set-program-version         )
```

## [Proof-General](https://proofgeneral.github.io/)

In the home directory run this:

```
git clone https://github.com/ProofGeneral/PG ~/.emacs.d/lisp/PG
cd ~/.emacs.d/lisp/PG
make
```

## Theme

I think the spacemacs did it very good in this aspect. I searched and
there its theme available without the need to install all the spacemacs.

- https://github.com/nashamri/spacemacs-theme

Add this in the `init.el` file:

```
(load-theme 'spacemacs-light t)
```

## Markdown and Jekyll

Use `M-x package-install markdown-mode`
Use `M-x package-install jekyll-modes`

## Keybindings

For keybindings beginner and learners I totally recommend to install the package:
[`which-key`](https://github.com/justbur/emacs-which-key): `M-x package-install
which-key` and add these lines in the `init.el`:

```
(require 'which-key)
(which-key-mode)
```

To visualize all the commands, I set up this package to show me on the right
side the frame with all the commands (add this
`(which-key-setup-side-window-right)` in the `init.el`)

- `C-h` : help
- `C-g` : quit
- `C-x b` : switch buffers
- `C-x k` always kills the active buffer, rather than asking you which one you want to kill

- `C-x 1` : close all windows except the active window
- `C-x 0` : close the active window
- `C-x 2` : split the active window vertically into two horizontal windows
- `C-x 3` : split the active window horizontally into two vertical windows

### Files

- `C-x` + `C-f` : open file
- `C-x` + `C-s` : save file
- `C-x` + `C-w` : save file as

### Writing

- `C-space` : set region mark
- `C-w` : kill region
- `C-k` : kill region between point and end of current line
- `C-y` : yank region from kill ring

- `C-_` : undo

- `C-s` : search forwards
- `C-r` : search backwards
- `M-%` : query replace (‘space’ to replace, ‘n’ to skip, ‘!’ to replace all)
- `M-q` : **wrap text**


### Graphene

Graphene creates some new keybindings, and alters some existing ones:

- `C-x C-k` kills the default buffer and closes its window
- `C-c n` creates a new buffer
- `C-c N` creates a new instance of Emacs

(*Not working for unknown reason in my laptop*):

- `C-;` adds a semicolon at the end of the line
- `M-RET` creates a newline below the current line and moves to it
- `C-M-;` comments or uncomments the current line
- `C->` increases the height of the current window
- `C-<` decreases it
- `C-.` increases the width of the current window
- `C-,` decreases it
- `C-c s` selects the Speedbar window


## Projects

project-persist uses the following keybindings:

- `C-c` `P n` to create a new project
- `C-c` `P f` to find an existing project
- `C-c` `P k` to close the current project
- `C-c` `P d` to delete an existing project
