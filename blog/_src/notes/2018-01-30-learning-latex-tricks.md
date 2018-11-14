---
layout: "post"
title: "Latex tricks"
date: "2018-01-30"
categories: learning
linkify: true

---

A collection of useful tricks and snippets to use in Latex.

### Highlight undefined references and citation by Stefan Kottwitz

{: .links }
  - See https://latex.org/forum/viewtopic.php?t=13654
  - See https://tex.stackexchange.com/questions/176297/automatically-highlight-undefined-references

{%- highlight latex -%}
{% raw %}
  \documentclass{article}
  \usepackage{xcolor}
  \newcommand*{\missingreference}{\colorbox{red}{?reference?}}
  \newcommand*{\missingcitation}{\colorbox{red}{?citation?}}
  \makeatletter
  \def\@setref#1#2#3{%
     \ifx#1\relax
      \protect\G@refundefinedtrue
      \nfss@text{\reset@font\missingreference}%
      \@latex@warning{Reference `#3' on page \thepage \space
                undefined}%
     \else
      \expandafter#2#1\null
     \fi}
  \def\@citex[#1]#2{\leavevmode
     \let\@citea\@empty
     \@cite{\@for\@citeb:=#2\do
       {\@citea\def\@citea{,\penalty\@m\ }%
        \edef\@citeb{\expandafter\@firstofone\@citeb\@empty}%
        \if@filesw\immediate\write\@auxout{\string\citation{\@citeb}}\fi
        \@ifundefined{b@\@citeb}{\hbox{\reset@font\missingcitation}%
          \G@refundefinedtrue
          \@latex@warning
            {Citation `\@citeb' on page \thepage \space undefined}}%
          {\@cite@ofmt{\csname b@\@citeb\endcsname}}}}{#1}}
  \makeatothers
  \begin{document}
  This is a missing reference: \ref{somefig}.
  This is a missing citation: \cite{somebib}.
  \end{document}
{% endraw %}
{%- endhighlight -%}
