\documentclass[a4, 10pt]{article}
\usepackage[english]{babel}
\usepackage[papersize={8.5in,11in},
            twoside,
            includehead,
            top=1in,
            bottom=1in,
            inner=0.75in,
            outer=1.0in,
            bindingoffset=0.35in]{geometry}
\usepackage{graphicx}

\usepackage[pagebackref,
            colorlinks,
            citecolor=darkgreen,
            linkcolor=darkgreen,
            unicode,
            pdfauthor={Univalent Foundations Program},
            pdftitle={Homotopy Type Theory: Univalent Foundations of Mathematics},
            pdfsubject={Mathematics},
            pdfkeywords={type theory, homotopy theory, univalence axiom}]{hyperref}

\usepackage[links]{agda}
\newcounter{chapter}
\usepackage{hott}
\usepackage{bussproofs}
\usepackage{aliascnt}
\usepackage[capitalize]{cleveref}
\usepackage[all,2cell]{xy}
%%%% Indexing
\usepackage{makeidx}
\makeindex

\input{main.labels}

\begin{document}
\begin{center}
  {\Large{\underline{\textbf{Homotopy Type Theory}}}} \\[2mm]
  {\large HoTT Book's exercises}\\
  (work in progress)\\[3.2mm]
  {\large Jonathan Prieto-Cubides}
\end{center}

\begin{abstract}
This is a self-contained version of some solutions for HoTT-Book's exercises.
The idea is to unpackage all as long as possible to get a better understanding.
Solutions are type-checked as a whole using Agda v2.5.3.
\end{abstract}

\tableofcontents

\begin{ex}\label{ex:equality-reflection}
  Suppose we add to type theory the \emph{equality reflection rule} which says that if there is an element $p:x=y$, then in fact $x\jdeq y$.
  Prove that for any $p:x=x$ we have $p\jdeq \refl{x}$.
  (This implies that every type is a \emph{set} in the sense to be introduced in \cref{sec:basics-sets}; see \cref{sec:hedberg}.)
\end{ex}

\end{document}
