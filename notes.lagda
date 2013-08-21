\documentclass{book}
\usepackage{a4}
\usepackage{palatino}
\usepackage{natbib}
\usepackage{amsfonts}
\usepackage{stmaryrd}
\usepackage{upgreek}


\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}

\usepackage{color}
\newcommand{\redFG}[1]{\textcolor[rgb]{0.6,0,0}{#1}}
\newcommand{\greenFG}[1]{\textcolor[rgb]{0,0.4,0}{#1}}
\newcommand{\blueFG}[1]{\textcolor[rgb]{0,0,0.8}{#1}}
\newcommand{\orangeFG}[1]{\textcolor[rgb]{0.8,0.4,0}{#1}}
\newcommand{\purpleFG}[1]{\textcolor[rgb]{0.4,0,0.4}{#1}}
\newcommand{\yellowFG}[1]{\textcolor{yellow}{#1}}
\newcommand{\brownFG}[1]{\textcolor[rgb]{0.5,0.2,0.2}{#1}}
\newcommand{\blackFG}[1]{\textcolor[rgb]{0,0,0}{#1}}
\newcommand{\whiteFG}[1]{\textcolor[rgb]{1,1,1}{#1}}
\newcommand{\yellowBG}[1]{\colorbox[rgb]{1,1,0.2}{#1}}
\newcommand{\brownBG}[1]{\colorbox[rgb]{1.0,0.7,0.4}{#1}}

\newcommand{\ColourStuff}{
  \newcommand{\red}{\redFG}
  \newcommand{\green}{\greenFG}
  \newcommand{\blue}{\blueFG}
  \newcommand{\orange}{\orangeFG}
  \newcommand{\purple}{\purpleFG}
  \newcommand{\yellow}{\yellowFG}
  \newcommand{\brown}{\brownFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\whiteFG}
}

\newcommand{\MonochromeStuff}{
  \newcommand{\red}{\blackFG}
  \newcommand{\green}{\blackFG}
  \newcommand{\blue}{\blackFG}
  \newcommand{\orange}{\blackFG}
  \newcommand{\purple}{\blackFG}
  \newcommand{\yellow}{\blackFG}
  \newcommand{\brown}{\blackFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\blackFG}
}

\ColourStuff


\newcommand{\D}[1]{\blue{\mathsf{#1}}}
\newcommand{\C}[1]{\red{\mathsf{#1}}}
\newcommand{\F}[1]{\green{\mathsf{#1}}}
\newcommand{\V}[1]{\purple{\mathit{#1}}}
\newcommand{\T}[1]{\raisebox{0.02in}{\tiny\green{\textsc{#1}}}}

\newcommand{\us}[1]{\_\!#1\!\_}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

%subst keyword a = "\mathkw{" a "}"
%subst conid a = "\V{" a "}"
%subst varid a = "\V{" a "}"

%format -> = "\blue{\rightarrow}"

\newcommand{\nudge}[1]{\marginpar{\footnotesize #1}}
\newtheorem{exe}{Exercise}[chapter]

%format rewrite = "\mathkw{rewrite}"
%format constructor = "\mathkw{constructor}"

%format ? = "\orange{?}"

\begin{document}

\title{Dependently Typed Metaprogramming \\ (in Agda)}
\author{Conor McBride}
\maketitle

\section*{Introduction}

If you have never met a metaprogram in a dependently typed programming
language like Agda~\citep{DBLP:conf/afp/Norell08}, then prepare to be
underwhelmed. Once we have types which can depend computationally upon
first class values, metaprograms just become ordinary programs
manipulating and interpreting data which happen to stand for types and
operations.

This course, developed in the summer of 2013, explores methods of
metaprogramming in the dependently typed setting. I happen to be using
Agda to deliver this material, but the ideas transfer to any setting
with enough dependent types. It would certainly be worth trying to
repeat these experiments in Idris, or in Coq, or in Haskell, or in
your own dependently typed language, or maybe one day in mine.


\chapter{Vectors and Normal Functors}

%include Vec.lagda


\chapter{Simply Typed $\uplambda$-Calculus}

%include STLC.lagda


\chapter{Containers and W-types}

%include Containers.lagda


\chapter{Indexed Containers (Levitated)}

%include IxCon.lagda


\chapter{Induction-Recursion}

%include IR.lagda


\chapter{Observational Equality}

\chapter{Type Theory in Type Theory}

\chapter{Reflections and Directions}

\bibliographystyle{plainnat}
\bibliography{notes.bib}

\end{document}