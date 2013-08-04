%if False
\begin{code}

module STLC where

open import Vec

\end{code}
%endif

Last century, I learned the following recipe for well typed terms of
the simply typed $\lambda$-calculus from Altenkirch and Reus.

First, give a syntax for types. I shall start with a base type
and close under function spaces.

%format Ty = "\D{\star}"
%format iota = "\C{\upiota}"
%format ->> = "\C{\vartriangleright}"
%format _->>_ = "\_\!" ->> "\!\_"
%format Cx = "\D{Cx}"
%format Em = "\C{\mathcal{E}}"
%format var = "\C{var}"
%format lam = "\C{lam}"
%format app = "\C{app}"
%format :: = "\!\raisebox{ -0.09in}[0in][0in]{\red{\textrm{`}}\,}"
%format _::_ = "\us{" :: "}"

\begin{code}
data Ty : Set where
  iota   :              Ty
  _->>_  : Ty -> Ty ->  Ty
infixr 5 _->>_
\end{code}

Next, build contexts as snoc-lists.

\begin{code}
data Cx (X : Set) : Set where
  Em    : Cx X
  _::_  : Cx X -> X -> Cx X
infixl 4 _::_
\end{code}

Now, define typed de Bruijn indices to be context membership evidence.

%format <: = "\D{\in}"
%format _<:_ = "\us{" <: "}"
%format Gam = "\V{\Gamma}"
%format sg = "\V{\sigma}"
%format tau = "\V{\tau}"
\begin{code}
data _<:_ (tau : Ty) : Cx Ty -> Set where
  zero  : forall {Gam}                    -> tau <: Gam :: tau
  suc   : forall {Gam sg}  -> tau <: Gam  -> tau <: Gam :: sg
infix 3 _<:_
\end{code}

That done, we can build well typed terms by writing syntax-directed
rules for the typing judgment.

%format !- = "\D{\vdash}"
%format _!-_ = "\us{" !- "}"
\newcommand{\negs}{\hspace*{ -0.3in}}
\begin{code}
data _!-_ (Gam : Cx Ty) : Ty -> Set where

  var :  forall {tau}
         ->  tau <: Gam
         --  \negs -------------
         ->  Gam !- tau

  lam :  forall {sg tau}
         ->  Gam :: sg !- tau
         --  \negs ------------------
         ->  Gam !- sg ->> tau

  app :  forall {sg tau}
         ->  Gam !- sg ->> tau  ->  Gam !- sg
         --  \negs -------------------------------
         ->  Gam !- tau

infix 3 _!-_
\end{code}

Writing an interpreter for such a calculus is an exercise also from
last century, for which we should thank Augustsson and Carlsson.
Start by defining the semantics of each type.

%format !>T = !> "_{" Ty "}"
%format <!_!>T = <! "\!" _ "\!" !>T
\begin{code}
<!_!>T : Ty -> Set
<! iota !>T        = Nat                      -- by way of being nontrivial
<! sg ->> tau !>T  = <! sg !>T -> <! tau !>T
\end{code}

Next, define \emph{environments} for contexts, with projection.
%format !>C = !> "_{" Cx "}"
%format <!_!>C = <! "\!" _ "\!" !>C
%format !>V = !> "_{" <: "}"
%format <!_!>V = <! "\!" _ "\!" !>V
%format gam = "\V{\gamma}"
\begin{code}
<!_!>C : Cx Ty -> Set
<! Em !>C         = One
<! Gam :: sg !>C  = <! Gam !>C * <! sg !>T

<!_!>V : forall {Gam tau} -> tau <: Gam -> <! Gam !>C -> <! tau !>T
<! zero !>V   (gam , t)  = t
<! suc i !>V  (gam , s)  = <! i !>V gam
\end{code}

Finally, define the meaning of terms.
%format !>t = !> "_{" !- "}"
%format <!_!>t = <! "\!" _ "\!" !>V
\begin{code}
<!_!>t : forall {Gam tau} -> Gam !- tau -> <! Gam !>C -> <! tau !>T
<! var i !>t    gam = <! i !>V gam
<! lam t !>t    gam = \ s -> <! t !>t (gam , s)
<! app f s !>t  gam = <! f !>t gam (<! s !>t gam)
\end{code}
