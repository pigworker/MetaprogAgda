%if False
\begin{code}

module STLC where

open import Vec

\end{code}
%endif

This chapter contains some standard techniques for the representation
of typed syntax and its semantics. The joy of typed syntax is the avoidance
of junk in its interpretation. Everything fits, just so.

\section{Syntax}

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
%format :: = "\!\raisebox{ -0.09in}[0in][0in]{\red{\textsf{`}}\,}"
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


\section{Semantics}

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


\section{Substitution with a Friendly Fish}

%format Ren = "\F{Ren}"
%format Sub = "\F{Sub}"

We may define the types of simultaneous renamings and substitutions
as type-preserving maps from variables:
\begin{code}
Ren Sub : Cx Ty -> Cx Ty -> Set
Ren  Gam Del  = forall {tau} -> tau <: Gam -> tau <: Del
Sub  Gam Del  = forall {tau} -> tau <: Gam -> Del !- tau
\end{code}

%format <>< = "\F{\propto}"
%format _<><_ = "\us{" <>< "}"
The trouble with defining the action of substitution for a de Bruijn
representation is the need to shift indices when the context grows.
Here is one way to address that situation.
First, let me define\nudge{|<><| is pronounce `fish',
for historical reasons.} context extension as
concatenation with a cons-list, using the |<><| operator.

\begin{code}
_<><_ : forall {X} -> Cx X -> List X -> Cx X
xz <>< <>        = xz
xz <>< (x , xs)  = (xz :: x) <>< xs
\end{code}

%format Xi = "\V{\Xi}"
%format Del = "\V{\Delta}"
%format // = "\F{/\!\!/}"
%format _//_ = "\us{" // "}"
%format theta = "\V{\theta}"
%format Shub = "\F{Shub}"
We may then define the \emph{shiftable} simultaneous substitutions
from |Gam| to |Del|
as type-preserving mappings from the variables in any extension of |Gam| to
terms in the same extension of |Del|.
\begin{code}
Shub : Cx Ty -> Cx Ty -> Set
Shub Gam Del = forall Xi -> Sub (Gam <>< Xi) (Del <>< Xi)
\end{code}

By the computational behaviour of |<><|, a |Shub Gam Del| can be used
as a |Shub (Gam :: sg) (Del :: sg)|, so we can push substitutions under
binders very easily.
\begin{code}
_//_ : forall {Gam Del}(theta : Shub Gam Del){tau} -> Gam !- tau -> Del !- tau
theta // var i    = theta <> i
theta // lam t    = lam ((theta o _,_ _) // t)
theta // app f s  = app (theta // f) (theta // s)
\end{code}

Of course, we shall need to construct some of these joyous shubstitutions.
Let us first show that any simultaneous renaming can be made shiftable by
iterative weakening.
%format wkr = "\F{wkr}"
%format ren = "\F{ren}"
\begin{code}
wkr :  forall {Gam Del sg} -> Ren Gam Del -> Ren (Gam :: sg) (Del :: sg)
wkr r zero     = zero
wkr r (suc i)  = suc (r i)

ren :  forall {Gam Del} -> Ren Gam Del -> Shub Gam Del
ren r <>         = var o r
ren r (_ , Xi)   = ren (wkr r) Xi
\end{code}

%format wks = "\F{wks}"
%format sub = "\F{sub}"
With renaming available, we can do the same for substitutions.
\begin{code}
wks :  forall {Gam Del sg} -> Sub Gam Del -> Sub (Gam :: sg) (Del :: sg)
wks s zero     = var zero
wks s (suc i)  = ren suc // s i

sub :  forall {Gam Del} -> Sub Gam Del -> Shub Gam Del
sub s <>         = s
sub s (_ , Xi)   = sub (wks s) Xi
\end{code}

