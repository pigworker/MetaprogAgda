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
xz <>< (x , xs)  = xz :: x <>< xs
infixl 4 _<><_
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
With renaming available, we can play the same game for substitutions.
\begin{code}
wks :  forall {Gam Del sg} -> Sub Gam Del -> Sub (Gam :: sg) (Del :: sg)
wks s zero     = var zero
wks s (suc i)  = ren suc // s i

sub :  forall {Gam Del} -> Sub Gam Del -> Shub Gam Del
sub s <>         = s
sub s (_ , Xi)   = sub (wks s) Xi
\end{code}

%if False
I wonder if there's a canny reversal trick which will fix this.
Hope it's chips, it's chips...

\begin{code}
_<>>_ : forall {X} -> Cx X -> List X -> List X
Em <>> ys = ys
(xz :: x) <>> ys = xz <>> (x , ys)

nocyc : (n : Nat) -> suc n == n -> {A : Set} -> A
nocyc n ()



_+a_ : Nat -> Nat -> Nat
zero +a y = y
suc x +a y = x +a suc y

sucI : (a b : Nat) -> (_==_ {lzero}{Nat} (suc a) (suc b)) -> a == b
sucI .b b refl = refl

grr : (x y : Nat) -> suc x +Nat y == x +Nat suc y
grr zero y = refl
grr (suc x) y rewrite grr x y = refl

noc' : (x y : Nat) -> suc (x +Nat y) == y -> {A : Set} -> A
noc' x zero ()
noc' x (suc y) q = noc' x y
     (suc (x +Nat y) =!! grr x y >> x +Nat suc y =!! sucI _ _ q >> y <QED>)

noc : (x k y : Nat) -> x +a (suc k +Nat y) == y -> {A : Set} -> A
noc zero k y q = noc' k y q
noc (suc x) k y q = noc x (suc k) y q

len : forall {X} -> Cx X -> Nat
len Em = zero
len (xz :: x) = suc (len xz)

lenlem : forall {X}(xz : Cx X)(xs : List X) ->
  length (xz <>> xs) == len xz +a length xs
lenlem Em xs = refl
lenlem (xz :: x) xs = lenlem xz (x , xs)

lem0 : forall {X}(xz yz : Cx X)(xs ys : List X) ->
       length xs == length ys ->
       xz <>> xs == yz <>> ys -> (xz == yz) * (xs == ys)
lem0 Em Em xs ys q q' = refl , q'
lem0 Em (yz :: x) .(yz <>> (x , ys)) ys q refl
 rewrite lenlem yz (x , ys) = noc (len yz) zero (length ys) q
lem0 (xz :: x) Em xs .(xz <>> (x , xs)) q refl
 rewrite lenlem xz (x , xs) = noc (len xz) zero (length xs)
   (_ << q !!= _ <QED>)
lem0 (xz :: x) (yz :: y) xs ys q q'
  with lem0 xz yz (x , xs) (y , ys) (cong suc q) q' 
lem0 (.yz :: .y) (yz :: y) .ys ys q q' | refl , refl = refl , refl

lem : forall {X}(Del Gam : Cx X) Xi -> Del <>> <> == Gam <>> Xi ->
      Gam <>< Xi == Del
lem Del Gam <>       q  =
   Gam << fst (lem0 Del Gam <> <> refl q) !!= Del <QED>
lem Del Gam (x , Xi) q  = lem Del (Gam :: x) Xi q

fishy : forall {Gam} Xi -> Ren Gam (Gam <>< Xi)
fishy <>        i  = i
fishy (_ , Xi)  i  = fishy Xi (suc i)

lambda :  forall {Gam sg tau} ->
          ((forall {Del Xi}{{_ : Del <>> <> == Gam <>> (sg , Xi)}} -> Del !- sg) ->
            Gam :: sg !- tau) ->
          Gam !- sg ->> tau
lambda {Gam} f = lam (f \ {Del Xi}{{q}} -> subst (lem Del Gam (_ , Xi) q) (\ Gam -> Gam !- _) (var (fishy Xi zero)))

myTest : Em !- (iota ->> iota) ->> (iota ->> iota)
myTest = lambda \ f -> lambda \ x -> app f (app f x)

\end{code}

\begin{spec}
fishy : forall {Gam} Xi -> Ren Gam (Gam <>< Xi)
fishy <>        i  = i
fishy (_ , Xi)  i  = fishy Xi (suc i)

lambda :  forall {Gam sg tau} ->
          ((forall {Xi} -> Gam :: sg <>< Xi !- sg) -> Gam :: sg !- tau) ->
          Gam !- sg ->> tau
lambda f = lam (f \ {Xi} -> var (fishy Xi zero))

myTest : Em !- iota ->> iota
myTest = lambda \ x -> x
\end{spec}
%endif
