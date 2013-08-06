%if False
\begin{code}
module Containers where

open import Proving public
\end{code}
%endif

Containers are the infinitary generalization of normal functors.
%format Con = "\D{Con}"
%format Sh = "\F{Sh}"
%format Po = "\F{Po}"
%format <1 = "\C{\triangleleft}"
%format _<1_ = "\us{" <1 "}"
%format !>c = !> "_{" <1 "}"
%format <!_!>c = <! _ !>c where
\begin{code}
record Con : Set1 where
  constructor _<1_
  field
    Sh  : Set             -- a set of shapes
    Po  : Sh -> Set       -- a family of positions
  <!_!>c : Set -> Set
  <!_!>c X = Sg Sh \ s -> Po s -> X
open Con public
infixr 1 _<1_
\end{code}
Instead of having a \emph{size} and a \emph{vector} of contents, we represent
the positions for each shape as a set, and the contents as a \emph{function}
from positions.


\section{Closure Properties}

We may readily check that the polynomials are all containers.

%format Kc = "\F{K}_{" <1 "}"
%format Ic = "\F{I}_{" <1 "}"
%format +c = "\F{+}_{" <1 "}"
%format *c = "\F{\times}_{" <1 "}"
%format _+c_ = "\us{" +c "}"
%format _*c_ = "\us{" *c "}"
\begin{code}
Kc : Set -> Con
Kc A = A <1 \ _ -> Zero

Ic : Con
Ic = One <1 \ _ -> One

_+c_ : Con -> Con -> Con
(S <1 P) +c (S' <1 P') = (S + S') <1 vv P <?> P'

_*c_ : Con -> Con -> Con
(S <1 P) *c (S' <1 P') = (S * S') <1 vv \ s s' -> P s + P' s'
\end{code}

Moreover, we may readily close containers under dependent pairs and functions,
a fact which immediately tells us how to compose containers.
%format Sgc = "\F{\Upsigma}_{" <1 "}"
%format Pic = "\F{\Uppi}_{" <1 "}"
%format oc = "\F{\circ}_{" <1 "}"
%format _oc_ = "\us{" oc "}"
\begin{code}
Sgc : (A : Set)(C : A -> Con) -> Con
Sgc A C = (Sg A \ a -> Sh (C a)) <1 vv \ a s -> Po (C a) s

Pic : (A : Set)(C : A -> Con) -> Con
Pic A C = ((a : A) -> Sh (C a)) <1 \ f -> Sg A \ a -> Po (C a) (f a)

_oc_ : Con -> Con -> Con
(S <1 P) oc C = Sgc S \ s -> Pic (P s) \ p -> C
\end{code}

\begin{exe}[containers are endofunctors]
Check that containers yield endofunctors which obey the laws.

%format conEndoFunctor = "\F{conEndoFunctor}"
%format conEndoFunctorOKP = "\F{conEndoFunctorOKP}"
\begin{spec}
conEndoFunctor : {C : Con} -> EndoFunctor <! C !>c
conEndoFunctor {S <1 P} = ?

conEndoFunctorOKP : {C : Con} -> EndoFunctorOKP <! C !>c
conEndoFunctorOKP {S <1 P} = ?
\end{spec}
%if False
\begin{code}
conEndoFunctor : {C : Con} -> EndoFunctor <! C !>c
conEndoFunctor {S <1 P} = record { map = \ f -> vv \ s k -> s , f o k }

conEndoFunctorOKP : {C : Con} -> EndoFunctorOKP <! C !>c
conEndoFunctorOKP {S <1 P} = record
  {  endoFunctorId = \ { (s , k) -> refl }
  ;  endoFunctorCo = \ { f g  (s , k) -> refl }
  }
\end{code}
%endif
\end{exe}


\section{Container Morphisms}

A container morphism describes a \emph{natural transformation} between
the functors given by containers. As the element type is abstract, there
is nowhere that the elements of the output can come from except somewhere
in the input. Correspondingly, a container morphism is given by a pair of
functions, the first mapping input shapes to output shapes, and the second
mapping output positions back to the input positions from which they
fetch elements.
%format -c> = "\F{\to}_{" <1 "}"
%format _-c>_ = "\us{" -c> "}"
\begin{code}
_-c>_ : Con -> Con -> Set
(S <1 P) -c> (S' <1 P') = Sg (S -> S') \ f -> (s : S) -> P' (f s) -> P s
\end{code}
The action of a container morphism is thus
%format /c = "\F{/}_{" <1 "}"
%format _/c_ = "\us{" /c "}"
\begin{code}
_/c_ : forall {C C'} -> C -c> C' -> forall {X} -> <! C !>c X -> <! C' !>c X
(to , fro) /c (s , k) = to s , k o fro s
\end{code}

\paragraph{Interactive Interpretation} Peter Hancock encourages us to
think of |S <1 P| as the description of a \emph{command-response}
protocol, where |S| is a set of commands we may invoke and |P| tells
us which responses may be returned for each command.  The type |<! S
<1 P !>c X| is thus a \emph{strategy} for obtaining an |X| by one run
of the protocol. Meanwhile, a container morphism is thus a kind of
`device driver', translating commands one way, then responses the
other.

\begin{exe}[representing natural transformations]
Check that you can represent any natural transformation between
containers as a container morphism.
%format morphc = "\F{morph}_{" <1 "}"
\begin{spec}
morphc : forall {C C'} -> (forall {X} -> <! C !>c X -> <! C' !>c X) -> C -c> C'
morphc f = ?
\end{spec}
%if False
\begin{code}
morphc : forall {C C'} -> (forall {X} -> <! C !>c X -> <! C' !>c X) -> C -c> C'
morphc f = (\ s -> fst (f (s , id))) , (\ s -> snd (f (s , id)))
\end{code}
%endif
\end{exe}

\paragraph{Container-of-positions presentation} The above exercise might
suggest an equivalent presentation of container morphisms, namely
\begin{spec} (S <1 P) -c> C = (s : S) -> <! C !>c (P s)
\end{spec}
but the to-and-fro presentation is usually slightly easier to work
with. You win some, you lose some.

\begin{exe}[identity and composition]
Check that you can define identity and composition for container morphisms.
%format idmc = id "_{" -c> "}"
%format omc = o "_{\!\!\!" -c> "}"
%format _omc_ = "\us{" omc "}"
\begin{spec}
idmc : forall {C} -> C -c> C
idmc = ?

_omc_ : forall {C D E} -> (D -c> E) -> (C -c> D) -> (C -c> E)
e omc d = ?
\end{spec}
%if False
\begin{code}
idmc : forall {C} -> C -c> C
idmc = id , \ _ -> id

_omc_ : forall {C D E} -> D -c> E -> C -c> D -> C -c> E
(to , fro) omc (to' , fro') = (to o to') , \ s -> fro' s o fro (to' s)
\end{code}
%endif
\end{exe}


\section{W-types}

%format W = "\D{\mathcal{W}}"
The least fixpoint of a container is a |W|-type---|W| for `well founded'.
\begin{code}
data W (C : Con) : Set where
  <$_$> : <! C !>c (W C) -> W C
\end{code}

In an extensional setting, |W| can be used to represent a great many
datatypes, but intensional systems have some difficulties achieving
faithful representations of first order data via |W|-types.

\begin{exe}[natural numbers]
Define natural numbers as a |W|-type. Implement the constructors.
Hint: |magic : Zero -> {A : Set} -> A|.
Implement primitive recursion and use it to implement addition.
%format NatW = "\F{NatW}"
%format zeroW = "\F{zeroW}"
%format sucW = "\F{sucW}"
%format precW = "\F{precW}"
%format addW = "\F{addW}"
\begin{spec}
NatW : Set
NatW = W ?

zeroW : NatW
zeroW = <$ ? $>

sucW : NatW -> NatW
sucW n = <$ ? $>

precW : forall {l}{T : Set l} -> T -> (NatW -> T -> T) -> NatW -> T
precW z s n = ?

addW : NatW -> NatW -> NatW
addW x y = precW ? ? x
\end{spec}
%if False
\begin{code}
NatW : Set
NatW = W (Two <1 Zero <?> One)

zeroW : NatW
zeroW = <$ tt , magic $>

sucW : NatW -> NatW
sucW n = <$ ff , pure n $>

precW : forall {l}{T : Set l} -> T -> (NatW -> T -> T) -> NatW -> T
precW z s <$ tt , _ $> = z
precW z s <$ ff , k $> = s (k <>) (precW z s (k <>))

addW : NatW -> NatW -> NatW
addW x y = precW y (pure sucW) x
\end{code}
%endif
How many different implementations of |zeroW| can you find?
Meanwhile, discover for yourself why an attempt to establish the
induction principle is a fool's errand.
%format indW = "\F{indW}"
\begin{spec}
indW :  forall {l}(P : NatW -> Set l) ->
        P zeroW ->
        ((n : NatW) -> P n -> P (sucW n)) ->
        (n : NatW) -> P n
indW P z s n = ?
\end{spec}
\end{exe}