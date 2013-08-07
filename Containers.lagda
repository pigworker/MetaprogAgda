%if False
\begin{code}
module Containers where

open import Proving public
open import NormF public
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

\begin{exe}[closure properties]
Check that the meanings of the operations on containers are justified
by their interpretations as functors.
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

A useful deployment of the |W|-type is to define the free monad for a
container.
%format ^* = "\F{{}^{\ast}}"
%format _^*_ = "\us{" ^* "}"
\begin{code}
_^*_ : Con -> Set -> Set
C ^* X = W (Kc X +c C)
\end{code}

\begin{exe}[free monad]
Construct the components for
%format freeMonad = "\F{freeMonad}"
\begin{spec}
freeMonad : (C : Con) -> Monad (_^*_ C)
freeMonad C = ?
\end{spec}
%if  False
\begin{code}
freeMonad : (C : Con) -> Monad (_^*_ C)
freeMonad C = record
  {  return = \ x -> <$ (tt , x) , magic $>
  ;  _>>=_ = graft
  }  where
  graft : forall {A B} -> C ^* A -> (A -> C ^* B) -> C ^* B
  graft <$ (tt , a) , _ $> l = l a
  graft <$ (ff , s) , k $> l = <$ (ff , s) , (\ p -> graft (k p) l) $>
\end{code}
%endif
\end{exe}

\begin{exe}[free monad closure]
Define an operator
%format ^*c = "\F{{}^{\ast_{\!" <1 "}}}"
%format _^*c = _ ^*c
\begin{spec}
_^*c : Con -> Con
_^*c C = ?
\end{spec}
%if False
\begin{code}
_^*c : Con -> Con
_^*c C = C ^* One <1 Path where
  Path : C ^* One -> Set
  Path <$ (tt , _) , _ $> = One
  Path <$ (ff , s) , k $> = Sg (Po C s) \ p -> Path (k p)
\end{code}
%endif
and exhibit an isomorphism 
\[
  |C ^* X| \cong |<! C ^*c !>c X|
\]
\end{exe}

\begin{exe}[general recursion]
Define the monadic computation which performs one command-response
interaction:
%format call = "\F{call}"
\begin{spec}
call : forall {C} -> (s : Sh C) -> C ^* Po C s
call s = ?
\end{spec}
%if False
\begin{code}
call : forall {C} -> (s : Sh C) -> C ^* Po C s
call s = <$ (ff , s) , (\ p -> <$ (tt , p) , magic $>) $>
\end{code}
%endif
We can model\nudge{in too much detail}, the general recursive function
space as the means to perform finite, on demand expansion of call trees.
%format Pib = "\F{\Uppi}_{\F{\!\bot}}"
\begin{code}
Pib : (S : Set)(T : S -> Set) -> Set
Pib S T = (s : S) -> (S <1 T) ^* T s
\end{code}
Give the `gasoline-driven' interpreter for this function space,
delivering a result provided the call tree does not expand more times
than a given number.
%format gas = "\F{gas}"
\begin{spec}
gas : forall {S T} -> Nat -> Pib S T -> (s : S) -> T s + One
gas n f s = ?
\end{spec}
%if False
\begin{code}
gas : forall {S T} -> Nat -> Pib S T -> (s : S) -> T s + One
gas zero f s = ff , <>
gas {S}{T} (suc n) f s = run (f s) where
  run : forall {X} -> (S <1 T) ^* X -> X + One
  run <$ (tt , x) , _ $> = tt , x
  run <$ (ff , s) , k $> with gas n f s
  ... | tt , t = run (k t)
  ... | ff , _ = ff , <>
\end{code}
%endif
Feel free to implement reduction for the untyped
$\lambda$-calculus, or some other model of computation, as a recursive
function in this way.
\end{exe}

\paragraph{Turing completeness} To say that Agda fails to be Turing complete
is manifest nonsense. It does not stop you writing general recursive programs.
It does not stop you feeding them to a client who is willing to risk running
them. It does stop you giving a general recursive program a type which
claims it is guaranteed to terminate, nor can you persuade Agda
to execute such a program unboundedly in the course of checking a type.
It is not unusual for typecheckers to refuse to run general recursive
type-level programs. So the situation is \emph{not} that we give up power
for totality. Totality buys us a degree of honesty which partial languages
just discard.


\section{Derivatives of Containers}

We have
\[
  |<! S <1 P !>c X = Sg S \ s -> P s -> X|
\]
but we could translate the right-hand side into a more mathematical notation
and observe that a container is something a bit like a power series:
\[
  |<! S <1 P !>c X =| \sum_{|s:S|}|X|^{(|P| |s|)}
\]

We might imagine computing a formal derivative of such a series,
`multiplying down by each index, then subtracting one', but we are not
merely counting data---they have individual existences. Let us define
a kind of `dependent decrement', subtracting a \emph{particular}
element from a type.
\begin{code}
_-_ : (X : Set)(x : X) -> Set
X - x = Sg X \ x' -> x' == x -> Zero
\end{code}
That is, an element of |X - x| is some element for |X| which is known to be
other than |x|.

We may now define the formal derivative of a container.
%format der = "\F{\partial}"
\begin{code}
der : Con -> Con
der (S <1 P) = Sg S P <1 vv \ s p -> P s - p
\end{code}
The shape of the derivative is the pair of a shape with one position,
which we call the `hole', and the positions in the derivative are
`everywhere but the hole'.

%format plug = "\F{plug}"
\begin{exe}[|plug|]
Exhibit a container morphism which witnesses the ability to
fill the hole, provided equality on positions is decidable.
\begin{spec}
plug :  forall {C} -> ((s : Sh C)(p p' : Po C s) -> Dec (p == p')) ->
        (der C *c Ic) -c> C
plug {C} poeq? = ?
\end{spec}
%if False
\begin{code}
plug :  forall {C} -> ((s : Sh C)(p p' : Po C s) -> Dec (p == p')) ->
        (der C *c Ic) -c> C
plug {C} poeq? = (fst o fst) , \ { ((s , p) , _) p' -> help s p p' } where
  help : (s : Sh C)(p p' : Po C s) -> (Po C s - p) + One
  help s p p' with poeq? s p' p
  help s p .p | tt , refl = ff , <>
  help s p p' | ff , no = tt , p' , no
\end{code}
%endif
\end{exe}

\begin{exe}[laws of calculus]
Check that the following laws hold at the level of mutually inverse
container morphisms.

\[\begin{array}{r@@{\quad\cong\quad}l}
|der (Kc A)| & |Kc Zero| \\
|der I|      & |Kc One| \\
|der (C +c D)| & |der C +c der D| \\
|der (C *c D)| & |(der C *c D) +c (C *c der D)| \\
|der (C oc D)| & |(der C oc D) *c der D|
\end{array}\]

What is |der (C ^*c)| ?
\end{exe}


\section{Denormalized Containers}

These may appear later.

