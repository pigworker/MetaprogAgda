module Exe3 where

open import Proving public
open import NormF public

record Con : Set1 where
  constructor _<1_
  field
    Sh  : Set             -- a set of shapes
    Po  : Sh -> Set       -- a family of positions
  <!_!>c : Set -> Set
  <!_!>c X = Sg Sh \ s -> Po s -> X
open Con public
infixr 1 _<1_

Kc : Set -> Con
Kc A = A <1 \ _ -> Zero

Ic : Con
Ic = One <1 \ _ -> One

_+c_ : Con -> Con -> Con
(S <1 P) +c (S' <1 P') = (S + S') <1 vv P <?> P'

_*c_ : Con -> Con -> Con
(S <1 P) *c (S' <1 P') = (S * S') <1 vv \ s s' -> P s + P' s'

Sgc : (A : Set)(C : A -> Con) -> Con
Sgc A C = (Sg A \ a -> Sh (C a)) <1 vv \ a s -> Po (C a) s

Pic : (A : Set)(C : A -> Con) -> Con
Pic A C = ((a : A) -> Sh (C a)) <1 \ f -> Sg A \ a -> Po (C a) (f a)

_oc_ : Con -> Con -> Con
(S <1 P) oc C = Sgc S \ s -> Pic (P s) \ p -> C

{- {exe}[containers are endofunctors]
Check that containers yield endofunctors which obey the laws. -}

conEndoFunctor : {C : Con} -> EndoFunctor <! C !>c
conEndoFunctor {S <1 P} = {!!}

conEndoFunctorOKP : {C : Con} -> EndoFunctorOKP <! C !>c
conEndoFunctorOKP {S <1 P} = {!!}

{- {exe}[closure properties]
Check that the meanings of the operations on containers are justified
by their interpretations as functors. -}


-----------------------------------------------------------------------
_-c>_ : Con -> Con -> Set
(S <1 P) -c> (S' <1 P') = Sg (S -> S') \ f -> (s : S) -> P' (f s) -> P s

_/c_ : forall {C C'} -> C -c> C' -> forall {X} -> <! C !>c X -> <! C' !>c X
(to , fro) /c (s , k) = to s , k o fro s

{- {exe}[representing natural transformations]
Check that you can represent any natural transformation between
containers as a container morphism. -}

morphc : forall {C C'} -> (forall {X} -> <! C !>c X -> <! C' !>c X) -> C -c> C'
morphc f = {!!}

{- {exe}[identity and composition]
Check that you can define identity and composition for container morphisms. -}

idmc : forall {C} -> C -c> C
idmc = {!!}

_omc_ : forall {C D E} -> (D -c> E) -> (C -c> D) -> (C -c> E)
e omc d = {!!}


------------------------------------------------------------------------
data W (C : Con) : Set where
  <$_$> : <! C !>c (W C) -> W C

{- {exe}[natural numbers]
Define natural numbers as a |W|-type. Implement the constructors.
Hint: |magic : Zero -> {A : Set} -> A|.
Implement primitive recursion and use it to implement addition. -}

NatW : Set
NatW = W {!!}

zeroW : NatW
zeroW = <$ {!!} $>

sucW : NatW -> NatW
sucW n = <$ {!!} $>

precW : forall {l}{T : Set l} -> T -> (NatW -> T -> T) -> NatW -> T
precW z s n = {!!}

addW : NatW -> NatW -> NatW
addW x y = precW {!!} {!!} x

{- How many different implementations of |zeroW| can you find?
Meanwhile, discover for yourself why an attempt to establish the
induction principle is a fool's errand. -}

indW :  forall {l}(P : NatW -> Set l) ->
        P zeroW ->
        ((n : NatW) -> P n -> P (sucW n)) ->
        (n : NatW) -> P n
indW P z s n = {!!}


_^*_ : Con -> Set -> Set
C ^* X = W (Kc X +c C)

{- {exe}[free monad]
Construct the components for -}

freeMonad : (C : Con) -> Monad (_^*_ C)
freeMonad C = {!!}

{- {exe}[free monad closure]
Define an operator -}

_^*c : Con -> Con
_^*c C = {!!}

{- and exhibit an isomorphism 
\[
  |C ^* X| \cong |<! C ^*c !>c X|
\] -}

{- {exe}[general recursion]
Define the monadic computation which performs one command-response
interaction: -}

call : forall {C} -> (s : Sh C) -> C ^* Po C s
call s = {!!}

{-We can model\nudge{in too much detail}, the general recursive function
space as the means to perform finite, on demand expansion of call trees. -}

Pib : (S : Set)(T : S -> Set) -> Set
Pib S T = (s : S) -> (S <1 T) ^* T s

{- Give the `gasoline-driven' interpreter for this function space,
delivering a result provided the call tree does not expand more times
than a given number. -}

gas : forall {S T} -> Nat -> Pib S T -> (s : S) -> T s + One
gas n f s = {!!}

{- Feel free to implement reduction for the untyped
$\lambda$-calculus, or some other model of computation, as a recursive
function in this way. -}

----------------------------------------------------------------------
_-_ : (X : Set)(x : X) -> Set
X - x = Sg X \ x' -> x' == x -> Zero

der : Con -> Con
der (S <1 P) = Sg S P <1 vv \ s p -> P s - p

{- {exe}[|plug|]
Exhibit a container morphism which witnesses the ability to
fill the hole, provided equality on positions is decidable. -}

plug :  forall {C} -> ((s : Sh C)(p p' : Po C s) -> Dec (p == p')) ->
        (der C *c Ic) -c> C
plug {C} poeq? = {!!}

{- {exe}[laws of calculus]
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
-}

