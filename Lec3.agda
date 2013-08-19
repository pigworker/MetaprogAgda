module Lec3 where

open import Basics public
open import Vec public

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
(S <1 P) +c (S' <1 P') = (S + S') <1 (vv P <?> P')

_*c_ : Con -> Con -> Con
(S <1 P) *c (S' <1 P') = (S * S') <1 (vv \ s s' -> P s + P' s')

Sgc : (A : Set)(C : A -> Con) -> Con
Sgc A C = (Sg A (Sh o C)) <1 (vv \ a s -> Po (C a) s)

Pic : (A : Set)(C : A -> Con) -> Con
Pic A C = ((a : A) -> Sh (C a)) <1 (\ f -> Sg A \ a -> Po (C a) (f a))

_oc_ : Con -> Con -> Con
(S <1 P) oc C = Sgc S \ s -> Pic (P s) \ p -> C

_-c>_ : Con -> Con -> Set
(S <1 P) -c> (S' <1 P') = Sg (S -> S') \ f -> (s : S) -> P' (f s) -> P s

_/c_ : forall {C C'} -> C -c> C' -> forall {X} -> <! C !>c X -> <! C' !>c X
(to , fro) /c (s , k) = to s , (k o fro s)

data W (C : Con) : Set where
  <$_$> : <! C !>c (W C) -> W C

BT : Con
BT = Two <1 (Zero <?> Two)

leaf : W BT
leaf = <$ (tt , magic) $>

node : W BT -> W BT -> W BT
node s t = <$ ff , (s <?> t) $>

_^*_ : Con -> Set -> Set
C ^* X = W (Kc X +c C)

_-_ : (X : Set)(x : X) -> Set
X - x = Sg X \ x' -> x' == x -> Zero

der : Con -> Con
der (S <1 P) = Sg S P <1 vv \ s p -> P s - p

BTZ : Set
BTZ = List (<! der BT !>c (W BT)) * W BT

