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
Kc A = {!!}

Ic : Con
Ic = {!!}

_+c_ : Con -> Con -> Con
(S <1 P) +c (S' <1 P') = {!!}

_*c_ : Con -> Con -> Con
(S <1 P) *c (S' <1 P') = {!!}

Sgc : (A : Set)(C : A -> Con) -> Con
Sgc A C = {!!}

Pic : (A : Set)(C : A -> Con) -> Con
Pic A C = {!!}

_oc_ : Con -> Con -> Con
(S <1 P) oc C = {!!}

_-c>_ : Con -> Con -> Set
(S <1 P) -c> (S' <1 P') = {!!}


_/c_ : forall {C C'} -> C -c> C' -> forall {X} -> <! C !>c X -> <! C' !>c X
m /c (s , k) = {!!}

data W (C : Con) : Set where
  <$_$> : <! C !>c (W C) -> W C

BT : Con
BT = {!!}

leaf : W BT
leaf = {!!}

node : W BT -> W BT -> W BT
node s t = {!!}

_^*_ : Con -> Set -> Set
C ^* X = {!!}

_-_ : (X : Set)(x : X) -> Set
X - x = Sg X \ x' -> x' == x -> Zero

der : Con -> Con
der (S <1 P) = {!!}

BTZ : Set
BTZ = List (<! der BT !>c (W BT)) * W BT

