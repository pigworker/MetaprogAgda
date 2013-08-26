module Lec6 where

open import IR public

data Favourite : (Nat -> Nat) -> Set where
  favourite : Favourite (\ x -> zero +Nat x)

plusZero : forall x -> zero +Nat x == x +Nat zero
plusZero x = {!!}

closedFact : (\ x -> zero +Nat x) == (\ x -> x +Nat zero)
closedFact = extensionality _ _ plusZero

myTerm = subst closedFact Favourite favourite


-- remark on intensional predicates
-- remark on the need for a more type-based computation mechanism

mutual

  EQ : (X Y : TU) -> TU * (<! X !>TU -> <! Y !>TU -> TU)

  _<->_ : TU -> TU -> TU
  X <-> Y = fst (EQ X Y)

  Eq : (X : TU)(x : <! X !>TU) -> (Y : TU)(y : <! Y !>TU) -> TU
  Eq X x Y y = snd (EQ X Y) x y

  EQ X Y = {!!}

coe : (X Y : TU) -> <! X <-> Y !>TU -> <! X !>TU -> <! Y !>TU

postulate
  coh :  (X Y : TU)(Q : <! X <-> Y !>TU)(x : <! X !>TU) ->
         <! Eq X x Y (coe X Y Q x) !>TU

coe X Y Q x = {!!}

