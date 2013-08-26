module Lec6 where

open import IR public

data Favourite (f : Nat -> Nat) : Set where
  favourite : (\ x -> zero +Nat x) == f -> Favourite f

plusZero : forall x -> x == x +Nat zero
plusZero zero = refl
plusZero (suc x)  = cong suc (plusZero x)

closedFact : (\ x -> zero +Nat x) == (\ x -> x +Nat zero)
closedFact = extensionality _ _ plusZero

myTerm = subst closedFact Favourite (favourite refl)

help : Favourite (λ x → x +Nat 0)
help = favourite closedFact

-- remark on intensional predicates
-- remark on the need for a more type-based computation mechanism

mutual

  EQ : (X Y : TU) -> TU * (<! X !>TU -> <! Y !>TU -> TU)

  _<->_ : TU -> TU -> TU
  X <-> Y = fst (EQ X Y)

  Eq : (X : TU)(x : <! X !>TU) -> (Y : TU)(y : <! Y !>TU) -> TU
  Eq X x Y y = snd (EQ X Y) x y

  EQ Zero' Zero' = One' , \ _ _ -> One'

  EQ One' One' = One' , \ _ _ -> One'
  EQ Two' Two' = One' , (\
    { tt tt -> One'
    ; ff ff -> One'
    ; _ _ -> Zero'
    })
  EQ (Sg' X T) (Sg' Y T₁) = {!!}
  EQ (Pi' S T) (Pi' S' T') = {!!}
  EQ (Tree' X F i) (Tree' Y F₁ i₁) = {!!}
  EQ _ _ = Zero' , \ _ _ -> One'

coe : (X Y : TU) -> <! X <-> Y !>TU -> <! X !>TU -> <! Y !>TU

postulate
  coh :  (X Y : TU)(Q : <! X <-> Y !>TU)(x : <! X !>TU) ->
         <! Eq X x Y (coe X Y Q x) !>TU

coe Zero' Zero' Q x = {!!}
coe Zero' One' Q x = {!!}
coe Zero' Two' Q x = {!!}
coe Zero' (Sg' Y T) Q x = {!!}
coe Zero' (Pi' Y T) Q x = {!!}
coe Zero' (Tree' Y F i) Q x = {!!}
coe One' Zero' Q x = {!!}
coe One' One' Q x = {!!}
coe One' Two' Q x = {!!}
coe One' (Sg' Y T) Q x = {!!}
coe One' (Pi' Y T) Q x = {!!}
coe One' (Tree' Y F i) Q x = {!!}
coe Two' Zero' Q x = {!!}
coe Two' One' Q x = {!!}
coe Two' Two' Q x = {!!}
coe Two' (Sg' Y T) Q x = {!!}
coe Two' (Pi' Y T) Q x = {!!}
coe Two' (Tree' Y F i) Q x = {!!}
coe (Sg' X T) Zero' () x
coe (Sg' X T) One' Q x = {!!}
coe (Sg' X T) Two' Q x = {!!}
coe (Sg' S T) (Sg' S' T') Q (s , t) = {!!}
coe (Sg' X T) (Pi' Y T₁) Q x = {!!}
coe (Sg' X T) (Tree' Y F i) Q x = {!!}
coe (Pi' X T) Zero' Q x = {!!}
coe (Pi' X T) One' Q x = {!!}
coe (Pi' X T) Two' Q x = {!!}
coe (Pi' X T) (Sg' Y T₁) Q x = {!!}
coe (Pi' X T) (Pi' Y T₁) Q x = {!!}
coe (Pi' X T) (Tree' Y F i) Q x = {!!}
coe (Tree' X F i) Zero' Q x = {!!}
coe (Tree' X F i) One' Q x = {!!}
coe (Tree' X F i) Two' Q x = {!!}
coe (Tree' X F i) (Sg' Y T) Q x = {!!}
coe (Tree' X F i) (Pi' Y T) Q x = {!!}
coe (Tree' X F i) (Tree' Y F₁ i₁) Q x = {!!}

