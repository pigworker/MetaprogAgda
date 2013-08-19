module Lec4 where

open import Basics public
open import Vec public


record _i>_ (I J : Set) : Set1 where
  constructor _<1_$_
  field
    Sh : J        -> Set
    Po : (j : J)  -> Sh j -> Set
    ri : (j : J)(s : Sh j)(p : Po j s) -> I
  <!_!>i : (I -> Set) -> (J -> Set)
  <!_!>i X j = Sg (Sh j) \ s -> (p : Po j s) -> X (ri j s p)
open _i>_ public

data Tree {J : Set}(C : J i> J)(j : J) : Set where
  <$_$> : <! C !>i (Tree C) j -> Tree C j

NatC : One i> One
NatC = ((\ _ -> Two)) <1 (\ _ -> Zero <?> One) $ _

zeroC : Tree NatC <>
zeroC = <$ (tt , magic) $>


sucC : Tree NatC <> -> Tree NatC <>
sucC n = <$ (ff , (\ _ -> n)) $>


zeroC' : Tree NatC <>
zeroC' = <$ (tt , \ _ -> sucC zeroC) $>


VecC : Set -> Nat i> Nat
VecC X = VS <1 VP $ Vr where  -- depending on the length
  VS : Nat -> Set
  VS zero = One
  VS (suc n) = X
  VP : (n : Nat) -> VS n -> Set
  VP zero s = Zero
  VP (suc n) s = One
  Vr : (n : Nat)(s : VS n)(p : VP n s) -> Nat
  Vr zero s ()
  Vr (suc n) s <> = n

vnil : forall {X} -> Tree (VecC X) zero
vnil = <$ <> , (\ ()) $>

vcons :  forall {X n} -> X -> Tree (VecC X) n -> Tree (VecC X) (suc n)
vcons x xs = <$ (x , (\ _ -> xs)) $>

data Desc {l}(I : Set l) : Set (lsuc l) where
  var   : I -> Desc I
  sg pi : (A : Set l)(D : A -> Desc I) -> Desc I
  _*D_  : Desc I -> Desc I -> Desc I
  kD    : Set l -> Desc I

<!_!>D : forall {l}{I : Set l} -> Desc I -> (I -> Set l) -> Set l
<! (var i) !>D X = X i
<! (sg A D) !>D X = Sg A \ a -> <! D a !>D X
<! (pi A D) !>D X = (a : A) -> <! D a !>D X
<! (D *D E) !>D X = <! D !>D X * <! E !>D X
<! (kD A) !>D X = A

data Data {l}{J : Set l}(F : J -> Desc J)(j : J) : Set l where
  <$_$> : <! F j !>D (Data F) -> Data F j

vecD : Set -> Nat -> Desc Nat
vecD X zero = kD One
vecD X (suc n) = kD X *D var n


