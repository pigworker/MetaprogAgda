{-# OPTIONS --no-termination-check --no-positivity-check #-}
-- the notes have no such shortcuts, but lecture time is short

module Lec5 where

open import IxCon public

{- need to talk about stuff in Chapter 4 -}

  -- recap Desc
  -- mention Everywhere & Somewhere & induction
  -- show muIx
  -- mention Jacobians
  -- look more closely at Pow and Fam

-- we've been looking at constructing functors from Pow I to Pow J

-- now it's time to consider Fam instead

-- the language of finite types, closed under sums and products.

sum prod : (n : Nat) -> (Fin n -> Nat) -> Nat
sum   zero     _  = 0
sum   (suc n)  f  = f zero +Nat sum n (f o suc)
prod  zero     _  = 1
prod  (suc n)  f  = f zero *Nat sum n (f o suc)

mutual
  data FTy : Set where
    fin    : Nat -> FTy
    sg pi  : (S : FTy)(T : # S -> FTy) -> FTy

  # : FTy -> Set
  # (fin n) = Fin n
  # (sg S T) = Sg (# S) (\ s -> # (T s))
  # (pi S T) = (s : # S) -> # (T s)

  -- do it with Nat, #, then  tweak it to Set

-- handy thing
fog : forall {n} -> Fin n -> Nat
fog zero     = zero
fog (suc i)  = suc (fog i)


-- compare

data RecR : Set1 where
  <>   : RecR
  _,_  : (A : Set)(R : A -> RecR) -> RecR

<!_!>RR : RecR -> Set
<! <> !>RR     = One
<! A , R !>RR  = Sg A \ a -> <! R a !>RR

mutual

  data RecL : Set1 where
    Em : RecL
    _::_ : (R : RecL)(A : <! R !>RL -> Set)  -> RecL

  <!_!>RL : RecL -> Set
  <! Em !>RL      = One
  <! R :: A !>RL  = Sg <! R !>RL A



-- mention manifest fields

-- but now, a serious universe

mutual
  data TU : Set where
    Zero' One' Two' : TU
    -- more to follow

  <!_!>TU : TU -> Set
  <! Zero'        !>TU  = Zero
  <! One'         !>TU  = One
  <! Two'         !>TU  = Two
  -- more to follow

-- then make it hierachical

-- --------------------- Dybjer-Setzer encoding

data DS (I J : Set1) : Set1 where
  io  : J -> DS I J                                   -- no more fields
  sg  : (A : Set)(T : A -> DS I J) -> DS I J          -- non-rec field
  de  : (H : Set)(T : (H -> I) -> DS I J) -> DS I J

<!_!>DS : forall {I J} -> DS I J -> Fam I -> Fam J
<! io j    !>DS  Xxi
  =  One
  ,  \ { <>        -> j }
<! sg A T  !>DS  Xxi
  = (Sg A \ a -> fst (<! T a !>DS Xxi))
  , (\ { (a , t) -> snd (<! T a !>DS Xxi) t })
<! de H T !>DS (X , xi)
  = (Sg (H -> X) \ hx -> fst (<! T (xi o hx) !>DS (X , xi)))
  , (\ { (hx , t) -> snd (<! T (xi o hx) !>DS (X , xi)) t })

mutual  -- fails positivity check and termination check

  data DataDS {I}(D : DS I I) : Set where
    <$_$> : fst (<! D !>DS (DataDS D , <!_!>ds)) -> DataDS D

  <!_!>ds : {I : Set1}{D : DS I I} -> DataDS D -> I
  <!_!>ds {D = D} <$ ds $> = snd (<! D !>DS (DataDS D , <!_!>ds)) ds

-- mention bind

coDS : forall {I J K} -> DS J K -> DS I J -> DS I K
coDS E D = {!!}

{-
PiF :  (S : Set){J : S -> Set1}(T : (s : S) -> Fam (J s)) ->
       Fam ((s : S) -> J s)
PiF S T = {!!}

SgF :  {I : Set1}(S : Fam I){J : I -> Set1}(T : (i : I) -> Fam (J i)) ->
       Fam (Sg I J)
SgF S T = {!!}
-}

mutual

  data Irish (I : Set1) : Set1 where
    io  : Irish I
    -- more to follow

  Info : forall {I} -> Irish I -> Set1
  Info {I} io    = I
  -- more to follow

Node : forall {I}(T : Irish I) -> Fam I -> Fam (Info T)
Node io        X  =  X
-- more to follow

IF : Set1 -> Set1 -> Set1
IF I J = Sg (Irish I) \ T -> Info T -> J

<!_!>IF : forall {I J} -> IF I J -> Fam I -> Fam J
<! T , d !>IF X = d $F Node T X

mutual -- fails positivity and termination checks

  data DataIF {I}(F : IF I I) : Set where
    <$_$> : fst (<! F !>IF (DataIF F , <!_!>if)) -> DataIF F

  <!_!>if : forall {I}{F : IF I I} -> DataIF F -> I
  <!_!>if {F = F} <$ ds $> = snd (<! F !>IF (DataIF F , <!_!>if)) ds
