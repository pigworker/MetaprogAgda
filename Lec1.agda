module Lec1 where

open import Basics

-- Lists and shape invariants

data List (X : Set) : Set where
  <>    :                 List X
  _,_   : X -> List X ->  List X

infixr 4 _,_

zip0 : {S T : Set} -> List S -> List T -> List (S * T)
zip0 <> <> = <>
zip0 <> (x , ts) = <>
zip0 (x , ss) <> = <>
zip0 (s , ss) (t , ts) = (s , t) , zip0 ss ts


data Nat : Set where
  zero  :         Nat
  suc   : Nat ->  Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

length : {X : Set} -> List X -> Nat
length <>        = zero
length (x , xs)  = suc (length xs)

-- what is the type of the zip we want?
{-
zip' : {S T : Set}(ss : List S)(ts : List T) ->
       length ss == length ts ->
       Sg (List (S * T)) \ sts -> length sts == length ss
zip' <> <> q = <> , refl
zip' <> (x , ts) ()
zip' (x , ss) <> ()
zip' (s , ss) (t , ts) q with zip' ss ts {!!}
zip' (s , ss) (t , ts) q | sts , q' = ((s , t) , sts) , {!!}
-}

-- vectors

data Vec (X : Set) : Nat -> Set where
  <>   :                               Vec X zero
  _,_  : {n : Nat} -> X -> Vec X n ->  Vec X (suc n)

zip1 : forall {n S T} -> Vec S n -> Vec T n -> Vec (S * T) n
zip1 <> <> = <>
zip1 (x , ss) (x₁ , ts) = (x , x₁) , zip1 ss ts

vec : forall {n X} -> X -> Vec X n
vec {zero} x = <>
vec {suc n} x = x , vec x

vapp :  forall {n S T} -> Vec (S -> T) n -> Vec S n -> Vec T n
vapp <> <> = <>
vapp (f , fs) (s , ss) = f s , vapp fs ss

{-
zip2 : forall {n S T} -> Vec S n -> Vec T n -> Vec (S * T) n
zip2 ss ts = {!!}
-}

-- applicative and traversable structure

record EndoFunctor (F : Set -> Set) : Set1 where
  field
    map  : forall {S T} -> (S -> T) -> F S -> F T
open EndoFunctor {{...}} public

record Applicative (F : Set -> Set) : Set1 where
  infixl 2 _<*>_
  field
    pure    : forall {X} -> X -> F X
    _<*>_   : forall {S T} -> F (S -> T) -> F S -> F T
  applicativeEndoFunctor : EndoFunctor F
  applicativeEndoFunctor = record { map = _<*>_ o pure }
open Applicative {{...}} public

applicativeVec  : forall {n} -> Applicative \ X -> Vec X n
applicativeVec  = record { pure = vec; _<*>_ = vapp }
endoFunctorVec  : forall {n} -> EndoFunctor \ X -> Vec X n
endoFunctorVec  = applicativeEndoFunctor

applicativeFun : forall {S} -> Applicative \ X -> S -> X
applicativeFun = record
  {  pure    = \ x s -> x              -- also known as K (drop environment)
  ;  _<*>_   = \ f a s -> f s (a s)    -- also known as S (share environment)
  }


applicativeId : Applicative id
applicativeId = {!!}

applicativeComp : forall {F G} ->
  Applicative F -> Applicative G -> Applicative (F o G)
applicativeComp aF aG = {!!}

record Monoid (X : Set) : Set where
  infixr 4 _&_
  field
    neut  : X
    _&_   : X -> X -> X
  monoidApplicative : Applicative \ _ -> X
  monoidApplicative = {!!}
open Monoid {{...}} public -- it's not obvious that we'll avoid ambiguity

record Traversable (F : Set -> Set) : Set1 where
  field
    traverse :  forall {G S T}{{AG : Applicative G}} ->
                (S -> G T) -> F S -> G (F T)
  traversableEndoFunctor : EndoFunctor F
  traversableEndoFunctor = record { map = traverse }
open Traversable {{...}} public

traversableVec : {n : Nat} -> Traversable \ X -> Vec X n
traversableVec = record { traverse = vtr } where
  vtr :  forall {n G S T}{{_ : Applicative G}} ->
         (S -> G T) -> Vec S n -> G (Vec T n)
  vtr {{aG}} f <>        = pure {{aG}} <>
  vtr {{aG}} f (s , ss)  = pure {{aG}} _,_ <*> f s <*> vtr f ss

crush :  forall {F X Y}{{TF : Traversable F}}{{M : Monoid Y}} ->
         (X -> Y) -> F X -> Y
crush {{M = M}} =
  traverse {T = One}{{AG = monoidApplicative {{M}}}}  -- |T| arbitrary


record Normal : Set1 where
  constructor _/_
  field
    Shape  : Set
    size   : Shape -> Nat
  <!_!>N : Set -> Set
  <!_!>N X = Sg Shape \ s -> Vec X (size s)
open Normal public
infixr 0 _/_

VecN : Nat -> Normal
VecN n = One / \ _ -> n

ListN : Normal
ListN = Nat / id


-- Normal Functor Kit

K : Set -> Normal
K A = A / (\ a -> 0)

I : Normal
I = One / (\ _ -> 1)

_+Nat_ : Nat -> Nat -> Nat
x +Nat y = {!!}

_+N_ : Normal -> Normal -> Normal
(ShF / szF) +N (ShG / szG) = {!!}

_*N_ : Normal -> Normal -> Normal
(ShF / szF) *N (ShG / szG) = (ShF * ShG) / vv (\ fs gs -> szF fs +Nat szG gs)

{-
nInj : forall {X}(F G : Normal) -> <! F !>N X + <! G !>N X -> <! F +N G !>N X
nInj F G forg = {!!}

data _^-1_ {S T : Set}(f : S -> T) : T -> Set where
  from : (s : S) -> f ^-1 f s

nCase : forall {X} F G (s : <! F +N G !>N X) -> nInj F G ^-1 s
nCase F G fng = {!!}

nOut : forall {X}(F G : Normal) -> <! F +N G !>N X -> <! F !>N X + <! G !>N X
nOut F G xs' = {!!}

nPair : forall {X}(F G : Normal) -> <! F !>N X * <! G !>N X -> <! F *N G !>N X
nPair F G fxgx = {!!}

-- Normal and Traversable
-}

sumMonoid : Monoid Nat
sumMonoid = {!!}

normalTraversable : (F : Normal) -> Traversable <! F !>N
normalTraversable F = record
  { traverse = \ {{aG}} f -> vv \ s xs -> pure {{aG}}  (_,_ s) <*> traverse f xs }

sizeT : forall {F}{{TF : Traversable F}}{X} -> F X -> Nat
sizeT = crush (\ _ -> 1)

normalT : forall F {{TF : Traversable F}} -> Normal
normalT F = F One / sizeT

-- fixpoints of normal functors

data Tree (N : Normal) : Set where
  <$_$> : <! N !>N (Tree N) -> Tree N

NatN : Normal
NatN = K One +N I

NatT : Set
NatT = Tree NatN

zeroN : NatT
zeroN = <$ ({!!} , {!!}) $>

sucN : NatT -> NatT
sucN n = {!!}

{-
-- theorem-proving
-- talk about equality


record MonoidOK X {{M : Monoid X}} : Set where
  field
    absorbL  : (x : X) ->      neut & x == x
    absorbR  : (x : X) ->      x & neut == x
    assoc    : (x y z : X) ->  (x & y) & z == x & (y & z)

natMonoidOK : MonoidOK Nat
natMonoidOK = record
  {  absorbL  = \ _ -> refl
  ;  absorbR  = _+zero
  ;  assoc    = assoc+
  }  where    -- see below
  _+zero : forall x -> x +Nat zero == x
  n   +zero                  = {!!}
  assoc+ : forall x y z -> (x +Nat y) +Nat z  == x +Nat (y +Nat z)
  assoc+ x y z = {!!}

_=!!_>>_ : forall {l}{X : Set l}(x : X){y z} -> x == y -> y == z -> x == z
_ =!! refl >> q = q

_<<_!!=_ : forall {l}{X : Set l}(x : X){y z} -> y == x -> y == z -> x == z
_ << refl !!= q = q

_<QED> : forall {l}{X : Set l}(x : X) -> x == x
x <QED> = refl

infixr 1 _=!!_>>_ _<<_!!=_ _<QED>

cong : forall {k l}{X : Set k}{Y : Set l}(f : X -> Y){x y} -> x == y -> f x == f y
cong f refl = refl

_=1=_ :  forall {l}{S : Set l}{T : S -> Set l}
         (f g : (x : S) -> T x) -> Set l
f =1= g = forall x -> f x == g x
infix 1 _=1=_

record EndoFunctorOKP F {{FF : EndoFunctor F}} : Set1 where
  field
    endoFunctorId  : forall {X} ->
      map {{FF}}{X} id =1= id
    endoFunctorCo  : forall {R S T}(f : S -> T)(g : R -> S) ->
      map {{FF}} f o map g =1= map (f o g)

record ApplicativeOKP F {{AF : Applicative F}} : Set1 where
  field
    lawId :   forall {X}(x : F X) ->
      pure {{AF}} id <*> x == x
    lawCo :   forall {R S T}(f : F (S -> T))(g : F (R -> S))(r : F R) ->
      pure {{AF}} (\ f g -> f o g) <*> f <*> g <*> r == f <*> (g <*> r)
    lawHom :  forall {S T}(f : S -> T)(s : S) ->
      pure {{AF}} f <*> pure s == pure (f s)
    lawCom :  forall {S T}(f : F (S -> T))(s : S) ->
      f <*> pure s == pure {{AF}} (\ f -> f s) <*> f
  applicativeEndoFunctorOKP : EndoFunctorOKP F {{applicativeEndoFunctor}}
  applicativeEndoFunctorOKP = record
    {  endoFunctorId = lawId
    ;  endoFunctorCo = \ f g r ->
         {!!}
    }

-}