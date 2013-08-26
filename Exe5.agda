module Exe5 where

open import Vec public
open import Normal public
open import IxCon public

-----------------------------------------------------------------------
{- {exe}[|FreshList|]
By means of a suitable choice of recursive interpretation, fill the |?|
with a condition which ensures that |FreshList|s have \emph{distinct}
elements. Try to make sure that, for any concrete |FreshList|, |ok|
can be inferred trivially. -}

module FRESHLIST (X : Set)(Xeq? : (x x' : X) -> Dec (x == x')) where
  mutual
    data FreshList : Set where
      []   : FreshList
      _,_  : (x : X)(xs : FreshList){ok : {!!}} -> FreshList


-----------------------------------------------------------------------
data RecR : Set1 where
  <>   : RecR
  _,_  : (A : Set)(R : A -> RecR) -> RecR

<!_!>RR : RecR -> Set
<! <> !>RR     = One
<! A , R !>RR  = Sg A \ a -> <! R a !>RR

{- {exe}[projection from |RecR|]
Show how to compute the size of a record, then define the projections,
first of types, then of values. -}

sizeRR : (R : RecR) -> <! R !>RR -> Nat
sizeRR R r = {!!}

TyRR : (R : RecR)(r : <! R !>RR) -> Fin (sizeRR R r) -> Set
TyRR R r i = {!!}

vaRR : (R : RecR)(r : <! R !>RR)(i : Fin (sizeRR R r)) -> TyRR R r i
vaRR R r i = {!!}

---------------------------------------------------------------------
mutual

  data RecL : Set1 where
    Em : RecL
    _::_ : {n : Nat}(R : RecL)(A : <! R !>RL -> Set)  -> RecL

  <!_!>RL : RecL -> Set
  <! Em !>RL      = One
  <! R :: A !>RL  = Sg <! R !>RL A

{- {exe}[projection from |RecL|]
Show how to compute the size of a |RecL| without knowing the
individual record. Show how to interpret a projection as a
function from a record, first for types, then values. -}

sizeRL : RecL -> Nat
sizeRL R = {!!}

TyRL : (R : RecL) -> Fin (sizeRL R) -> <! R !>RL -> Set
TyRL R i = {!!}

vaRL : (R : RecL)(i : Fin (sizeRL R))(r : <! R !>RL) -> TyRL R i r
vaRL R i = {!!}

{- {exe}[truncation]
Show how to truncate a record signature from a given field and compute the
corresponding projection on structures. -}

TruncRL : (R : RecL) -> Fin (sizeRL R) -> RecL
TruncRL R i = {!!}

truncRL : (R : RecL)(i : Fin (sizeRL R)) -> <! R !>RL -> <! TruncRL R i !>RL
truncRL R i = {!!}

---------------------------------------------------------------------
data Manifest {A : Set} : A -> Set where
  <$_$> : (a : A) -> Manifest a

mutual

  data RecM : Nat -> Set1 where
    Em         : RecM zero
    _::_       : {n : Nat}(R : RecM n)  (A : <! R !>RM -> Set) -> RecM (suc n)
    _:<:_:>:_  : {n : Nat}(R : RecM n)  (A : <! R !>RM -> Set)
                                        (a : (r : <! R !>RM) -> A r) ->
                                        RecM (suc n)

  <!_!>RM : {n : Nat} -> RecM n -> Set
  <! Em !>RM             = One
  <! R :: A !>RM         = Sg <! R !>RM A
  <! R :<: A :>: a !>RM  = Sg <! R !>RM (Manifest o a)

{- {exe}[projection from |RecM|]
Implement projection for |RecM|. -}
TyRM : {n : Nat}(R : RecM n) -> Fin n -> <! R !>RM -> Set
TyRM R i = {!!}

vaRM : {n : Nat}(R : RecM n)(i : Fin n)(r : <! R !>RM) -> TyRM R i r
vaRM R i = {!!}
{- Be careful not to recompute the value of a manifest field. -}

{- {exe}[record extension]
When building libraries of structures, we are often concerned with the idea
of one record signature being the extension of another. The following -}

mutual

  data REx : {n m : Nat} -> RecM n -> RecM m -> Set1 where
    Em : REx Em Em

  rfog :  forall {n m}{R : RecM n}{R' : RecM m}(X : REx R R') ->
          <! R' !>RM -> <! R !>RM
  rfog Em <> = <>

{- describes evidence |REx R R'| that |R'| is an extension of |R|,
interpreted by |rfog| as a map from |<! R' !>RM| back to |<! R
!>RM|. Unfortunately, it captures only the fact that the empty record
extends itself.  Extend |REx| to allow retention of every field,
insertion of new fields, and conversion of abstract to manifest
fields. -}


---------------------------------------------------------------------
mutual

  data NU (X : Fam Set) : Set where
    U' : NU X
    El' : fst X -> NU X
    Nat' : NU X
    Pi' : (S : NU X)(T : <! S !>NU -> NU X) -> NU X

  <!_!>NU : forall {X} -> NU X -> Set
  <!_!>NU {U , El}  U'       = U
  <!_!>NU {U , El}  (El' T)  = El T
  <! Nat'     !>NU           = Nat
  <! Pi' S T  !>NU           = (s : <! S !>NU) -> <! T s !>NU

EMPTY : Fam Set
EMPTY = Zero , \ ()

LEVEL : Nat -> Fam Set
LEVEL zero     = NU EMPTY , <!_!>NU
LEVEL (suc n)  = NU (LEVEL n) , <!_!>NU

{- {exe}[|Nat -> Nat|]
Find five names for |Nat -> Nat| in |fst (LEVEL 1)|. -}

infixr 4 _,_
nat2nat : List (fst (LEVEL 1))
nat2nat
  =  {!!}
  ,  {!!}
  ,  {!!}
  ,  {!!}
  ,  {!!}
  ,  <>

---------------------------------------------------------------------
mutual

  data HU {n}(U : Fin n -> Set) : Set where
    U'    : Fin n -> HU U
    Nat'  : HU U
    Pi'   : (S : HU U)(T : <! S !>HU -> HU U) -> HU U

  <!_!>HU : forall {n}{U : Fin n -> Set} -> HU U -> Set
  <!_!>HU {U = U} (U' i)  = U i
  <! Nat'     !>HU        = Nat
  <! Pi' S T  !>HU        = (s : <! S !>HU) -> <! T s !>HU

HPREDS : (n : Nat) -> Fin n -> Set
HPREDS zero     ()
HPREDS (suc n)  zero     = HU (HPREDS n)
HPREDS (suc n)  (suc i)  = HPREDS n i

HSET : Nat -> Set
HSET n = HU (HPREDS n)

{- {exe}[fool's errand]
Find out what breaks when you try to implement cumulativity.
What equation do you need to hold? Can you prove it? -}

Cumu : (n : Nat)(T : HSET n) -> HSET (suc n)
Cumu n T = {!!}

---------------------------------------------------------------------
data DS (I J : Set1) : Set1 where
  io  : J -> DS I J                                   -- no more fields
  sg  : (S : Set)(T : S         -> DS I J) -> DS I J  -- ordinary field
  de  : (H : Set)(T : (H -> I)  -> DS I J) -> DS I J  -- child field

<!_!>DS : forall {I J} -> DS I J -> Fam I -> Fam J
<! io j    !>DS  Xxi
  =  One
  ,  \ { <>        -> j }
<! sg S T  !>DS  Xxi
  =  (Sg S \ s -> fst (<! T s !>DS Xxi))
  ,  \ { (s , t)   -> snd (<! T s !>DS Xxi) t }
<! de H T  !>DS  (X , xi)
  =  (Sg (H -> X) \ hx -> fst (<! T (xi o hx) !>DS (X , xi)))
  ,  \ { (hx , t)  -> snd (<! T (xi o hx) !>DS (X , xi)) t }

{- [|idDS|]
A morphism from |(X , xi)| to |(Y , yi)| in |Fam I| is a function |f : X -> Y|
such that |xi = yi o f|.
Construct a code for the identity functor on |Fam I|, being -}

idDS : {I : Set1} -> DS I I
idDS = {!!}

{- such that
\[
  |<! idDS !>DS| \cong |id|
\]
in the sense that both take isomorphic inputs to isomorphic outputs. -}

mutual

  data DataDS {I}(D : DS I I) : Set where
    <$_$> : NoDS D D -> DataDS D

  <!_!>ds : {I : Set1}{D : DS I I} -> DataDS D -> I
  <!_!>ds {D = D} <$ ds $> = DeDS D D ds

  NoDS : {I : Set1}(D D' : DS I I) -> Set
  NoDS D (io i)    = One
  NoDS D (sg S T)  = Sg S \ s ->                 NoDS D (T s)
  NoDS D (de H T)  = Sg (H -> DataDS D) \ hd ->  NoDS D (T (\ h -> <! hd h !>ds))

  DeDS : {I : Set1}(D D' : DS I I) -> NoDS D D' -> I
  DeDS D (io i)    <>        = i
  DeDS D (sg S T)  (s , t)   = DeDS D (T s) t
  DeDS D (de H T)  (hd , t)  = DeDS D (T (\ h -> <! hd h !>ds)) t


{- {exe}[encode |TU|]
Construct an encoding of |TU| in |DS Set Set|. -}

{- {exe}[|bindDS| and its meaning]
Implement the appropriate |bindDS| operator, corresponding to substitution
at |iota|. -}

bindDS : forall {I J K} -> DS I J -> (J -> DS I K) -> DS I K
bindDS T U = {!!}

{- Show that |bindDS| corresponds to a kind of |Sg| by implementing
pairing and projections: -}

pairDS :  forall {I J K}(T : DS I J)(U : J -> DS I K){X : Fam I} ->
          (t : fst (<! T !>DS X))(u : fst (<! U (snd (<! T !>DS X) t) !>DS X))
          -> fst (<! bindDS T U !>DS X)
pairDS T U t u = {!!}

projDS :  forall {I J K}(T : DS I J)(U : J -> DS I K){X : Fam I} ->
          fst (<! bindDS T U !>DS X) ->
          Sg (fst (<! T !>DS X)) \ t -> fst (<! U (snd (<! T !>DS X) t) !>DS X)
projDS T U tu = {!!}

{- {exe}[composition for |DS|]
This is an open problem. Construct -}

coDS : forall {I J K} -> DS J K -> DS I K -> DS I K
coDS E D = {!!}

{- such that
\[
  |<! coDS E D !>DS| \cong |<! E !>DS o <! D !>DS|
\]
Alternatively, find a counterexample which wallops the very possibility of
|coDS|. -}

----------------------------------------------------------------------------
mutual

  data Irish (I : Set1) : Set1 where
    io  : Irish I
    ka  : Set -> Irish I
    pi  : (S : Set)(T : S -> Irish I) -> Irish I
    sg  : (S : Irish I)(T : Info S -> Irish I) -> Irish I

  Info : forall {I} -> Irish I -> Set1
  Info {I} io    = I
  Info (ka A)    = Up A
  Info (pi S T)  = (s : S) -> Info (T s)
  Info (sg S T)  = Sg (Info S) \ s -> Info (T s)

PiF :  (S : Set){J : S -> Set1}(T : (s : S) -> Fam (J s)) ->
       Fam ((s : S) -> J s)
PiF S T  = ((s : S) -> fst (T s)) , \ f s -> snd (T s) (f s)

SgF :  {I : Set1}(S : Fam I){J : I -> Set1}(T : (i : I) -> Fam (J i)) ->
       Fam (Sg I J)
SgF S T  =  Sg (fst S) (fst o (T o snd S))
         ,  \ { (s , t) -> snd S s , snd (T (snd S s)) t }

Node : forall {I}(T : Irish I) -> Fam I -> Fam (Info T)
Node io        X  =  X
Node (ka A)    X  =  A , up
Node (pi S T)  X  =  PiF S \ s -> Node (T s) X
Node (sg S T)  X  =  SgF (Node S X) \ iS -> Node (T iS) X

IF : Set1 -> Set1 -> Set1
IF I J = Sg (Irish I) \ T -> Info T -> J

<!_!>IF : forall {I J} -> IF I J -> Fam I -> Fam J
<! T , d !>IF X = d $F Node T X

mutual

  data DataIF {I}(F : IF I I) : Set where
    <$_$> : NoIF F (fst F) -> DataIF F

  <!_!>if : forall {I}{F : IF I I} -> DataIF F -> I
  <!_!>if {F = F} <$ rs $> = snd F (DeIF F (fst F) rs)

  NoIF : forall {I}(F : IF I I)(T : Irish I) -> Set
  NoIF F io        = DataIF F
  NoIF F (ka A)    = A
  NoIF F (pi S T)  = (s : S) -> NoIF F (T s)
  NoIF F (sg S T)  = Sg (NoIF F S) \ s -> NoIF F (T (DeIF F S s))

  DeIF : forall {I}(F : IF I I)(T : Irish I) -> NoIF F T -> Info T
  DeIF F io        r        = <! r !>if
  DeIF F (ka A)    a        = up a
  DeIF F (pi S T)  f        = \ s -> DeIF F (T s) (f s)
  DeIF F (sg S T)  (s , t)  = let s' = DeIF F S s in s' , DeIF F (T s') t


{- {exe}[Irish |TU|]
Give a construction for the |TU| universe as a description-decoder pair in
|IF Set Set|. -}

{- {exe}[Irish-to-Swedish]
Show how to define -}

DSIF : forall {I J} -> DS I J -> IF I J
DSIF T = {!!}

{- such that
\[
  |<! DSIF T !>DS| \cong |<! T !>IF|
\] -}

{- {exe}[|subIF|]
Construct a substitution operator for |Irish J| with a refinement
of the following type. -}

subIF : forall {I J}(T : Irish J)(F : IF I J) -> Sg (Irish I) {!!}
subIF T F = {!!}

{- Hint: you will find out what you need in the |sg| case. -}

{- {exe}[|coIF|]
Now define composition for Irish IR functors. -}

coIF : forall {I J K} -> IF J K -> IF I J -> IF I K
coIF G F = {!!}

