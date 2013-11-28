module Lec2 where

open import Basics
open import Vec

infixr 4 _->>_
infixr 3 _!-_
infixr 3 _<:_
infixl 7 _$_

data Type : Set where
  iota  :                  Type
  _->>_  : (sig tau : Type) ->  Type

data Context : Set where
  Em    : Context
  _::_  : (Gam : Context)(sig : Type) -> Context

data _<:_ (tau : Type) : Context -> Set where
  zero  : forall {Gam}                        -> tau <: (Gam :: tau)
  suc   : forall {Gam sig}  (x : tau <: Gam)  -> tau <: (Gam :: sig)

data _!-_ : Context -> Type -> Set where

  var  : forall {Gam tau}           (x : tau <: Gam)
                               -> --------------------
                                       Gam !- tau

  -- $\lambda$-abstraction extends the context

  lam  : forall {Gam sig tau}       (b : Gam :: sig !- tau)
                               -> ---------------------------
                                      Gam !- sig ->> tau

  -- application demands a type coincidence

  _$_  : forall {Gam sig tau}       (f : Gam !- sig ->> tau)   (s : Gam !- sig)
                               -> -----------------------------------------------
                                                    Gam !- tau

[_]T : Type -> Set
[ tau ]T    = {!!}

[_]C : Context -> Set
[ Gam ]C      = {!!}

[_]v : forall {Gam tau} -> tau <: Gam -> [ Gam ]C -> [ tau ]T
[ i ]v    g = {!!}

[_]t : forall {Gam tau} -> Gam !- tau -> [ Gam ]C -> [ tau ]T
[ t ]t = {!!}

eval : forall {tau} -> Em !- tau -> [ tau ]T
eval t = [ t ]t {!!}


-- substitution with a friendly fish

Ren Sub : Context -> Context -> Set
Ren  Gam Del  = forall {tau} -> tau <: Gam -> tau <: Del
Sub  Gam Del  = forall {tau} -> tau <: Gam -> Del !- tau

_<><_ : Context -> List Type -> Context
xz <>< <>        = xz
xz <>< (x , xs)  = xz :: x <>< xs
infixl 4 _<><_

Shub : Context -> Context -> Set
Shub Gam Del = forall Xi -> Sub (Gam <>< Xi) (Del <>< Xi)

_//_ : forall {Gam Del}(theta : Shub Gam Del){tau} ->
       Gam !- tau -> Del !- tau
theta // t = {!!}

wkr :  forall {Gam Del sg} -> Ren Gam Del -> Ren (Gam :: sg) (Del :: sg)
wkr r x = {!!}

ren :  forall {Gam Del} -> Ren Gam Del -> Shub Gam Del
ren r Xi = {!!}

wks :  forall {Gam Del sg} -> Sub Gam Del -> Sub (Gam :: sg) (Del :: sg)
wks s x = {!!}

sub :  forall {Gam Del} -> Sub Gam Del -> Shub Gam Del
sub s Xi = {!!}


-- a modern convenience

weak : forall {Gam} Xi -> Ren Gam (Gam <>< Xi)
weak <>        i  = i
weak (_ , Xi)  i  = weak Xi (suc i)

lambda' :  forall {Gam sg tau} ->
           ((forall {Xi} -> Gam :: sg <>< Xi !- sg) -> Gam :: sg !- tau) ->
           Gam !- sg ->> tau
lambda' f = lam (f \ {Xi} -> var (weak Xi zero))

myTest' : Em !- iota ->> iota
myTest' = lambda' \ x -> x

_<>>_ : Context -> List Type -> List Type
Em         <>> ys = ys
(xz :: x)  <>> ys = xz <>> (x , ys)

revLem : forall Del Phi ->
         Em <>< (Del <>> Phi) == Del <>< Phi
revLem Em Phi = refl
revLem (Del :: sig) Phi = revLem Del (sig , Phi)

lem :  forall Del Gam Xi ->
       Del <>> <> == Gam <>> Xi -> Gam <>< Xi == Del
lem Del Em .(Del <>> <>) refl = revLem Del <>
lem Del (Gam :: sig) Xi q = lem Del Gam (sig , Xi) q

lambda :  forall {Gam sg tau} ->
          ((forall {Del Xi}{{_ : Del <>> <> == Gam <>> (sg , Xi)}} -> Del !- sg) ->
            Gam :: sg !- tau) ->
          Gam !- sg ->> tau
lambda {Gam} f =
  lam  (f \ {Del Xi}{{q}} ->
       subst (lem Del Gam (_ , Xi) q) (\ Gam -> Gam !- _) (var (weak Xi zero)))

myTest : Em !- (iota ->> iota) ->> (iota ->> iota)
myTest = lambda \ f -> lambda \ x -> f $ (f $ x)

