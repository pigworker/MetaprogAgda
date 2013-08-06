module Exe2 where

open import Vec

-- STLC representation

data Ty : Set where
  iota   :              Ty
  _->>_  : Ty -> Ty ->  Ty
infixr 5 _->>_

data Cx (X : Set) : Set where
  Em    : Cx X
  _::_  : Cx X -> X -> Cx X
infixl 4 _::_

data _<:_ (tau : Ty) : Cx Ty -> Set where
  zero  : forall {Gam}                    -> tau <: Gam :: tau
  suc   : forall {Gam sg}  -> tau <: Gam  -> tau <: Gam :: sg
infix 3 _<:_

data _!-_ (Gam : Cx Ty) : Ty -> Set where

  var :  forall {tau}
         ->  tau <: Gam
         ----------------
         ->  Gam !- tau

  lam :  forall {sg tau}
         ->  Gam :: sg !- tau
         -----------------------
         ->  Gam !- sg ->> tau

  app :  forall {sg tau}
         ->  Gam !- sg ->> tau  ->  Gam !- sg
         --------------------------------------
         ->  Gam !- tau

infix 3 _!-_

<!_!>T : Ty -> Set
<! iota !>T        = Nat                      -- by way of being nontrivial
<! sg ->> tau !>T  = <! sg !>T -> <! tau !>T

<!_!>C : Cx Ty -> (Ty -> Set) -> Set
<! Em !>C         V  = One
<! Gam :: sg !>C  V  = <! Gam !>C V * V sg

<!_!>V : forall {Gam tau V} -> tau <: Gam -> <! Gam !>C V -> V tau
<! zero !>V   (gam , t)  = t
<! suc i !>V  (gam , s)  = <! i !>V gam

<!_!>t : forall {Gam tau} -> Gam !- tau -> <! Gam !>C <!_!>T -> <! tau !>T
<! var i !>t    gam = <! i !>V gam
<! lam t !>t    gam = \ s -> <! t !>t (gam , s)
<! app f s !>t  gam = <! f !>t gam (<! s !>t gam)

--\section{Substitution with a Friendly Fish}

Ren Sub : Cx Ty -> Cx Ty -> Set
Ren  Gam Del  = forall {tau} -> tau <: Gam -> tau <: Del
Sub  Gam Del  = forall {tau} -> tau <: Gam -> Del !- tau

_<><_ : forall {X} -> Cx X -> List X -> Cx X
xz <>< <>        = xz
xz <>< (x , xs)  = xz :: x <>< xs
infixl 4 _<><_

Shub : Cx Ty -> Cx Ty -> Set
Shub Gam Del = forall Xi -> Sub (Gam <>< Xi) (Del <>< Xi)

_//_ : forall {Gam Del}(theta : Shub Gam Del){tau} -> Gam !- tau -> Del !- tau
theta // var i    = theta <> i
theta // lam t    = lam ((theta o _,_ _) // t)
theta // app f s  = app (theta // f) (theta // s)

wkr :  forall {Gam Del sg} -> Ren Gam Del -> Ren (Gam :: sg) (Del :: sg)
wkr r zero     = zero
wkr r (suc i)  = suc (r i)

ren :  forall {Gam Del} -> Ren Gam Del -> Shub Gam Del
ren r <>         = var o r
ren r (_ , Xi)   = ren (wkr r) Xi

wks :  forall {Gam Del sg} -> Sub Gam Del -> Sub (Gam :: sg) (Del :: sg)
wks s zero     = var zero
wks s (suc i)  = ren suc // s i

sub :  forall {Gam Del} -> Sub Gam Del -> Shub Gam Del
sub s <>         = s
sub s (_ , Xi)   = sub (wks s) Xi


--\section{A Modern Convenience}

weak : forall {Gam} Xi -> Ren Gam (Gam <>< Xi)
weak <>        i  = i
weak (_ , Xi)  i  = weak Xi (suc i)

_<>>_ : forall {X} -> Cx X -> List X -> List X
Em         <>> ys = ys
(xz :: x)  <>> ys = xz <>> (x , ys)

lem :  forall {X}(Del Gam : Cx X) Xi ->
       Del <>> <> == Gam <>> Xi -> Gam <>< Xi == Del
lem Del Gam Xi q  = {!!}

lambda :  forall {Gam sg tau} ->
          ((forall {Del Xi}{{_ : Del <>> <> == Gam <>> (sg , Xi)}} -> Del !- sg) ->
            Gam :: sg !- tau) ->
          Gam !- sg ->> tau
lambda {Gam} f =
  lam  (f \ {Del Xi}{{q}} ->
       subst (lem Del Gam (_ , Xi) q) (\ Gam -> Gam !- _) (var (weak Xi zero)))

myTest : Em !- (iota ->> iota) ->> (iota ->> iota)
myTest = lambda \ f -> lambda \ x -> app f (app f x)


--\section{Hereditary Substitution}

mutual

  data _!=_ (Gam : Cx Ty) : Ty -> Set where
    lam  : forall {sg tau} -> Gam :: sg != tau -> Gam != sg ->> tau
    _$_  : forall {tau} -> tau <: Gam -> Gam !=* tau -> Gam != iota

  data _!=*_ (Gam : Cx Ty) : Ty -> Set where
    <>   : Gam !=* iota
    _,_  : forall {sg tau} -> Gam != sg -> Gam !=* tau -> Gam !=* sg ->> tau

infix 3 _!=_ _!=*_
infix 3 _$_

{-
Define the function |-| which \emph{removes} a designated entry from a context,
then implement the \emph{thinning} operator, being the renaming which maps the
embed the smaller context back into the larger.
-}

_-_ : forall (Gam : Cx Ty){tau}(x : tau <: Gam) -> Cx Ty
Gam - x = {!!}
infixl 4 _-_

_/=_ : forall {Gam sg}(x : sg <: Gam) -> Ren (Gam - x) Gam
x /= y = {!!}

data Veq? {Gam sg}(x : sg <: Gam) : forall {tau} -> tau <: Gam -> Set where
  same  :                                      Veq? x x
  diff  : forall {tau}(y : tau <: Gam - x) ->  Veq? x (x /= y)

--Show that every |y| is discriminable with respect to a given |x|.

veq? : forall {Gam sg tau}(x : sg <: Gam)(y : tau <: Gam) -> Veq? x y
veq? x y = {!!}

--Show how to propagate a renaming through a normal form.
mutual

  renNm : forall {Gam Del tau} -> Ren Gam Del -> Gam != tau -> Del != tau
  renNm r t = {!!}

  renSp : forall {Gam Del tau} -> Ren Gam Del -> Gam !=* tau -> Del !=* tau
  renSp r ss = {!!}

-- Implement hereditary substitution for normal forms and spines,
-- defined mutually with application of a normal form to a spine,
-- performing $\beta$-reduction.

mutual

  <<_:=_>>_ :  forall  {Gam sg tau} -> (x : sg <: Gam) -> Gam - x != sg -> 
                       Gam != tau -> Gam - x != tau
  << x := s >> t = {!!}

  <<_:=_>>*_ :  forall  {Gam sg tau} -> (x : sg <: Gam) -> Gam - x != sg ->
                        Gam !=* tau -> Gam - x !=* tau
  << x := s >>* ts = {!!}

  _$$_ : forall  {Gam tau} ->
                 Gam != tau -> Gam !=* tau -> Gam != iota
  f      $$ ss = {!!}

infix 3 _$$_ 
infix 2 <<_:=_>>_

--Finish the following

normalize : forall {Gam tau} -> Gam !- tau -> Gam != tau
normalize (var x)    = {!!}
normalize (lam t)    = lam (normalize t)
normalize (app f s)  with  normalize f  | normalize s
normalize (app f s)  |     lam t        | s'        = << zero := s' >> t

try1 : Em != ((iota ->> iota) ->> (iota ->> iota)) ->> (iota ->> iota) ->> (iota ->> iota)
try1 = normalize (lambda \ x -> x)

church2 : forall {tau} -> Em !- (tau ->> tau) ->> tau ->> tau
church2 = lambda \ f -> lambda \ x -> app f (app f x)

try2 : Em != (iota ->> iota) ->> (iota ->> iota)
try2 = normalize (app (app church2 church2) church2)


--\section{Normalization by Evaluation}

data Stop (Gam : Cx Ty)(tau : Ty) : Set where
  var : tau <: Gam -> Stop Gam tau
  _$_ : forall {sg} -> Stop Gam (sg ->> tau) -> Gam != sg -> Stop Gam tau

-- Show that |Stop| terms are closed under renaming, and that you can apply
-- them to a spine to get a normal form.

renSt : forall {Gam Del tau} -> Ren Gam Del -> Stop Gam tau -> Stop Del tau
renSt r u = {!!}

stopSp : forall {Gam tau} -> Stop Gam tau -> Gam !=* tau -> Gam != iota
stopSp u ss = {!!}

mutual

  Val : Cx Ty -> Ty -> Set
  Val Gam tau = Go Gam tau + Stop Gam tau

  Go : Cx Ty -> Ty -> Set
  Go Gam iota          = Zero
  Go Gam (sg ->> tau)  = forall {Del} -> Ren Gam Del -> Val Del sg -> Val Del tau

-- Show that values admit renaming. Extend renaming to environments storing values.
-- Construct the identity environment, mapping each variable to itself.

renVal : forall {Gam Del} tau -> Ren Gam Del -> Val Gam tau -> Val Del tau
renVal tau r v = {!!}

renVals : forall The {Gam Del} -> Ren Gam Del -> <! The !>C (Val Gam) -> <! The !>C (Val Del)
renVals The r the = {!!}

idEnv : forall Gam -> <! Gam !>C (Val Gam)
idEnv Gam = {!!}

-- Implement application for values. \nudge{It seems $\F{quote}$ is a
-- reserved symbol in Agda.}In order to apply a stopped function, you will
-- need to be able to extract a normal form for the argument, so you will also need
-- to be able to `|quo|te' values as normal forms.

mutual

  apply : forall {Gam sg tau} -> Val Gam (sg ->> tau) -> Val Gam sg -> Val Gam tau
  apply f s = {!!}

  quo : forall {Gam} tau -> Val Gam tau -> Gam != tau
  quo tau v = {!!}

-- Show that every well typed term can be given a value in any context where its
-- free variables have values.

eval : forall {Gam Del tau} -> Gam !- tau -> <! Gam !>C (Val Del) -> Val Del tau
eval t gam = {!!}

normByEval : forall {Gam tau} -> Gam !- tau -> Gam != tau
normByEval {Gam}{tau} t = quo tau (eval t (idEnv Gam))

{-
\begin{exe}[numbers and primitive recursion]
Consider extending the term language with constructors for numbers
and a primitive recursion operator.
%format prec = "\C{rec}"
\begin{spec}
  zero    : Gam !- iota
  suc     : Gam !- iota -> Gam !- iota
  prec    : forall {tau}  -> Gam !- tau -> Gam !- (iota ->> tau ->> tau)
                          -> Gam !- iota -> Gam !- tau
\end{spec}
How should the normal forms change? How should the values change?
Can you extend the implementation of normalization?
\end{exe}

\begin{exe}[adding adding]
Consider making the further extension with a hardwired addition operator.
%format add = "\C{add}"
\begin{spec}
  suc     : Gam !- iota -> Gam !- iota -> Gam !- iota
\end{spec}
Can you engineer the notion of value and the evaluator so that |normByEval|
identifies
\[\begin{array}{l@@{\;\mathrm{with}\;}r}
|add zero t| & |t| \\
|add s zero| & |s| \\
|add (suc s) t| & |suc (add s t)|\\
|add s (suc t)| & |suc (add s t)|\\
|add (add r s) t| & |add r (add s t)|\\
|add s t| & |add t s|
\end{array}\]
and thus yields a stronger decision procedure for equality of expressions
involving adding? (This is not an easy exercise, especially if you want the
last equation to hold. I must confess I have not worked out the details.)
\end{exe}

-}