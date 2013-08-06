%if False
\begin{code}

module STLC where

open import Vec

\end{code}
%endif

This chapter contains some standard techniques for the representation
of typed syntax and its semantics. The joy of typed syntax is the avoidance
of junk in its interpretation. Everything fits, just so.

\section{Syntax}

Last century, I learned the following recipe for well typed terms of
the simply typed $\lambda$-calculus from Altenkirch and Reus.

First, give a syntax for types. I shall start with a base type
and close under function spaces.

%format Ty = "\D{\star}"
%format iota = "\C{\upiota}"
%format ->> = "\C{\vartriangleright}"
%format _->>_ = "\_\!" ->> "\!\_"
%format Cx = "\D{Cx}"
%format Em = "\C{\mathcal{E}}"
%format var = "\C{var}"
%format lam = "\C{lam}"
%format app = "\C{app}"
%format :: = "\!\raisebox{ -0.09in}[0in][0in]{\red{\textsf{`}}\,}"
%format _::_ = "\us{" :: "}"

\begin{code}
data Ty : Set where
  iota   :              Ty
  _->>_  : Ty -> Ty ->  Ty
infixr 5 _->>_
\end{code}

Next, build contexts as snoc-lists.

\begin{code}
data Cx (X : Set) : Set where
  Em    : Cx X
  _::_  : Cx X -> X -> Cx X
infixl 4 _::_
\end{code}

Now, define typed de Bruijn indices to be context membership evidence.

%format <: = "\D{\in}"
%format _<:_ = "\us{" <: "}"
%format Gam = "\V{\Gamma}"
%format sg = "\V{\sigma}"
%format tau = "\V{\tau}"
\begin{code}
data _<:_ (tau : Ty) : Cx Ty -> Set where
  zero  : forall {Gam}                    -> tau <: Gam :: tau
  suc   : forall {Gam sg}  -> tau <: Gam  -> tau <: Gam :: sg
infix 3 _<:_
\end{code}

That done, we can build well typed terms by writing syntax-directed
rules for the typing judgment.

%format !- = "\D{\vdash}"
%format _!-_ = "\us{" !- "}"
\newcommand{\negs}{\hspace*{ -0.3in}}
\begin{code}
data _!-_ (Gam : Cx Ty) : Ty -> Set where

  var :  forall {tau}
         ->  tau <: Gam
         --  \negs -------------
         ->  Gam !- tau

  lam :  forall {sg tau}
         ->  Gam :: sg !- tau
         --  \negs ------------------
         ->  Gam !- sg ->> tau

  app :  forall {sg tau}
         ->  Gam !- sg ->> tau  ->  Gam !- sg
         --  \negs -------------------------------
         ->  Gam !- tau

infix 3 _!-_
\end{code}


\section{Semantics}

Writing an interpreter for such a calculus is an exercise also from
last century, for which we should thank Augustsson and Carlsson.
Start by defining the semantics of each type.

%format !>T = !> "_{" Ty "}"
%format <!_!>T = <! "\!" _ "\!" !>T
\begin{code}
<!_!>T : Ty -> Set
<! iota !>T        = Nat                      -- by way of being nontrivial
<! sg ->> tau !>T  = <! sg !>T -> <! tau !>T
\end{code}

Next, define \emph{environments} for contexts, with projection.
We can reuse these definitions in the rest of the section if we abstract
over the notion of value.
%format !>C = !> "_{" Cx "}"
%format <!_!>C = <! "\!" _ "\!" !>C
%format !>V = !> "_{" <: "}"
%format <!_!>V = <! "\!" _ "\!" !>V
%format gam = "\V{\gamma}"
\begin{code}
<!_!>C : Cx Ty -> (Ty -> Set) -> Set
<! Em !>C         V  = One
<! Gam :: sg !>C  V  = <! Gam !>C V * V sg

<!_!>V : forall {Gam tau V} -> tau <: Gam -> <! Gam !>C V -> V tau
<! zero !>V   (gam , t)  = t
<! suc i !>V  (gam , s)  = <! i !>V gam
\end{code}

Finally, define the meaning of terms.
%format !>t = !> "_{" !- "}"
%format <!_!>t = <! "\!" _ "\!" !>V
\begin{code}
<!_!>t : forall {Gam tau} -> Gam !- tau -> <! Gam !>C <!_!>T -> <! tau !>T
<! var i !>t    gam = <! i !>V gam
<! lam t !>t    gam = \ s -> <! t !>t (gam , s)
<! app f s !>t  gam = <! f !>t gam (<! s !>t gam)
\end{code}


\section{Substitution with a Friendly Fish}

%format Ren = "\F{Ren}"
%format Sub = "\F{Sub}"
%format Del = "\V{\Delta}"

We may define the types of simultaneous renamings and substitutions
as type-preserving maps from variables:
\begin{code}
Ren Sub : Cx Ty -> Cx Ty -> Set
Ren  Gam Del  = forall {tau} -> tau <: Gam -> tau <: Del
Sub  Gam Del  = forall {tau} -> tau <: Gam -> Del !- tau
\end{code}

%format <>< = "\F{<\!\!>\!\!<}"
%format _<><_ = "\us{" <>< "}"
The trouble with defining the action of substitution for a de Bruijn
representation is the need to shift indices when the context grows.
Here is one way to address that situation.
First, let me define\nudge{|<><| is pronounce `fish',
for historical reasons.} context extension as
concatenation with a cons-list, using the |<><| operator.

\begin{code}
_<><_ : forall {X} -> Cx X -> List X -> Cx X
xz <>< <>        = xz
xz <>< (x , xs)  = xz :: x <>< xs
infixl 4 _<><_
\end{code}

%format Xi = "\V{\Xi}"
%format // = "\F{/\!\!/}"
%format _//_ = "\us{" // "}"
%format theta = "\V{\theta}"
%format Shub = "\F{Shub}"
We may then define the \emph{shiftable} simultaneous substitutions
from |Gam| to |Del|
as type-preserving mappings from the variables in any extension of |Gam| to
terms in the same extension of |Del|.
\begin{code}
Shub : Cx Ty -> Cx Ty -> Set
Shub Gam Del = forall Xi -> Sub (Gam <>< Xi) (Del <>< Xi)
\end{code}

By the computational behaviour of |<><|, a |Shub Gam Del| can be used
as a |Shub (Gam :: sg) (Del :: sg)|, so we can push substitutions under
binders very easily.
\begin{code}
_//_ : forall {Gam Del}(theta : Shub Gam Del){tau} -> Gam !- tau -> Del !- tau
theta // var i    = theta <> i
theta // lam t    = lam ((theta o _,_ _) // t)
theta // app f s  = app (theta // f) (theta // s)
\end{code}

Of course, we shall need to construct some of these joyous shubstitutions.
Let us first show that any simultaneous renaming can be made shiftable by
iterative weakening.
%format wkr = "\F{wkr}"
%format ren = "\F{ren}"
\begin{code}
wkr :  forall {Gam Del sg} -> Ren Gam Del -> Ren (Gam :: sg) (Del :: sg)
wkr r zero     = zero
wkr r (suc i)  = suc (r i)

ren :  forall {Gam Del} -> Ren Gam Del -> Shub Gam Del
ren r <>         = var o r
ren r (_ , Xi)   = ren (wkr r) Xi
\end{code}

%format wks = "\F{wks}"
%format sub = "\F{sub}"
With renaming available, we can play the same game for substitutions.
\begin{code}
wks :  forall {Gam Del sg} -> Sub Gam Del -> Sub (Gam :: sg) (Del :: sg)
wks s zero     = var zero
wks s (suc i)  = ren suc // s i

sub :  forall {Gam Del} -> Sub Gam Del -> Shub Gam Del
sub s <>         = s
sub s (_ , Xi)   = sub (wks s) Xi
\end{code}


\section{A Modern Convenience}

Bob Atkey once remarked that ability to cope with de Bruijn indices
was a good reverse Turing Test, suitable for detecting humaniform
robotic infiltrators. Correspondingly, we might like to write terms
which use real names. I had an idea about how to do that.

We can build the renaming which shifts past any context extension.
%format weak = "\F{weak}"
\begin{code}
weak : forall {Gam} Xi -> Ren Gam (Gam <>< Xi)
weak <>        i  = i
weak (_ , Xi)  i  = weak Xi (suc i)
\end{code}

Then, we can observe that to build the body of a binder, it is enough
to supply a function which will deliver the term representing the
variable in any suitably extended context. The context extension is given
implicitly, to be inferred from the usage site, and then the correct
weakening is applied to the bound variable.
%format lambda' = "\F{lambda}"
\begin{code}
lambda' :  forall {Gam sg tau} ->
           ((forall {Xi} -> Gam :: sg <>< Xi !- sg) -> Gam :: sg !- tau) ->
           Gam !- sg ->> tau
lambda' f = lam (f \ {Xi} -> var (weak Xi zero))
\end{code}

%format myTest' = "\F{myTest}"
But sadly, the followinf does not typecheck
\begin{spec}
myTest' : Em !- iota ->> iota
myTest' = lambda' \ x -> x
\end{spec}
because the following constraint is not solved:
\[
|(Em :: iota <>< _Xi_232 x) = (Em :: iota) : Cx Ty|
\]
That is, constructor-based unification is insufficient to solve for the prefix
of a context, given a common suffix.

By contrast, solving for a suffix is easy when the prefix is just a
value: it requires only the stripping off of matching constructors.
So, we can cajole Agda into solving the problem by working with its
reversal, via the `chips' operator:
%format <>> = "\F{<\!\!>\!\!>}"
%format _<>>_ = "\us{" <>> "}"
\begin{code}
_<>>_ : forall {X} -> Cx X -> List X -> List X
Em         <>> ys = ys
(xz :: x)  <>> ys = xz <>> (x , ys)
\end{code}

%if False
\begin{code}
_+a_ : Nat -> Nat -> Nat
zero +a y = y
suc x +a y = x +a suc y

sucI : (a b : Nat) -> (_==_ {lzero}{Nat} (suc a) (suc b)) -> a == b
sucI .b b refl = refl

grr : (x y : Nat) -> suc x +Nat y == x +Nat suc y
grr zero y = refl
grr (suc x) y rewrite grr x y = refl

noc' : (x y : Nat) -> suc (x +Nat y) == y -> {A : Set} -> A
noc' x zero ()
noc' x (suc y) q = noc' x y
     (suc (x +Nat y) =!! grr x y >> x +Nat suc y =!! sucI _ _ q >> y <QED>)

noc : (x k y : Nat) -> x +a (suc k +Nat y) == y -> {A : Set} -> A
noc zero k y q = noc' k y q
noc (suc x) k y q = noc x (suc k) y q

len : forall {X} -> Cx X -> Nat
len Em = zero
len (xz :: x) = suc (len xz)

lenlem : forall {X}(xz : Cx X)(xs : List X) ->
  length (xz <>> xs) == len xz +a length xs
lenlem Em xs = refl
lenlem (xz :: x) xs = lenlem xz (x , xs)

lem0 : forall {X}(xz yz : Cx X)(xs ys : List X) ->
       length xs == length ys ->
       xz <>> xs == yz <>> ys -> (xz == yz) * (xs == ys)
lem0 Em Em xs ys q q' = refl , q'
lem0 Em (yz :: x) .(yz <>> (x , ys)) ys q refl
 rewrite lenlem yz (x , ys) = noc (len yz) zero (length ys) q
lem0 (xz :: x) Em xs .(xz <>> (x , xs)) q refl
 rewrite lenlem xz (x , xs) = noc (len xz) zero (length xs)
   (_ << q !!= _ <QED>)
lem0 (xz :: x) (yz :: y) xs ys q q'
  with lem0 xz yz (x , xs) (y , ys) (cong suc q) q' 
lem0 (.yz :: .y) (yz :: y) .ys ys q q' | refl , refl = refl , refl

lem : forall {X}(Del Gam : Cx X) Xi -> Del <>> <> == Gam <>> Xi ->
      Gam <>< Xi == Del
lem Del Gam <>       q  =
   Gam << fst (lem0 Del Gam <> <> refl q) !!= Del <QED>
lem Del Gam (x , Xi) q  = lem Del (Gam :: x) Xi q
\end{code}
%endif

Of course, one must prove that solving the reverse problem is good for
solving the original.

%format lem = "\F{lem}"
\begin{exe}[reversing lemma]
Show\nudge{I have discovered a truly appalling proof of this lemma. Fortunately, this margin is too narrow to contain it. See if you can do better.}
\begin{spec}
lem :  forall {X}(Del Gam : Cx X) Xi ->
       Del <>> <> == Gam <>> Xi -> Gam <>< Xi == Del
lem Del Gam Xi q  = ?
\end{spec}
\end{exe}

Now we can frame the constraint solve as an instance argument supplying a
proof of the relevant equation on cons-lists: Agda will try to use |refl|
to solve the instance argument, triggering the tractable version of the
unification problem.
%format lambda = lambda'
%format myTest = myTest'
\begin{code}
lambda :  forall {Gam sg tau} ->
          ((forall {Del Xi}{{_ : Del <>> <> == Gam <>> (sg , Xi)}} -> Del !- sg) ->
            Gam :: sg !- tau) ->
          Gam !- sg ->> tau
lambda {Gam} f =
  lam  (f \ {Del Xi}{{q}} ->
       subst (lem Del Gam (_ , Xi) q) (\ Gam -> Gam !- _) (var (weak Xi zero)))

myTest : Em !- (iota ->> iota) ->> (iota ->> iota)
myTest = lambda \ f -> lambda \ x -> app f (app f x)
\end{code}


\section{Hereditary Substitution}

This section is a structured series of exercises, delivering a
$\beta\eta$-long normalization algorithm for our $\lambda$-calculus
by the method of \emph{hereditary substitution}.

The target type for the algorithm is the following right-nested spine
representation of $\beta$-normal $\eta$-long forms.%format != = "\D{\vDash}"
%format _!=_ = "\us{" != "}"
%format !=* = "\D{\vDash^*}"
%format _!=*_ = "\us{" !=* "}"
%format $ = "\C{\scriptstyle \$}"
%format _$_ = "\us{" $ "}"
\begin{code}
mutual

  data _!=_ (Gam : Cx Ty) : Ty -> Set where
    lam  : forall {sg tau} -> Gam :: sg != tau -> Gam != sg ->> tau
    _$_  : forall {tau} -> tau <: Gam -> Gam !=* tau -> Gam != iota

  data _!=*_ (Gam : Cx Ty) : Ty -> Set where
    <>   : Gam !=* iota
    _,_  : forall {sg tau} -> Gam != sg -> Gam !=* tau -> Gam !=* sg ->> tau

infix 3 _!=_ _!=*_
infix 3 _$_
\end{code}
That is |Gam != tau| is the type of normal forms \emph{in} |tau|, and
|Gam !=* tau| is the type of spines \emph{for} a |tau|, delivering |iota|.

The operation of hereditary substitution replaces \emph{one} variable with a
normal form and immediately performs all the resulting computation (i.e., more
substitution), returning a normal form. You will need some equipment for talking
about individual variables.

%format - = "\F{ -}"
%format _-_ = "\us{" - "}"
%format /= = "\F{\neq}"
%format _/=_ = "\us{" /= "}"
\begin{exe}[thinning]
Define the function |-| which \emph{removes} a designated entry from a context,
then implement the \emph{thinning} operator, being the renaming which maps the
embed the smaller context back into the larger.
\begin{spec}
_-_ : forall (Gam : Cx Ty){tau}(x : tau <: Gam) -> Cx Ty
Gam - x = ?
infixl 4 _-_

_/=_ : forall {Gam sg}(x : sg <: Gam) -> Ren (Gam - x) Gam
x /= y = ?
\end{spec}
%if False
\begin{code}
_-_ : forall (Gam : Cx Ty){tau}(x : tau <: Gam) -> Cx Ty
Gam :: _  - zero  = Gam
Gam :: sg - suc x = Gam - x :: sg
infixl 4 _-_

_/=_ : forall {Gam sg}(x : sg <: Gam) -> Ren (Gam - x) Gam
zero   /= y      = suc y
suc x  /= zero   = zero
suc x  /= suc y  = suc (x /= y)
\end{code}
%endif
\end{exe}

%format << = "\F{\langle}"
%format := = "\F{\mapsto}"
%format <<_:=_>>_ = << _ := _ >> _
This much will let us frame the problem. We have a candidate value for |x|
which does not depend on |x|, so we should be able to eliminate |x| from any
term by substituting out. If we try, we find this situation:
\begin{spec}
  <<_:=_>>_ :  forall  {Gam sg tau} -> (x : sg <: Gam) -> Gam - x != sg -> 
                       Gam != tau -> Gam - x != tau
  << x := s >> lam t   = lam (<< suc x := ? >> t)
  << x := s >> y $ ts  = ?
infix 2 <<_:=_>>_
\end{spec}
Let us now address the challenges we face.

%format Veq? = "\D{Veq?}"
%format veq? = "\F{veq?}"
%format same = "\C{same}"
%format diff = "\C{diff}"
In the application case, we shall need to test whether or not |y|
is the |x| for which we
must substitute, so we need some sort of equality test. A \emph{Boolean} equality
test does not generate enough useful information---if |y| is |x|, we need to know
that |ts| is a suitable spine for |s|; if |y| is not |x|, we need to know its
representation in |Gam - x|.
Hence, let us rather prove that any variable is either the one we are looking for or
another. We may express this discriminability property as a predicate on variables.
\begin{code}
data Veq? {Gam sg}(x : sg <: Gam) : forall {tau} -> tau <: Gam -> Set where
  same  :                                      Veq? x x
  diff  : forall {tau}(y : tau <: Gam - x) ->  Veq? x (x /= y)
\end{code}

\begin{exe}[variable equality testing]
Show that every |y| is discriminable with respect to a given |x|.
\begin{spec}
veq? : forall {Gam sg tau}(x : sg <: Gam)(y : tau <: Gam) -> Veq? x y
veq? x y = ?
\end{spec}
Hint: it will help to use |with| in the recursive case.
%if False
\begin{code}
veq? : forall {Gam sg tau}(x : sg <: Gam)(y : tau <: Gam) -> Veq? x y
veq? zero     zero             = same
veq? zero     (suc y)          = diff y
veq? (suc x)  zero             = diff zero
veq? (suc x)  (suc y)          with  veq? x y 
veq? (suc x)  (suc .x)         |     same        = same
veq? (suc x)  (suc .(x /= y))  |     diff y      = diff (suc y)
\end{code}
%endif
\end{exe}

Meanwhile, in the |lam| case, we may easily shift |x| to account for the
new variable in |t|, but we shall also need to shift |s|.
%format renNm = "\F{renNm}"
%format renSp = "\F{renSp}"
\begin{exe}[closure under renaming]
Show how to propagate a renaming through a normal form.
\begin{spec}
mutual

  renNm : forall {Gam Del tau} -> Ren Gam Del -> Gam != tau -> Del != tau
  renNm r t = ?

  renSp : forall {Gam Del tau} -> Ren Gam Del -> Gam !=* tau -> Del !=* tau
  renSp r ss = ?
\end{spec}
%if False
\begin{code}
mutual
  renNm : forall {Gam Del tau} -> Ren Gam Del -> Gam != tau -> Del != tau
  renNm r (lam t)   = lam (renNm (wkr r) t)
  renNm r (x $ ss)  = r x $ renSp r ss

  renSp : forall {Gam Del tau} -> Ren Gam Del -> Gam !=* tau -> Del !=* tau
  renSp r <> = <>
  renSp r (s , ss) = renNm r s , renSp r ss
\end{code}
%endif
\end{exe}

Now we have everything we need to implement hereditary substitution.

\begin{exe}[hereditary substitution]
Implement hereditary substitution for normal forms and spines, defined mutually with
application of a normal form to a spine, performing $\beta$-reduction.
%format >>* = "\F\rangle^\ast"
%format <<_:=_>>*_ = << _ := _ >>* _
%format $$ = $ "\!" $
%format _$$_ = "\us{" $$ "}"
\begin{spec}
mutual

  <<_:=_>>_ :  forall  {Gam sg tau} -> (x : sg <: Gam) -> Gam - x != sg -> 
                       Gam != tau -> Gam - x != tau
  << x := s >> t = ?

  <<_:=_>>*_ :  forall  {Gam sg tau} -> (x : sg <: Gam) -> Gam - x != sg ->
                        Gam !=* tau -> Gam - x !=* tau
  << x := s >>* ts = ?

  _$$_ : forall  {Gam tau} ->
                 Gam != tau -> Gam !=* tau -> Gam != iota
  f      $$ ss = ?

infix 3 _$$_ 
infix 2 <<_:=_>>_
\end{spec}
Do you think these functions are mutually structurally recursive?
%if False
\begin{code}
mutual
  <<_:=_>>_ :  forall  {Gam sg tau} -> (x : sg <: Gam) -> Gam - x != sg -> 
                       Gam != tau -> Gam - x != tau
  << x := s >> lam t           = lam (<< suc x := renNm (_/=_ zero) s >> t)
  << x := s >> y $ ts          with veq? x y 
  << x := s >> .x        $ ts  | same         = s $$ (<< x := s >>* ts)
  << x := s >> .(x /= y) $ ts  | diff y       = y $ (<< x := s >>* ts)

  <<_:=_>>*_ :  forall  {Gam sg tau} -> (x : sg <: Gam) -> Gam - x != sg ->
                        Gam !=* tau -> Gam - x !=* tau
  << x := s >>* <>        = <>
  << x := s >>* (t , ts)  = (<< x := s >> t) , (<< x := s >>* ts)

  _$$_ : forall  {Gam tau} ->
                 Gam != tau -> Gam !=* tau -> Gam != iota
  f      $$ <>      = f
  lam t  $$ s , ss  = (<< zero := s >> t) $$ ss
infix 3 _$$_ 
infix 2 <<_:=_>>_
\end{code}
%endif
\end{exe}

With hereditary substitution, it should be a breeze to implement
normalization, but there is one little tricky part remaining.

%format normalize = "\F{normalize}"
\begin{exe}[$\eta$-expansion for |normalize|]
If we start implementing |normalize|, it is easy to get this far:
\begin{spec}
normalize : forall {Gam tau} -> Gam !- tau -> Gam != tau
normalize (var x)    = ?
normalize (lam t)    = lam (normalize t)
normalize (app f s)  with  normalize f  | normalize s
normalize (app f s)  |     lam t        | s'        = << zero := s' >> t
\end{spec}
We can easily push under |lam| and implement |app| by hereditary substitution.
However, if we encounter a variable, |x|, we must deliver it in $\eta$-long form.
You will need to figure out how to expand |x| in a type-directed manner, which is
not a trivial thing to do. Hint: if you need to represent the prefix of a spine,
it suffices to consider functions from suffices.
%if False
\begin{code}
eta : forall  {Gam sg}(x : sg <: Gam) tau ->
              (forall {Del} -> Ren Gam Del -> Del !=* tau -> Del !=* sg) ->
              Gam != tau
eta x iota          f = x $ f id <>
eta x (sg ->> tau)  f
  = lam (  eta (suc x) tau \ rho ss ->
           f (rho o suc) ((eta (rho zero) sg (\ _ -> id)) , ss))

normalize : forall {Gam tau} -> Gam !- tau -> Gam != tau
normalize (var x)    = eta x _ \ _ -> id
normalize (lam t)    = lam (normalize t)
normalize (app f s)  with  normalize f  | normalize s
normalize (app f s)  |     lam t        | s'        = << zero := s' >> t
\end{code}
%endif
\end{exe}

Here are a couple of test examples for you to try. You may need to translate them
into de Bruijn terms manually if you have not yet proven the `reversing lemma'.
%format try1 = "\F{try}_{\F{1}}"
%format try2 = "\F{try}_{\F{2}}"
%format church2 = "\F{church}_{\F{2}}"
\begin{code}
try1 : Em != ((iota ->> iota) ->> (iota ->> iota)) ->> (iota ->> iota) ->> (iota ->> iota)
try1 = normalize (lambda \ x -> x)

church2 : forall {tau} -> Em !- (tau ->> tau) ->> tau ->> tau
church2 = lambda \ f -> lambda \ x -> app f (app f x)

try2 : Em != (iota ->> iota) ->> (iota ->> iota)
try2 = normalize (app (app church2 church2) church2)
\end{code}


\section{Normalization by Evaluation}

Let's cook normalization a different way, extracting more leverage
from Agda's computation machinery. the idea is to model values as
either `going' (capable of computation if applied) or `stopping'
(incapable of computation, but not $\eta$-long). The latter terms
look like left-nested applications of a variable.

%format Stop = "\D{Stop}"
\begin{code}
data Stop (Gam : Cx Ty)(tau : Ty) : Set where
  var : tau <: Gam -> Stop Gam tau
  _$_ : forall {sg} -> Stop Gam (sg ->> tau) -> Gam != sg -> Stop Gam tau
\end{code}

\begin{exe}[|Stop| equipment]
Show that |Stop| terms are closed under renaming, and that you can apply
them to a spine to get a normal form.
%format renSt = "\F{renSt}"
%format stopSp = "\F{stopSp}"
\begin{spec}
renSt : forall {Gam Del tau} -> Ren Gam Del -> Stop Gam tau -> Stop Del tau
renSt r u = ?

stopSp : forall {Gam tau} -> Stop Gam tau -> Gam !=* tau -> Gam != iota
stopSp u ss = ?
\end{spec}
%if False
\begin{code}
renSt : forall {Gam Del tau} -> Ren Gam Del -> Stop Gam tau -> Stop Del tau
renSt r (var x) = var (r x)
renSt r (u $ s) = renSt r u $ renNm r s

stopSp : forall {Gam tau} -> Stop Gam tau -> Gam !=* tau -> Gam != iota
stopSp (var x) ss = x $ ss
stopSp (u $ s) ss = stopSp u (s , ss)
\end{code}
%endif
\end{exe}

%format Go = "\F{Go}"
%format Val = "\F{Val}"
%format Zero = "\D{Zero}"
Let us now give a contextualized semantics to each type. Values either |Go| or
|Stop|. Ground values cannot go: |Zero| is a datatype with no constructors.
Functional values have a Kripke semantics. Wherever their
context is meaningful, they take values to values.
\begin{code}
mutual

  Val : Cx Ty -> Ty -> Set
  Val Gam tau = Go Gam tau + Stop Gam tau

  Go : Cx Ty -> Ty -> Set
  Go Gam iota          = Zero
  Go Gam (sg ->> tau)  = forall {Del} -> Ren Gam Del -> Val Del sg -> Val Del tau
\end{code}


\begin{exe}[renaming values and environments]
%format renVal = "\F{renVal}"
%format renVals = "\F{renVals}"
%format The = "\V{\Theta}"
%format the = "\V{\theta}"
%format idEnv = "\F{idEnv}"
Show that values admit renaming. Extend renaming to environments storing values.
Construct the identity environment, mapping each variable to itself.
\begin{spec}
renVal : forall {Gam Del} tau -> Ren Gam Del -> Val Gam tau -> Val Del tau
renVal tau r v = ?

renVals : forall The {Gam Del} -> Ren Gam Del -> <! The !>C (Val Gam) -> <! The !>C (Val Del)
renVals The r the = ?

idEnv : forall Gam -> <! Gam !>C (Val Gam)
idEnv Gam = ?
\end{spec}
%if False
\begin{code}
renVal : forall {Gam Del} tau -> Ren Gam Del -> Val Gam tau -> Val Del tau
renVal tau r (ff , u) = ff , renSt r u
renVal iota r (tt , ())
renVal (sg ->> tau) r (tt , f) = tt , (\ r' s -> f (r' o r) s)

renVals : forall The {Gam Del} -> Ren Gam Del -> <! The !>C (Val Gam) -> <! The !>C (Val Del)
renVals Em r <> = <>
renVals (The :: sg) r (the , s) = renVals The r the , renVal sg r s

idEnv : forall Gam -> <! Gam !>C (Val Gam)
idEnv Em = <>
idEnv (Gam :: sg) = renVals _ suc (idEnv Gam) , (ff , var zero)
\end{code}
%endif
\end{exe}

\begin{exe}[application and quotation]
%format apply = "\F{apply}"
%format quo = "\F{quo}"
Implement application for values. \nudge{It seems $\F{quote}$ is a
reserved symbol in Agda.}In order to apply a stopped function, you will
need to be able to extract a normal form for the argument, so you will also need
to be able to `|quo|te' values as normal forms.
\begin{spec}
mutual

  apply : forall {Gam sg tau} -> Val Gam (sg ->> tau) -> Val Gam sg -> Val Gam tau
  apply f s = ?

  quo : forall {Gam} tau -> Val Gam tau -> Gam != tau
  quo tau v = ?
\end{spec}

%if False
\begin{code}
mutual

  apply : forall {Gam sg tau} -> Val Gam (sg ->> tau) -> Val Gam sg -> Val Gam tau
  apply (tt , f) s = f id s
  apply (ff , u) s = ff , (u $ quo _ s)

  quo : forall {Gam} tau -> Val Gam tau -> Gam != tau
  quo iota (tt , ())
  quo iota (ff , u) = stopSp u <>
  quo (sg ->> tau) v = lam (quo tau (apply (renVal _ suc v) (ff , var zero)))
\end{code}
%endif
\end{exe}

For the last step, we need to compute values from terms.

\begin{exe}[evaluation]
%format eval = "\F{eval}"
Show that every well typed term can be given a value in any context where its
free variables have values.
\begin{spec}
eval : forall {Gam Del tau} -> Gam !- tau -> <! Gam !>C (Val Del) -> Val Del tau
eval t gam = ?
\end{spec}
%if False
\begin{code}
eval : forall {Gam Del tau} -> Gam !- tau -> <! Gam !>C (Val Del) -> Val Del tau
eval (var x) gam = <! x !>V gam
eval (lam t) gam = tt , \ r s -> eval t (renVals _ r gam , s)
eval (app f s) gam = apply (eval f gam) (eval s gam)
\end{code}
%endif
\end{exe}

With all the pieces in place, we get
%format normByEval = "\F{normByEval}"
\begin{code}
normByEval : forall {Gam tau} -> Gam !- tau -> Gam != tau
normByEval {Gam}{tau} t = quo tau (eval t (idEnv Gam))
\end{code}

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

%if False
\section{Normalization by Evaluation with Levels}

mutual

  data Nm : Ty -> Set where
    lam  : forall {sg tau} -> Nm tau -> Nm (sg ->> tau)
    ne   : forall {tau} -> Ne tau -> Nm tau

  data Ne (tau : Ty) : Set where
    var  : Nat -> Ne tau
    app  : forall {sg} -> Ne (sg ->> tau) -> (Nat -> Nm sg) -> Ne tau

mutual

  Val : Ty -> Set
  Val tau = Go tau + Ne tau

  Go : Ty -> Set
  Go iota          = Zero
  Go (sg ->> tau)  = Val sg -> Val tau

stop : forall tau -> Val tau -> Nat -> Nm tau
stop tau           (ff , u)   n  = ne u
stop iota          (tt , ())  n
stop (sg ->> tau)  (tt , f)   n  = lam (stop tau (f (ff , var n)) (suc n))

apply : forall {sg tau} -> Val (sg ->> tau) -> Val sg -> Val tau
apply (tt , f) s = f s
apply (ff , u) s = ff , app u (stop _ s)

eval : forall {Gam tau} -> Gam !- tau -> <! Gam !>C Val -> Val tau
eval (var x) gam = <! x !>V gam
eval (lam t) gam = tt , \ s -> eval t (gam , s)
eval (app f s) gam = apply (eval f gam) (eval s gam)

data LGood (x : Nat)(tau : Ty) : Nat -> Cx Ty -> Set where
  zero  : forall {Gam} -> LGood x tau (suc x) (Gam :: tau)
  suc   : forall {n Gam sg} ->
            LGood x tau n Gam -> LGood x tau (suc n) (Gam :: sg)

linx : forall {n Gam x tau} -> LGood x tau n Gam -> tau <: Gam
linx zero = zero
linx (suc g) = suc (linx g)

mutual
  NmGood : forall (n : Nat)(Del : Cx Ty){tau} -> Nm tau -> Set
  NmGood n Del (lam {sg = sg} t)  = NmGood (suc n) (Del :: sg) t
  NmGood n Del (ne u)             = NeGood n Del u

  NeGood : forall (n : Nat)(Del : Cx Ty){tau} -> Ne tau -> Set
  NeGood n Del {tau} (var x) = LGood x tau n Del
  NeGood n Del (app u s)
    =  NeGood n Del u
    *  (forall Xi -> let n' = length Xi +Nat n in NmGood n' (Del <>< Xi) (s n'))

ValGood : forall (n : Nat)(Del : Cx Ty) tau -> Val tau -> Set
ValGood n Del tau (ff , u) = NeGood n Del u
ValGood n Del iota (tt , ())
ValGood n Del (sg ->> tau) (tt , f)
  = forall Xi -> let n' = length Xi +Nat n in
     (v : Val sg) -> ValGood n' (Del <>< Xi) sg v ->
                     ValGood n' (Del <>< Xi) tau (f v)

EnvGood : forall (n : Nat)(Del Gam : Cx Ty) -> <! Gam !>C Val -> Set
EnvGood n Del Em <> = One
EnvGood n Del (Gam :: sg) (gam , s) = EnvGood n Del Gam gam * ValGood n Del sg s

projLem : forall  (n : Nat)(Del Gam : Cx Ty)(gam : <! Gam !>C Val)
                  {tau}(x : tau <: Gam) ->
                  EnvGood n Del Gam gam -> ValGood n Del tau (<! x !>V gam)
projLem n Del ._ _ zero (good , g) = g
projLem n Del (Gam :: sg) (gam , _) (suc x) (good , g)
  = projLem n Del Gam gam x good

stopLem :  forall n Del tau v -> ValGood n Del tau v -> 
           forall Xi ->  let  n' = length Xi +Nat n
                         in   NmGood n' (Del <>< Xi) (stop tau v n')
stopLem n Del tau (ff , u)  v' Xi = {!!}
stopLem n Del iota (tt , ()) v' Xi
stopLem n Del (sg ->> tau) (tt , f) v' Xi =
  {!stopLem (suc n) (Del :: sg) tau (f (ff , var n)) !}

applyLem : forall  n Del {sg tau} ->
           (f : Val (sg ->> tau))(s : Val sg) ->
           ValGood n Del (sg ->> tau) f -> ValGood n Del sg s ->
           ValGood n Del tau (apply f s)
applyLem n Del (ff , u) s f' s' = f' , stopLem n Del _ s s'
applyLem n Del (tt , f) s f' s' = f' <> s s'

evalThm : forall  (n : Nat)(Del Gam : Cx Ty)(gam : <! Gam !>C Val)
                  {tau}(t : Gam !- tau) ->
                  EnvGood n Del Gam gam -> ValGood n Del tau (eval t gam)
evalThm n Del Gam gam (var x) good = projLem n Del Gam gam x good
evalThm n Del Gam gam (lam t) good = {!!}
evalThm n Del Gam gam (app f s) good
  = applyLem n Del (eval f gam) (eval s gam)
     (evalThm n Del Gam gam f good) (evalThm n Del Gam gam s good)

%endif