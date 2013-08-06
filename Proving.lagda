%if False
\begin{code}
module Proving where

open import Normal public  -- a pro-immigration slogan if ever there was one
\end{code}
%endif

\section{Proving Equations}

The best way to start a fight in a room full of type theorists is to
bring up the topic of \emph{equality}.\nudge{Never trust a type
theorist who has not changed their mind about equality at least once.}
There's a huge design space, not least because we often have \emph{two}
notions of equality to work with, so we need to design both and their
interaction.

%format jeq = "\equiv"

On the one hand, we have \emph{judgmental} equality. Suppose you have
|s : S| and you want to put |s| where a value of type |T| is
expected. Can you? You can if |S jeq T|. Different systems specify
|jeq| differently. Before dependent types arrived, syntactic equality
(perhaps up to $\alpha$-conversion) was often enough.

In dependently typed languages, it is quite convenient if |Vec X (2 +
2)| is the same type as |Vec X 4|, so we often consider types up to
the $\alpha\beta$-conversion of the $\lambda$-calculus further
extended by the defining equations of total functions. If we've been
careful enough to keep the \emph{open-terms} reduction of the language
strongly normalizing, then |jeq| is decidable, by
normalize-and-compare in theory and by more carefully tuned heuristics
in practice.

%format !!!- = "\vdash"
%format == = "\D{\simeq}"
%format refl = "\C{refl}"

Agda takes things a little further by supporting $\eta$-conversion at
some `negative' types---specifically, function types and record
types---where a type-directed and terminating $\eta$-expansion makes
sense. Note that a \emph{syntax}-directed `tit-for-tat' approach,
e.g. testing |f jeq \ x -> t| by testing |x !!!- f x jeq t| or |p jeq
(s , t)| by |fst p jeq s| and |snd p = t|, works fine because two
non-canonical functions and pairs are equal if and only if their
expansions are. But if you want the $eta$-rule for |One|, you need a
cue to notice that |u jeq v| when both inhabit |One| and neither is |<>|.

It is always tempting (hence, dangerous) to try to extract more work
from the computer by making judgmental equality admit more equations
which we consider morally true, but it is clear that any
\emph{decidable} judgmental equality will always
disappont---extensional equality of functions is undecidable, for
example. Correspondingly, the equational theory of \emph{open} terms
(conceived as functions from valuations of their variables) will always
be to some extent beyond the ken of the computer.

The remedy for our inevitable disappointment with judgmental equality
is to define a notion of \emph{evidence} for equality. It is standard
practice to establish decidable certificate-checking for undecidable
problems, and we have a standard mechanism for so doing---checking
types.  Let us have types |s == t| inhabited by proofs that |s| and
|t| are equal.  We should ensure that |t == t| for all |t|, and that
for all |P|, |s == t -> P s -> P t|, in accordance with the philosophy
of Leibniz. On this much, we may agree. But after that, the fight
starts.

The above story is largely by way of an apology for the following
declaration.
%format _==_ = "\us{" == "}"
\nudge{The size of equality types is also moot. Agda would allow us to
put |s == t| in |Set|, however large |s| and |t| may be...}
\begin{spec}
data _==_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x == x
infix 1 _==_
\end{spec}
We may certainly implement Leibniz's rule.
%format subst = "\F{subst}"
\begin{spec}
subst :  forall {k l}{X : Set k}{s t : X} ->
         s == t -> (P : X -> Set l) -> P s -> P t
subst refl P p = p
\end{spec}

The only canonical proof of |s == t| is |refl|, available only if |s
jeq t|, so we have declared that the equality predicate for
\emph{closed} terms is whatever judgmental equality we happen to have
chosen. We have sealed our disappointment in, but we have gained the
abilty to prove useful equations on \emph{open} terms.
Moreover, the restriction to the judgmental equality is fundamental to
the computational behaviour of our |subst| implementation: we take |p : P s|
and we return it unaltered as |p : P t|, so we need to ensure that |P s jeq P t|,
and hence that |s jeq t|. If we want to make |==| larger than |jeq|, we need
a more invasive approach to transporting data between provably equal types.
For now, let us acknowledge the problem and make do.

We may register equality with Agda, via the following pragmas,
\nudge{...but for this pragma, we need |_==_ {l}{X} s t : Set l|}
\begin{verbatim}
{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}
\end{verbatim}
and thus gain access to Agda's support for equational reasoning.

%format "MonoidOK" = "\D{MonoidOK}"
%format absorbL = "\F{absorbL}"
%format absorbR = "\F{absorbR}"
%format assoc = "\F{assoc}"
Now that we have some sort of equality, we can specify laws for our
structures, e.g., for |Monoid|.
\begin{code}
record MonoidOK X {{M : Monoid X}} : Set where
  field
    absorbL  : (x : X) ->      neut & x == x
    absorbR  : (x : X) ->      x & neut == x
    assoc    : (x y z : X) ->  (x & y) & z == x & (y & z)
\end{code}

%format natMonoidOK = "\F{natMonoidOK}"
Let's check that |+Nat| really gives a monoid.
%format assoc+ = "\F{assoc+}"
\begin{code}
natMonoidOK : MonoidOK Nat
natMonoidOK = record
  {  absorbL  = \ _ -> refl
  ;  absorbR  = _+zero
  ;  assoc    = assoc+
  }  where    -- see below
\end{code}
The |absorbL| law follows by computation, but the other two require inductive
proof.
%format +zero = "\F{+zero}"
%format _+zero = "\_\!" +zero
\begin{code}
  _+zero : forall x -> x +Nat zero == x
  zero   +zero                  = refl
  suc n  +zero rewrite n +zero  = refl

  assoc+ : forall x y z -> (x +Nat y) +Nat z  == x +Nat (y +Nat z)
  assoc+ zero     y z                       = refl
  assoc+ (suc x)  y z rewrite assoc+ x y z  = refl
\end{code}
The usual inductive proofs become structurally recursive functions,
pattern matching on the argument in which |+Nat| is strict, so that
computation unfolds. Sadly, an Agda\nudge{differently from the
way in which a Coq script also does not} program, seen as a proof document
does not show you the subgoal structure. However, we can see that
the base case holds computationally and the step case becomes trivial
once we have rewritten the goal by the inductive hypothesis (being the
type of the structurally recursive call).

%format listNMonoidOK = "\F{listNMonoidOK}"
\begin{exe}[|ListN| monoid]
This is a nasty little exercise. By all means warm up by proving that
|List X| is a monoid with respect to concatenation, but I want you to
have a crack at
\begin{spec}
listNMonoidOK : {X : Set} -> MonoidOK (<! ListN !>N X)
listNMonoidOK {X} = ?
\end{spec}
Hint 1: use \emph{curried} helper functions to ensure structural recursion.
The inductive step cases are tricky because the
hypotheses equate number-vector pairs, but the components of those pairs
are scattered in the goal, so |rewrite| will not help. Hint 2: use
|subst| with a predicate of form |vv \ n xs -> ...|, which will allow you
to abstract over separated places with |n| and |xs|.
%if False
\begin{code}
listNMonoidOK : {X : Set} -> MonoidOK (<! ListN !>N X)
listNMonoidOK {X} = record
  {  absorbL  = \ _ -> refl
  ;  absorbR  = vv aR
  ;  assoc    = vv aa
  }  where
  aR : forall n (xs : Vec X n) ->
       (n , xs) & neut {{listNMonoid}} == (n , xs)
  aR .zero    <>        = refl
  aR (suc n)  (x , xs)  =
    subst (aR n xs) (vv \ m ys -> suc (n +Nat 0) , x , xs ++ <> == suc m , x , ys)
      refl
  aa : forall n (xs : Vec X n)(ys zs : <! ListN !>N X) ->
       ((n , xs) & ys) & zs == (n , xs) & (ys & zs)
  aa .zero    <>        _         _         = refl
  aa (suc n)  (x , xs)  (i , ys)  (j , zs)  =
     subst (aa n xs (i , ys) (j , zs))
       (vv \ m ws ->  _==_ {_}{<! ListN !>N X}
         (suc ((n +Nat i) +Nat j) , (x , (xs ++ ys) ++ zs)) (suc m , (x , ws)))
       refl
\end{code}
%endif
\end{exe}

\begin{exe}[a not inconsiderable problem]
Find out what goes wrong when you try to state associativity of vector |++|,
let alone prove it. What does it tell you about our |==| setup?
\end{exe}

A \emph{monoid homomorphism} is a map between their carrier sets which
respects the operations.
%format MonoidHom = "\D{MonoidHom}"
%format respNeut = "\F{resp}" neut
%format resp& = "\F{resp}" &
\begin{code}
record MonoidHom {X}{{MX : Monoid X}}{Y}{{MY : Monoid Y}}(f : X -> Y) : Set where
  field
    respNeut  :                 f neut == neut
    resp&     : forall x x' ->  f (x & x') == f x & f x'
\end{code}
For example, taking the length of a list is, in the |Normal| representation,
trivially a homomorphism.
%format fstHom = "\F{fstHom}"
\begin{code}
fstHom : forall {X} -> MonoidHom {<! ListN !>N X}{Nat} fst
fstHom = record { respNeut = refl; resp& = \ _ _ -> refl }
\end{code}


Moving along to functorial structures, let us explore laws about
the transformation of \emph{functions}. Equations at higher order mean
trouble ahead!

%format EndoFunctorOK = "\D{EndoFunctorOK}"
%format endoFunctorId = "\F{endoFunctorId}"
%format endoFunctorCo = "\F{endoFunctorCo}"
\begin{code}
record EndoFunctorOK F {{FF : EndoFunctor F}} : Set1 where
  field
    endoFunctorId  : forall {X} ->
      map {{FF}}{X} id == id
    endoFunctorCo  : forall {R S T}(f : S -> T)(g : R -> S) ->
      map {{FF}} f o map g == map (f o g)
\end{code}

However, when we try to show,
%format vecEndoFunctorOK = "\F{vecEndoFunctorOK}"
\begin{spec}
vecEndoFunctorOK : forall {n} -> EndoFunctorOK \ X -> Vec X n
vecEndoFunctorOK = record
  {  endoFunctorId  = (HOLE GAP 0)
  ;  endoFunctorCo  = \ f g -> (HOLE GAP 1)
  }
\end{spec}
we see concrete goals (up to some tidying):
\begin{spec}
  ?0  :  vapp (vec id) == id
  ?1  :  vapp (vec f) o vapp (vec g) == vapp (vec (f o g))
\end{spec}

This is a fool's errand. The pattern matching definition of |vapp|
will not allow these equations on functions to hold at the level of
|jeq|. We could make them a little more concrete by doing induction on
|n|, but we will still not force enough computation. Our |==| cannot
be extensional\nudge{Some see this as reason enough to abandon
decidability of |jeq|, thence of typechecking.} for functions because
it has canonical proofs for nothing more than |jeq|, and |jeq| cannot
incorporate extensionality and remain decidable.

We can define \emph{pointwise} equality,
%format =1= = "\F{\doteq}"
%format _=1=_ = "\us{" =1= "}"
\begin{code}
_=1=_ :  forall {l}{S : Set l}{T : S -> Set l}
         (f g : (x : S) -> T x) -> Set l
f =1= g = forall x -> f x == g x
infix 1 _=1=_
\end{code}
which is reflexive but not substitutive.

Now we can at least require:
%format EndoFunctorOKP = "\D{EndoFunctorOKP}"
\begin{code}
record EndoFunctorOKP F {{FF : EndoFunctor F}} : Set1 where
  field
    endoFunctorId  : forall {X} ->
      map {{FF}}{X} id =1= id
    endoFunctorCo  : forall {R S T}(f : S -> T)(g : R -> S) ->
      map {{FF}} f o map g =1= map (f o g)
\end{code}

%format vecEndoFunctorOKP = "\F{vecEndoFunctorOKP}"
%format mapId = "\F{mapId}"
%format mapCo = "\F{mapCo}"
\begin{exe}[|Vec| functor laws]
Show that vectors are functorial.
\begin{spec}
vecEndoFunctorOKP : forall {n} -> EndoFunctorOKP \ X -> Vec X n
vecEndoFunctorOKP = ?
\end{spec}
%if False
\begin{code}
vecEndoFunctorOKP : forall {n} -> EndoFunctorOKP \ X -> Vec X n
vecEndoFunctorOKP = record
  {  endoFunctorId  = mapId
  ;  endoFunctorCo  = mapCo
  }  where
  mapId : forall {n X}(xs : Vec X n) -> vapp (vec id) xs == xs
  mapId <>                          = refl
  mapId (x , xs)  rewrite mapId xs  = refl
  mapCo :  forall {n R S T} (f : S -> T) (g : R -> S) (xs : Vec R n) →
           vapp (vec f) (vapp (vec g) xs) == vapp (vec (f o g)) xs
  mapCo f g <>                              = refl
  mapCo f g (x , xs)  rewrite mapCo f g xs  = refl
\end{code}
%endif
\end{exe}
