%if False
\begin{code}
module Normal where

open import Vec public
\end{code}
%endif

\section{Normal Functors}

A \emph{normal} functor is given, up to isomorphism, by a set of \emph{shapes}
and a function which assigns to each shape a \emph{size}. It is interpreted
as the \emph{dependent pair} of a shape, |s|, and a vector of elements whose
length is the size of |s|.

%format Normal = "\D{Normal}"
%format Shape = "\F{Shape}"
%format size = "\F{size}"
%format / = "\C{/}"
%format _/_ = "\_\!" / "\!\_"
%format <! = "\F{\llbracket}"
%format !> = "\F{\rrbracket}"
%format !>N = !> "_{\F{N}}"
%format <!_!>N = <! "\!" _ "\!" !>N
\begin{code}
record Normal : Set1 where
  constructor _/_
  field
    Shape  : Set
    size   : Shape -> Nat
  <!_!>N : Set -> Set
  <!_!>N X = Sg Shape \ s -> Vec X (size s)
open Normal public
infixr 0 _/_
\end{code}

%format VecN = "\F{VecN}"
%format ListN = "\F{ListN}"

Let us have two examples.
Vectors are the normal functors with a unique shape. Lists are the normal functors
whose shape is their size.
\begin{code}
VecN : Nat -> Normal
VecN n = One / pure n

ListN : Normal
ListN = Nat / id
\end{code}

But let us not get ahead of ourselves. We can build a kit for normal
functors corresponding to the type constructors that we often define,
then build up composite structures.
For example, let us have that constants and the identity are |Normal|.
%format KN = "\F{K}_{\!\F{N}}"
%format IN = "\F{I}\F{K}_{\!\F{N}}"
\begin{code}
KN : Set -> Normal
KN A = A / \ _ -> 0

IN : Normal
IN = VecN 1
\end{code}

%format +N = + "_{\!\F{N}}"
%format _+N_ = "\us{" +N "}"
%format *N = * "_{\!\F{N}}"
%format _*N_ = "\us{" *N "}"
Let us construct sums and products of normal functors.
\begin{code}
_+N_ : Normal -> Normal -> Normal
(ShF / szF) +N (ShG / szG) = (ShF + ShG) / vv szF <?> szG

_*N_ : Normal -> Normal -> Normal
(ShF / szF) *N (ShG / szG) = (ShF * ShG) / vv \ f g -> szF f +Nat szG g
\end{code}

Of course, it is one thing to construct these binary operators on |Normal|,
but quite another to show they are worthy of their names.

%format nInj = "\F{nInj}"
\begin{code}
nInj : forall {X}(F G : Normal) -> <! F !>N X + <! G !>N X -> <! F +N G !>N X
nInj F G (tt , ShF , xs) = (tt , ShF) , xs
nInj F G (ff , ShG , xs) = (ff , ShG) , xs
\end{code}

Now, we could implement the other direction of the isomorphism, but an
alternative is to define the \emph{inverse image}.

%format ^-1 = "{}^{\F{ -1}}"
%format from = "\C{from}"
\begin{code}
data _^-1_ {S T : Set}(f : S -> T) : T -> Set where
  from : (s : S) -> f ^-1 f s
\end{code}

%format nCase = "\F{nCase}"
Let us now show that |nInj| is surjective.
\begin{code}
nCase : forall {X} F G (s : <! F +N G !>N X) -> nInj F G ^-1 s
nCase F G ((tt , ShF) , xs) = from (tt , ShF , xs)
nCase F G ((ff , ShG) , xs) = from (ff , ShG , xs)
\end{code}
That is, we have written more or less the other direction of the iso,
but we have acquired some of the correctness proof for the cost of
asking. We shall check that |nInj| is injective shortly, once we have
suitable equipment to say so.

The inverse of `nInj` can be computed by |nCase| thus:
%format nOut = "\F{nOut}"
\begin{code}
nOut : forall {X}(F G : Normal) -> <! F +N G !>N X -> <! F !>N X + <! G !>N X
nOut F G xs' with nCase F G xs'
nOut F G .(nInj F G xs) | from xs = xs
\end{code}
The |with| notation allows us to compute some useful information and add
it to the collection of things available for inspection in pattern matching.
By matching the result of |nCase F G xs'| as |from xs|, we discover that
\emph{ipso facto}, |xs'| is |nInj xs|. It is in the nature of dependent
types that inspecting one piece of data can refine our knowledge of the whole
programming problem, hence McKinna and I designed |with| as a syntax for
bringing new information to the problem. The usual Burstallian
`case expression' focuses on one scrutinee and shows us its refinements,
but hides from us the refinement of the rest of the problem: in simply
typed programming there is no such refinement, but here there is. Agda
prefixes with a dot those parts of patterns, not necessarily linear
constructor forms, which need not be checked dynamically because the
corresponding value must be as indicated in any well typed usage.

\begin{exe}[normal pairing]
Implement the constructor for normal functor pairs. It may help to
define vector concatenation.
%format nPair = "\F{nPair}"
%format ++ = "\F{+\!\!+}"
%format _++_ = "\us{" ++ "}"
\begin{spec}
_++_ : forall {m n X} -> Vec X m -> Vec X n -> Vec X (m +Nat n)
xs ++ ys = ?

nPair : forall {X}(F G : Normal) -> <! F !>N X * <! G !>N X -> <! F *N G !>N X
nPair F G fxgx = ?
\end{spec}
Show that your constructor is surjective.
%if False
\begin{code}
_++_ : forall {m n X} -> Vec X m -> Vec X n -> Vec X (m +Nat n)
<> ++ ys = ys
(x , xs) ++ ys = x , (xs ++ ys)

nPair : forall {X}(F G : Normal) -> <! F !>N X * <! G !>N X -> <! F *N G !>N X
nPair F G ((ShF , xs) , (ShG , ys)) = (ShF , ShG) , xs ++ ys

split : forall m n {X}(xs : Vec X (m +Nat n)) -> (vv (_++_ {m}{n}{X})) ^-1 xs
split zero n xs = from (<> , xs)
split (suc m) n (x , xs) with split m n xs
split (suc m) n (x , .(ys ++ zs)) | from (ys , zs) = from ((x , ys) , zs)

nSplit : forall {X}(F G : Normal)(fgx : <! F *N G !>N X) -> nPair F G ^-1 fgx
nSplit F G ((f , g) , xs) with split (size F f) (size G g) xs
nSplit F G ((f , g) , .(ys ++ zs)) | from (ys , zs) = from ((f , ys) , (g , zs))
\end{code}
%endif
\end{exe}

\begin{exe}[|ListN| monoid]
While you are in this general area, construct (from readily available components)
the usual monoid structure for our normal presentation of lists.
\begin{spec}
listNMonoid : {X : Set} -> Monoid (<! ListN !>N X)
listNMonoid = ?
\end{spec}
%format listNMonoid = "\F{listNMonoid}"
%if False
\begin{code}
listNMonoid : {X : Set} -> Monoid (<! ListN !>N X)
listNMonoid = record
  {  neut  = 0 , <>
  ;  _&_   = vv \ xn xs -> vv \ yn ys -> xn +Nat yn , xs ++ ys 
  }
\end{code}
%endif
\end{exe}

We have already seen that the identity functor |VecN 1| is |Normal|, but can
we define composition?
%format oN = "\F{\circ_{\!N}}"
%format _oN_ = "\us{" oN "}"
\begin{spec}
_oN_ : Normal -> Normal -> Normal
F oN (ShG / szG) = ? / ?
\end{spec}
To choose the shape for the composite, we need to know the outer shape, and
then the inner shape at each element position. That is:
\begin{spec}
_oN_ : Normal -> Normal -> Normal
F oN (ShG / szG) = <! F !>N ShG / {!!}
\end{spec}
Now, the composite must have a place for each element of each inner structure,
so the size of the whole is the sum of the sizes of its parts. That is to say,
we must traverse the shape, summing the sizes of each inner shape therein.
Indeed, we can use |traverse|, given that |Nat| is a monoid for |+N| and
that |Normal| functors are traversable because vectors are.
%format sumMonoid = "\F{sumMonoid}"
%format normalTraversable = "\F{normalTraversable}"
\begin{code}
sumMonoid : Monoid Nat
sumMonoid = record { neut = 0; _&_ = _+Nat_ }

normalTraversable : (F : Normal) -> Traversable <! F !>N
normalTraversable F = record
  { traverse = \ {{aG}} f -> vv \ s xs -> pure {{aG}}  (_,_ s) <*> traverse f xs }
\end{code}

Armed with this structure, we can implement the composite size operator as a
|crush|.
\begin{code}
_oN_ : Normal -> Normal -> Normal
F oN (ShG / szG) = <! F !>N ShG / crush {{normalTraversable F}} szG
\end{code}

The fact that we needed only the |Traversable| interface to |F| is a bit of a
clue to a connection between |Traversable| and |Normal| functors.
|Traversable| structures have a notion of size induced by the |Monoid|
structure for |Nat|:
%format listNMonoid = "\F{listNMonoid}"
%format sizeT = "\F{sizeT}"
\begin{code}
sizeT : forall {F}{{TF : Traversable F}}{X} -> F X -> Nat
sizeT = crush (\ _ -> 1)
\end{code}

Hence, every |Traversable| functor has a |Normal| counterpart
%format normalT = "\F{normalT}"
\begin{code}
normalT : forall F {{TF : Traversable F}} -> Normal
normalT F = F One / sizeT
\end{code}
where the shape is an |F| with placeholder elements and the size is the number
of such places.

Can we put a |Traversable| structure into its |Normal| representation?
We can certainly extract the shape:
%format shapeT = "\F{shapeT}"
\begin{code}
shapeT : forall {F}{{TF : Traversable F}}{X} -> F X -> F One
shapeT = traverse (\ _ -> <>)
\end{code}
We can also define the list of elements, which should have the same length as
the size
%format contentsT = "\F{contentsT}"
%format one = "\F{one}"
\begin{code}
one : forall {X} -> X -> <! ListN !>N X
one x = 1 , (x , <>)

contentsT : forall {F}{{TF : Traversable F}}{X} -> F X -> <! ListN !>N X
contentsT = crush one
\end{code}
and then try
%format toNormal = "\F{toNormal}"
\begin{spec}
toNormal : forall {F}{{TF : Traversable F}}{X} -> F X -> <! normalT F !>N X
toNormal fx = BAD (shapeT fx , snd (contentsT fx))
\end{spec}
but it fails to typecheck because the size of the shape of |fx|
is not obviously the length of the contents of |fx|.
The trouble is that |Traversable F| is
underspecified. In due course, we shall discover that it means 
just that
|F| is naturally isomorphic to |<! normalT F !>N|.\nudge{Check this.}
To see this, however, we shall need the capacity to reason equationally,
which must wait until the next section.


\begin{exe}[normal morphisms]
A normal morphism is given as follows
%format -N> = "\F{\to}_{\F{N}}"
%format _-N>_ = "\us{" -N> "}"
\begin{code}
_-N>_ : Normal -> Normal -> Set
F -N> G = (s : Shape F) -> <! G !>N (Fin (size F s))
\end{code}
%format nMorph = "\F{nMorph}"
where any such thing determines a \emph{natural transformation} from |F| to |G|.
\begin{code}
nMorph : forall {F G} -> F -N> G -> forall {X} -> <! F !>N X -> <! G !>N X
nMorph f (s , xs)  with f s
...                | s' , is = s' , map (proj xs) is
\end{code}
Show how to compute the normal morphism representing a given natural
transformation.
%format morphN = "\F{morphN}"
\begin{spec}
morphN : forall {F G} -> (forall {X} -> <! F !>N X -> <! G !>N X) -> F -N> G
morphN f s = ?
\end{spec}
%if False
\begin{code}
morphN : forall {F G} -> (forall {X} -> <! F !>N X -> <! G !>N X) -> F -N> G
morphN f s = f (s , tabulate id)
\end{code}
%endif
\end{exe}

\begin{exe}[Hancock's tensor]
Let
%format >< = "\F{\otimes}"
%format _><_ = "\us{" >< "}"
\begin{code}
_><_ : Normal -> Normal -> Normal
(ShF / szF) >< (ShG / szG) = (ShF * ShG) / vv \ f g -> szF f *Nat szG g
\end{code}
Construct normal morphisms:
%format swap = "\F{swap}"
%format drop = "\F{drop}"
\begin{spec}
swap : (F G : Normal) -> (F >< G) -N> (G >< F)
swap F G x = ?

drop : (F G : Normal) -> (F >< G) -N> (F oN G)
drop F G x = ?
\end{spec}
Hint: for |swap|, you may find you need to build some operations manipulating
matrices.
Hint: for |drop|, it may help to prove a theorem about multiplication (see next
section for details of equality), but you can get away without so doing.
%if False
\begin{code}
tomato : forall m n {X} -> Vec X (m *Nat n) -> Vec (Vec X n) m
tomato zero n <> = <>
tomato (suc m) n xs with split n (m *Nat n) xs
tomato (suc m) n .(ys ++ zs) | from (ys , zs) = ys , tomato m n zs

otamot : forall m n {X} -> Vec (Vec X n) m -> Vec X (m *Nat n)
otamot zero n <> = <>
otamot (suc m) n (xs , xss) = xs ++ otamot m n xss

swap : (F G : Normal) -> (F >< G) -N> (G >< F)
swap F G (f , g) = (g , f) ,
  otamot (size G g) (size F f)
   (transpose
     (tomato (size F f) (size G g) (tabulate id)))

drop : (F G : Normal) -> (F >< G) -N> (F oN G)
drop F G (f , g) = (f , pure g) , subst (help (size F f)) (Vec _) (tabulate id) where
  help : forall n -> (n *Nat size G g) == (crush (size G) (vec {n} g))
  help zero = refl
  help (suc n) rewrite help n = refl
\end{code}
%endif
\end{exe}
