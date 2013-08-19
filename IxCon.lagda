%if False
\begin{code}
module IxCon where

open import Vec public
open import STLC public
\end{code}
%endif

There are lots of ways to present indexed containers, giving ample
opportunities for exercises, but I shall use the Hancock presentation,
as it has become my preferred version, too.

The idea is to describe functors between indexed families of sets.
%format i> = "\D{\triangleright}"
%format _i>_ = "\us{" i> "}"
%format ri = "\F{ri}"
%format _<1_$_ = _ <1 _ $ _
%format !>i = !> "_{\F{i}}"
%format <!_!>i = <! _ !>i
\begin{code}
record _i>_ (I J : Set) : Set1 where
  constructor _<1_$_
  field
    Sh : J        -> Set
    Po : (j : J)  -> Sh j -> Set
    ri : (j : J)(s : Sh j)(p : Po j s) -> I
  <!_!>i : (I -> Set) -> (J -> Set)
  <!_!>i X j = Sg (Sh j) \ s -> (p : Po j s) -> X (ri j s p)
open _i>_ public
\end{code}
An |I i> J| describes a |J|-indexed thing with places for |I|-indexed elements.
Correspondingly, some |j : J| tells us which sort of thing we're making,
determining a shape set |Sh j| and a position family |Po j|, just as with plain
containers. The |ri| function then determines which |I|-index is demanded in
each element position.

\paragraph{Interaction structures} Hancock calls these indexed
containers \emph{interaction structures}. Consider |J| to be the set
of possible `states of the world' before an interaction, and |I| the
possible states afterward.  The `before' states will determine a
choice of commands we can issue, each of which has a set of possible
responses which will then determine the state `after'. An interaction
structure thus describes the predicate transformer which describes the
precondition for achieving a postcondition by one step of interaction.
We are just using proof-relevant Hoare logic as the type system!

\begin{exe}[functoriality]
We have given the interpretation of indexed containers as operations on
indexed families of sets. Equip them with their functorial action for
the following notion of morphism
\begin{code}
_-:>_ : forall {I : Set} -> (I -> Set) -> (I -> Set) -> Set
X -:> Y = forall i -> X i -> Y i
\end{code}

\begin{spec}
ixMap : forall {I J}{C : I i> J}{X Y} -> (X -:> Y) -> <! C !>i X -:> <! C !>i Y
ixMap f j xs = ?
\end{spec}
%if False
\begin{code}
ixMap : forall {I J}{C : I i> J}{X Y} -> (X -:> Y) -> <! C !>i X -:> <! C !>i Y
ixMap f j (s , k) = s , \ p -> f _ (k p)
\end{code}
%endif
\end{exe}


\section{Petersson-Synek Trees}

Kent Petersson and Dan Synek proposed a universal inductive family,
amounting to the fixpoint of an indexed container

\begin{code}
data Tree {J : Set}(C : J i> J)(j : J) : Set where
  <$_$> : <! C !>i (Tree C) j -> Tree C j
\end{code}

The natural numbers are a friendly, if degenerate example.
%format NatC = "\F{NatC}"
%format zeroC = "\F{zeroC}"
%format sucC = "\F{sucC}"
\begin{code}
NatC : One i> One
NatC = (\ _ -> Two) <1 (\ _ -> Zero <?> One) $ _

zeroC : Tree NatC <>
zeroC = <$ tt , magic $>

sucC : Tree NatC <> -> Tree NatC <>
sucC n = <$ ff , pure n $>
\end{code}
This is just the indexed version of the |W|-type, so the same issue with
extensionality arises.

We may also define the node structure for vectors as an instance.
%format VecC = "\F{VecC}"
%format VS = "\F{VS}"
%format VP = "\F{VP}"
%format Vr = "\F{Vr}"
\begin{code}
VecC : Set -> Nat i> Nat
VecC X = VS <1 VP $ Vr where  -- depending on the length
  VS : Nat -> Set
  VS zero             = One   -- nil is unlabelled
  VS (suc n)          = X     -- cons carried an element
  VP : (n : Nat) -> VS n -> Set
  VP zero     _       = Zero  -- nil has no children
  VP (suc n)  _       = One   -- cons has one child
  Vr : (n : Nat)(s : VS n)(p : VP n s) -> Nat
  Vr zero     <>  ()          -- nil has no children to index
  Vr (suc n)  x   <>  = n     -- the tail of a cons has the length one less
\end{code}

Let us at least confirm that we can rebuild the constructors.

\begin{code}
vnil : forall {X} -> Tree (VecC X) zero
vnil = <$ <> , (\ ()) $>

vcons :  forall {X n} -> X -> Tree (VecC X) n -> Tree (VecC X) (suc n)
vcons x xs = <$ (x , (\ _ -> xs)) $>
\end{code}

Why don't you have a go at rebuilding an inductive family in this manner?

\begin{exe}[simply typed $\lambda$-calculus]
Define the simply typed $\lambda$-terms as Petersson-Synek trees.
%format STLC = "\F{STLC}"
\begin{spec}
STLC : (Cx Ty * Ty) i> (Cx Ty * Ty)
STLC = ?
\end{spec}
Implement the constructors.
%if False
\begin{code}
IsArr : Ty -> Set
IsArr iota = Zero
IsArr (_ ->> _) = One

STLC : (Cx Ty * Ty) i> (Cx Ty * Ty)
STLC = (vv \ G T -> (T <: G) + (Ty + IsArr T)) <1
       (\  {  (G , T) (tt , _)       -> Zero
           ;  (G , T) (ff , tt , _)  -> Two
           ;  (G , T) (ff , ff , _)  -> One
           }) $
       (\  {  (G , T) (tt , _) ()
           ;  (G , T) (ff , tt , S) tt  -> G , S ->> T
           ;  (G , T) (ff , tt , S) ff  -> G , S
           ;  (G , iota) (ff , ff , ()) _
           ;  (G , S ->> T) (ff , ff , p) _   -> (G :: S) , T
           })

stlcV : forall {G T} -> T <: G -> Tree STLC (G , T)
stlcV x = <$ ((tt , x) , \ ()) $>

stlcA :  forall {G S T} ->
         Tree STLC (G , S ->> T) -> Tree STLC (G , S) -> Tree STLC (G , T)
stlcA f s = <$ (ff , (tt , _)) , (f <?> s) $>

stlcL :  forall {G S T} -> Tree STLC ((G :: S) , T) -> Tree STLC (G , S ->> T)
stlcL t = <$ ((ff , (ff , _)) , \ _ -> t) $>
\end{code}
%endif
\end{exe}


\section{Closure Properties}

It is not difficult to show that indexed containers have an identity
composition which is compatible up to isomorphism with those of their
interpretations.

\begin{exe}[identity and composition]
Construct
\begin{spec}
IdIx : forall {I} -> I i> I
IdIx = ?
\end{code}
%if False
\begin{code}
IdIx : forall {I} -> I i> I
IdIx = (\ _ -> One) <1 (\ _ _ -> One) $ \ i _ _ -> i
\end{code}
%endif
such that
\[ |<! IdIx !>i X i| \cong |X i|
\]
Similarly, construct the composition
\begin{spec}
CoIx : forall {I J K} -> J i> K -> I i> J -> I i> K
CoIx C C' = ?
\end{code}
%if False
\begin{code}
CoIx : forall {I J K} -> J i> K -> I i> J -> I i> K
CoIx (S <1 P $ r) (S' <1 P' $ r')
  =    (\ k -> Sg (S k) \ s -> (p : P k s) -> S' (r k s p))
   <1  (\ k -> vv \ s f -> Sg (P k s) \ p -> P' (r k s p) (f p))
   $   (\ { k (s , f) (p , p') -> r' (r k s p) (f p) p'})
\end{code}
%endif
such that
\[ |<! CoIx C C' !>i X k| \cong |<! C !>i (<! C' !>i X) k|
\]
\end{exe}

It may be useful to consider constructing binary products and
coproducts, but let us chase after richer structure, exploiting
dependent types to a greater extent. We\nudge{My motivation for level
polymorphism will appear in due course.} may describe a class of
indexed functors, as follows.

\begin{code}
data Desc {l}(I : Set l) : Set (lsuc l) where
  var    : I -> Desc I
  sg pi  : (A : Set l)(D : A -> Desc I) -> Desc I
  _*D_   : Desc I -> Desc I -> Desc I
  kD     : Set l -> Desc I
infixr 4 _*D_
\end{code}
which admit a direct interpretation as follows
\begin{code}
<!_!>D : forall {l}{I : Set l} -> Desc I -> (I -> Set l) -> Set l
<! var i !>D    X  = X i
<! sg A D !>D   X  = Sg A \ a -> <! D a !>D X
<! pi A D !>D   X  = (a : A) -> <! D a !>D X
<! D *D E !>D   X  = <! D !>D X * <! E !>D X
<! kD A !>D     X  = A
\end{code}

A family of such descriptions in |J -> Desc I| thus determines, pointwise,
a functor from |I -> Set| to |J -> Set|. It is easy to see that every indexed
container has a description.
\begin{code}
ixConDesc : forall {I J} -> I i> J -> J -> Desc I
ixConDesc (S <1 P $ r) j = sg (S j) \ s -> pi (P j s) \ p -> var (r j s p)
\end{code}

Meanwhile, up to isomorphism at least, we can go the other way around.

\begin{exe}[from |J -> Desc I| to |I i> J|]
Construct functions
\begin{spec}
DSh : {I : Set} -> Desc I -> Set
DSh D = ?
DPo : forall {I}(D : Desc I) -> DSh D -> Set
DPo D s = ?
Dri : forall {I}(D : Desc I)(s : DSh D) -> DPo D s -> I
Dri D s p = ?
\end{spec}
%if False
\begin{code}
DSh : {I : Set} -> Desc I -> Set
DSh (var i) = One
DSh (sg A D) = Sg A \ a -> DSh (D a)
DSh (pi A D) = (a : A) -> DSh (D a)
DSh (D *D D') = DSh D * DSh D'
DSh (kD A) = A
DPo : forall {I}(D : Desc I) -> DSh D -> Set
DPo (var i) s = One
DPo (sg A D) (a , s) = DPo (D a) s
DPo (pi A D) f = Sg A \ a -> DPo (D a) (f a)
DPo (D *D D') (s , s') = DPo D s + DPo D' s'
DPo (kD A) s = Zero
Dri : forall {I}(D : Desc I)(s : DSh D) -> DPo D s -> I
Dri (var i) s p = i
Dri (sg A D) (a , s) p = Dri (D a) s p
Dri (pi A D) f (a , p) = Dri (D a) (f a) p
Dri (D *D D') (s , s') (tt , p) = Dri D s p
Dri (D *D D') (s , s') (ff , p) = Dri D' s' p
Dri (kD A) s ()
\end{code}
%endif
in order to compute the indexed container form of a family of descriptions.
\begin{code}
descIxCon : forall {I J} -> (J -> Desc I) -> I i> J
descIxCon F = (DSh o F) <1 (DPo o F) $ (Dri o F)
\end{code}
Exhibit the isomorphism
\[
  |<! descIxCon F !>i X j| \cong |<! F j !>D X|
\]
\end{exe}

We shall find further closure properties of indexed containers later,
but let us explore description awhile.


\section{Describing Datatypes}

Descriptions are quite a lot like inductive family declarations. The
traditional |Vec| declaration corresponds to

\begin{code}
vecD : Set -> Nat -> Desc Nat
vecD X n =
  sg Two    (     kD (n == zero)
            <?>   sg Nat \ k -> kD X *D var k *D kD (n == suc k)
            )
\end{code}

The choice of constructors becomes a |sg|-description. Indices specialized
in the return types of constructors become explicit equational constraints.
However, in defining a family of descriptions, we are free to use the full
computational power of the function space, inspecting the index, e.g.

\begin{code}
vecD' : Set -> Nat -> Desc Nat
vecD' X zero     = kD One
vecD' X (suc n)  = kD X *D var n
\end{code}

To obtain a datatype from a description, we can turn it into a container and
use the Petersson-Synek tree, or we can preserve the first orderness of first
order things and use the direct interpretation.

\begin{code}
data Data {l}{J : Set l}(F : J -> Desc J)(j : J) : Set l where
  <$_$> : <! F j !>D (Data F) -> Data F j
\end{code}

\begin{exe}[something like `levitation']
Construct a family of descriptions which describes a type like |Desc|.
As Agda is not natively cumulative, you will need to shunt types up
through the |Set l| hierarchy by hand, with this gadget:
\begin{code}
record Up {l}(X : Set l) : Set (lsuc l) where
  constructor up
  field
    down : X
open Up
\end{code}
Now implement
\begin{spec}
DescD : forall {l}(I : Set l) -> One{lsuc l} -> Desc (One{lsuc l})
DescD {l} I _ = ?
\end{spec}
%if False
\begin{code}
data DescT {l} : Set l where var sg pi timesD kD : DescT

DescD : forall {l}(I : Set l) -> One{lsuc l} -> Desc (One{lsuc l})
DescD {l} I _ = sg DescT (\
  { var     -> kD (Up I)
  ; sg      -> sg (Set l) (\ A -> pi (Up A) \ _ -> var <>)
  ; pi      -> sg (Set l) (\ A -> pi (Up A) \ _ -> var <>)
  ; timesD  -> var <> *D var <>
  ; kD      -> kD (Set l)
  })
\end{code}
%endif
Check that you can map your described descriptions back to descriptions.
\begin{spec}
desc : forall {l}{I : Set l} -> Data (DescD I) <> -> Desc I
desc D = ?
\end{spec}
%if False
\begin{code}
desc : forall {l}{I : Set l} -> Data (DescD I) <> -> Desc I
desc <$ var , up i $> = var i
desc <$ sg , A , D $> = sg A \ a -> desc (D (up a))
desc <$ pi , A , D $> = pi A \ a -> desc (D (up a))
desc <$ timesD , D , D' $> = desc D *D desc D'
desc <$ kD , A $> = kD A
\end{code}
%endif
\end{exe}

We could, if we choose, work entirely with described datatypes. Perhaps,
in some future programming language, the external |Desc I| type will be
identified with the internal |Data (DescD I) <>| so that |Data| is the
\emph{only} datatype.


\section{Some Useful Predicate Transformers}

A container stores a bunch of data. If we have a predicate |P| on
data, it might be useful to formulate the predicates on bunches of
data asserting that |P| holds \emph{everywhere} or \emph{somewhere}.
But an indexed container is a predicate transformer! We can thus
close indexed containers under the formation of `everywhere'.

\begin{code}
Everywhere : forall {I J}(C : I i> J)(X : I -> Set) -> Sg I X i> Sg J (<! C !>i X)
Everywhere (S <1 P $ r) X
  =   (\ _ -> One)
  <1  (\ { (j , s , k) _ -> P j s })
  $   (\ { (j , s , k) _ p -> r j s p , k p })
\end{code}

The witnesses to the property of the elements of the original container
become the elements of the derived container.
The trivial predicate holds everywhere.

\begin{code}
allTrivial : forall {I J}(C : I i> J)(X : I -> Set) jc ->
             <! Everywhere C X !>i (\ _ -> One) jc
allTrivial C X _ = <> , \ p -> <>
\end{code}

If you think of simply typed $\lambda$-calculus contexts as containers
of types, then an \emph{environment} is given by supplying values |Everywhere|.

Meanwhile, the finger now points at you, pointing a finger at an element.

\begin{exe}[Somewhere]
Construct the transformer which takes |C| to the container for witnesses
that a property holds for some element of a |C|-structure
\begin{spec}
Somewhere : forall {I J}(C : I i> J)(X : I -> Set) -> Sg I X i> Sg J (<! C !>i X)
Somewhere (S <1 P $ r) X
  =   ?
  <1  ?
  $   ?
\end{spec}
%if False
\begin{code}
Somewhere : forall {I J}(C : I i> J)(X : I -> Set) -> Sg I X i> Sg J (<! C !>i X)
Somewhere (S <1 P $ r) X
  =   (\ { (j , s , k) -> P j s })
  <1  (\ { (j , s , k) _ -> One })
  $   (\ { (j , s , k) p _ -> r j s p , k p })
\end{code}
%endif
Check that the impossible predicate cannot hold somewhere.
\begin{spec}
noMagic : forall {I J}(C : I i> J)(X : I -> Set) jc ->
             <! Somewhere C X !>i (\ _ -> Zero) jc -> Zero
noMagic C X _ (p , m) = ?
\end{spec}
%if False
\begin{code}
noMagic : forall {I J}(C : I i> J)(X : I -> Set) jc ->
             <! Somewhere C X !>i (\ _ -> Zero) jc -> Zero
noMagic C X _ (p , m) = m <>
\end{code}
%endif
\end{exe}

For simply typed $\lambda$-calculus contexts, a variable of type |T| is just
the evidence that a type equal to |T| is somewhere. Environment lookup is
just the obvious property that if |Q| holds everywhere and |R| holds somewhere,
then their conjunction holds somewhere, too.

\begin{exe}[lookup]
Implement generalized environment lookup.
\begin{spec}
lookup :  forall {I J}(C : I i> J)(X : I -> Set) jc {Q R} ->
          <! Everywhere C X !>i Q jc -> <! Somewhere C X !>i R jc ->
          <! Somewhere C X !>i (\ ix -> Q ix * R ix) jc
lookup C X jc qs r = ?
\end{spec}
%if False
\begin{code}
lookup : forall {I J}(C : I i> J)(X : I -> Set) jc {Q R} ->
         <! Everywhere C X !>i Q jc -> <! Somewhere C X !>i R jc ->
         <! Somewhere C X !>i (\ ix -> Q ix * R ix) jc
lookup C X _ (_ , q) (p , r) = p , (\ _ -> q p , r <>)
\end{code}
%endif
\end{exe}

A key use of the |Everywhere| transformer is in the formulation
of \emph{induction} principles. The induction hypotheses amount to
asserting that the induction predicate holds at every substructure..

\begin{code}
treeInd :  forall {I}(C : I i> I)(P : Sg I (Tree C) -> Set) ->
           (  <! Everywhere C (Tree C) !>i P -:>
              (vv \ i ts -> P (i , <$ ts $>)) ) ->
           (i : I)(t : Tree C i) -> P (i , t)
treeInd C P m i <$ s , k $> = m (i , s , k) (<> , \ p -> treeInd C P m _ (k p))
\end{code}

The step method of the above looks a bit like an algebra, modulo plumbing.

\begin{exe}[induction as a fold]
Petersson-Synek trees come with a `fold' operator, making |Tree C|
(weakly) initial for |<! C !>i|. We can compute any |P| from a |Tree C|,
given a |C|-algebra for |P|.
\begin{code}
treeFold :  forall {I}(C : I i> I)(P : I -> Set) ->
            (<! C !>i P -:> P) ->
            (Tree C -:> P)
treeFold C P m i <$ s , k $> = m i (s , \ p -> treeFold C P m _ (k p))
\end{code}
However, |treeFold| does not give us \emph{dependent} induction on |Tree C|.
If al you have is a hammer, everything looks like a nail. If we want to
compute why some |P : Sg I (Tree C) -> Set| always holds, we'll need an
indexed container storing |P|s in positions corresponding to the children
of a given tree. The |Everywhere C| construct does most of the work,
but you need a little adaptor to unwrap the |C| container inside the |Tree C|.
\begin{spec}
Children : forall {I}(C : I i> I) -> Sg I (Tree C) i> Sg I (Tree C)
Children C = CoIx ? (Everywhere C (Tree C))
\end{spec}
%if False
\begin{code}
Delta : forall {I J} -> (J -> I) -> I i> J
Delta f = descIxCon (var o f)

kids : forall {I}{C : I i> I} -> Sg I (Tree C) -> Sg I \ i -> <! C !>i (Tree C) i
kids (i , <$ ts $>) = i , ts

Children : forall {I}(C : I i> I) -> Sg I (Tree C) i> Sg I (Tree C)
Children C = CoIx (Delta kids) (Everywhere C (Tree C))
\end{code}
%endif
Now, you can extract a general induction principle for |Tree C| from
|treeFold (Children C)|, but you will need a little construction. Finish the
job.
\begin{spec}
treeFoldInd :  forall {I}(C : I i> I) P ->
               (<! Children C !>i P -:> P) ->
               forall it -> P it
treeFoldInd C P m (i , t) = treeFold (Children C) P m (i , t) ?
\end{spec}
\begin{code}
children : forall {I}(C : I i> I) i t -> Tree (Children C) (i , t)
children C i <$ s , k $> = <$ _ , (vv (\ _ p -> children C _ (k p))) $>

treeFoldInd :  forall {I}(C : I i> I) P ->
               (<! Children C !>i P -:> P) ->
               forall it -> P it
treeFoldInd C P m (i , t) = treeFold (Children C) P m (i , t) (children C i t)
\end{code}
Of course, you need to do what is effectively an inductive proof to fill in the
hole. Induction really does amount to more than weak initiality. But one last
induction will serve for all.
\end{exe}

What goes for containers goes for descriptions. We can biuld all the equipment of
this section for |Desc| and |Data|, too.

\begin{exe}[everywhere and somewhere for |Desc|]
Define suitable description transformers, capturing what it means for a predicate to hold in every or some element position within a given described structure.
\begin{spec}
EverywhereD SomewhereD :  {I : Set}(D : Desc I)(X : I -> Set) ->
                          <! D !>D X -> Desc (Sg I X)
EverywhereD  D X xs = ?
SomewhereD   D X xs = ?
\end{spec}
\begin{code}
EverywhereD SomewhereD :  {I : Set}(D : Desc I)(X : I -> Set) ->
                          <! D !>D X -> Desc (Sg I X)
EverywhereD (var i) X x = var (i , x)
EverywhereD (sg A D) X (a , xs) = EverywhereD (D a) X xs
EverywhereD (pi A D) X f = pi A \ a -> EverywhereD (D a) X (f a)
EverywhereD (D *D D') X (xs , xs') = EverywhereD D X xs *D EverywhereD D' X xs'
EverywhereD (kD A) X a = kD One
SomewhereD (var i) X x = var (i , x)
SomewhereD (sg A D) X (a , xs) = SomewhereD (D a) X xs
SomewhereD (pi A D) X f = sg A \ a -> SomewhereD (D a) X (f a)
SomewhereD (D *D D') X (xs , xs') =
  sg Two (SomewhereD D X xs <?> SomewhereD D' X xs')
SomewhereD (kD A) X a = kD Zero
\end{code}
Now construct
\begin{spec}
dataInd : forall {I : Set}(F : I -> Desc I)(P : Sg I (Data F) -> Set) ->
          (  (i : I)(ds : <! F i !>D (Data F)) ->
             <! EverywhereD (F i) (Data F) ds !>D P -> P (i , <$ ds $>)) ->
          forall i d -> P (i , d)
dataInd F P m i d = ?
\end{spec}
%if False
\begin{code}
dataInd : forall {I : Set}(F : I -> Desc I)(P : Sg I (Data F) -> Set) ->
          (  (i : I)(ds : <! F i !>D (Data F)) ->
             <! EverywhereD (F i) (Data F) ds !>D P -> P (i , <$ ds $>)) ->
          forall i d -> P (i , d)
dataInd F P m i <$ ds $> = m i ds (help (F i) ds) where
  help : (D : Desc _)(ds : <! D !>D (Data F)) -> <! EverywhereD D (Data F) ds !>D P
  help (var i) d = dataInd F P m i d
  help (sg A D) (a , ds) = help (D a) ds
  help (pi A D) f = \ a -> help (D a) (f a)
  help (D *D D') (ds , ds') = help D ds , help D' ds'
  help (kD A) a = <>
\end{code}
%endif
\end{exe}


\section{Indexed Containers are Closed Under Fixpoints}

So far, we have used indexed containers to describe the node
structures of recursive data, but we have not considered recursive
data structures to be containers themselves. Consider, e.g., the
humble vector: might we not consider the vector's elements to be a
kind of contained thing, just as much as its subvectors? We can just throw
in an extra kind of element!
\begin{code}
vecNodeIx : (One + Nat) i> Nat
vecNodeIx = descIxCon {J = Nat} \
  {  zero     -> kD One
  ;  (suc n)  -> var (tt , <>) *D var (ff , n)
  }
\end{code}

That is enough to see vector \emph{nodes} as containers of elements or
subnodes, but it still does not give \emph{vectors} as containers:
\begin{spec}
vecIx : One i> Nat
vecIx = ?
\end{spec}
We should be able to solve this goal by taking |vecNodeIx| and tying a
recursive knot at positions labelled |(ff , n)|, retaining positions
labelled |(tt , <>)|. Let us try the general case.
\begin{code}
MuIx : forall {I J} -> (I + J) i> J -> I i> J
MuIx {I}{J} F = (Tree F' o _,_ ff) <1 (P o _,_ ff) $ (r o _,_ ff) where
\end{code}
The shapes of the recursive structures are themselves trees, with unlabelled
leaves at |I|-indexed places and |F|-nodes in |J|-indexed places. We could try
to work in |J i> J|, cutting out the non-recursive positions. However, it is
easier to shift to |(I + J) i> (I + J)|, introducing `unlabelled leaf' as the
dull node structure whenever an |I| shape is requested. We may construct
\begin{code}
  F'  :   (I + J) i> (I + J)
  F'  =   (vv (\ i -> One)     <?> Sh F)
      <1  (vv (\ _ _ -> Zero)  <?> Po F)
      $   (vv (\ t s ())       <?> ri F)
\end{code}
and then choose to start with |(ff , j)| for the given top level |j| index.
A position is then a path to a leaf: either we are at a leaf already, or we
must descend further.
\begin{code}
  P : (x : I + J) -> Tree F' x -> Set
  P (tt , i)  _            = One
  P (ff , j)  <$ s , k $>  = Sg (Po F j s) \ p -> P (ri F j s p) (k p)
\end{code}
Finally, we may follow each path to its indicated leaf and return the
index which sent us there.
\begin{code}
  r : (x : I + J)(t : Tree F' x) -> P x t -> I
  r (tt , i)  _            _         = i
  r (ff , j)  <$ s , k $>  (p , ps)  = r _ (k p) ps
\end{code}

Let us check that this recipe cooks the vectors.

\begin{code}
vecIx : One i> Nat
vecIx = MuIx vecNodeIx

Vec' : Set -> Nat -> Set
Vec' X = <! vecIx !>i (\ _ -> X)

vnil' : forall {X} -> Vec' X zero
vnil' = <$ (<> , \ ()) $> , (vv \ ())

vcons' : forall {X n} -> X -> Vec' X n -> Vec' X (suc n)
vcons' x (s , k)
  =  <$ _ ,  (\ { (tt , _) -> <$ (_ , \ ()) $>  ; (ff , _) -> s }) $>
  ,          (\ { ((tt , _) , _) -> x           ; ((ff , _) , p) -> k p })
\end{code}

\begin{code}
data Desc' (I : Set) : Set1 where
  var : I -> Desc' I
  sg pi : (A : Set)(D : A -> Desc' I) -> Desc' I
  _*D_ : Desc' I -> Desc' I -> Desc' I
  kD : Set -> Desc' I
  mu : (J : Set) -> (J -> Desc' (I + J)) -> J -> Desc' I

mutual
  <!_!>' : forall {I} -> Desc' I -> (I -> Set) -> Set
  <! var i !>'     X  = X i
  <! sg A D !>'    X  = Sg A \ a -> <! D a !>' X
  <! pi A D !>'    X  = (a : A) -> <! D a !>' X
  <! D *D E !>'    X  = <! D !>' X * <! E !>' X
  <! kD A !>'      X  = A
  <! mu J F j !>'  X  = Data' F X j

  data Data' {I J}(F : J -> Desc' (I + J))(X : I -> Set)(j : J) : Set where
    <$_$> : <! F j !>' (vv X <?> Data' F X) -> Data' F X j
\end{code}

