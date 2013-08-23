%if False
\begin{code}
module IxCon where

open import Vec public
open import Normal public
open import STLC public
open import Containers public
\end{code}
%endif

There are lots of ways to present indexed containers, giving ample
opportunities for exercises, but I shall use the Hancock presentation,
as it has become my preferred version, too.

The idea is to describe functors between indexed families of sets.
%format i> = "\D{\triangleright}"
%format _i>_ = "\us{" i> "}"
%format riIx = "\F{riIx}"
%format ShIx = "\F{ShIx}"
%format PoIx = "\F{PoIx}"
%format <i = "\C{\triangleleft}"
%format _<i_$_ = _ <i _ $ _
%format !>i = !> "_{\F{i}}"
%format <!_!>i = <! _ !>i
\begin{code}
record _i>_ (I J : Set) : Set1 where
  constructor _<i_$_
  field
    ShIx : J        -> Set
    PoIx : (j : J)  -> ShIx j -> Set
    riIx : (j : J)(s : ShIx j)(p : PoIx j s) -> I
  <!_!>i : (I -> Set) -> (J -> Set)
  <!_!>i X j = Sg (ShIx j) \ s -> (p : PoIx j s) -> X (riIx j s p)
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
%format lmax = "\F{lmax}"
\begin{code}
_-:>_ : forall {k l}{I : Set k} -> (I -> Set l) -> (I -> Set l) -> Set (lmax l k)
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

%format ITree = "\D{ITree}"
\begin{code}
data ITree {J : Set}(C : J i> J)(j : J) : Set where
  <$_$> : <! C !>i (ITree C) j -> ITree C j
\end{code}

The natural numbers are a friendly, if degenerate example.
%format NatC = "\F{NatC}"
%format zeroC = "\F{zeroC}"
%format sucC = "\F{sucC}"
\begin{code}
NatC : One i> One
NatC = (\ _ -> Two) <i (\ _ -> Zero <?> One) $ _

zeroC : ITree NatC <>
zeroC = <$ tt , magic $>

sucC : ITree NatC <> -> ITree NatC <>
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
VecC X = VS <i VP $ Vr where  -- depending on the length
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
vnil : forall {X} -> ITree (VecC X) zero
vnil = <$ <> , (\ ()) $>

vcons :  forall {X n} -> X -> ITree (VecC X) n -> ITree (VecC X) (suc n)
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
STLC = (vv \ G T -> (T <: G) + (Ty + IsArr T)) <i
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

stlcV : forall {G T} -> T <: G -> ITree STLC (G , T)
stlcV x = <$ ((tt , x) , \ ()) $>

stlcA :  forall {G S T} ->
         ITree STLC (G , S ->> T) -> ITree STLC (G , S) -> ITree STLC (G , T)
stlcA f s = <$ (ff , (tt , _)) , (f <?> s) $>

stlcL :  forall {G S T} -> ITree STLC ((G :: S) , T) -> ITree STLC (G , S ->> T)
stlcL t = <$ ((ff , (ff , _)) , \ _ -> t) $>
\end{code}
%endif
\end{exe}


\section{Closure Properties}

It is not difficult to show that indexed containers have an identity
composition which is compatible up to isomorphism with those of their
interpretations.

%format IdIx = "\F{IdIx}"
%format CoIx = "\F{CoIx}"
\begin{exe}[identity and composition]
Construct
\begin{spec}
IdIx : forall {I} -> I i> I
IdIx = ?
\end{spec}
%if False
\begin{code}
IdIx : forall {I} -> I i> I
IdIx = (\ _ -> One) <i (\ _ _ -> One) $ \ i _ _ -> i
\end{code}
%endif
such that
\[ |<! IdIx !>i X i| \cong |X i|
\]
Similarly, construct the composition
\begin{spec}
CoIx : forall {I J K} -> J i> K -> I i> J -> I i> K
CoIx C C' = ?
\end{spec}
%if False
\begin{code}
CoIx : forall {I J K} -> J i> K -> I i> J -> I i> K
CoIx (S <i P $ r) (S' <i P' $ r')
  =    (\ k -> Sg (S k) \ s -> (p : P k s) -> S' (r k s p))
   <i  (\ k -> vv \ s f -> Sg (P k s) \ p -> P' (r k s p) (f p))
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

%format lsuc = "\C{lsuc}"
%format Desc = "\D{Desc}"
%format sg = "\C{\upsigma}"
%format pi = "\C{\uppi}"
%format *D = "\C{\times}_{\C{D}}"
%format _*D_ = "\us{" *D "}"
%format kD = "\C{\upkappa}"
%format !>D = !> "_{\!\F{D}}"
%format <!_!>D = <! _ !>D
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
%format ixConDesc = "\F{ixConDesc}"
\begin{code}
ixConDesc : forall {I J} -> I i> J -> J -> Desc I
ixConDesc (S <i P $ r) j = sg (S j) \ s -> pi (P j s) \ p -> var (r j s p)
\end{code}

Meanwhile, up to isomorphism at least, we can go the other way around.

\begin{exe}[from |J -> Desc I| to |I i> J|]
Construct functions
%format DSh = "\F{DSh}"
%format DPo = "\F{DPo}"
%format Dri = "\F{Dri}"
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
%format descIxCon = "\F{descIxCon}"
\begin{code}
descIxCon : forall {I J} -> (J -> Desc I) -> I i> J
descIxCon F = (DSh o F) <i (DPo o F) $ (Dri o F)
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

%format vecD = "\F{vecD}"
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

%format vecD' = vecD
\begin{code}
vecD' : Set -> Nat -> Desc Nat
vecD' X zero     = kD One
vecD' X (suc n)  = kD X *D var n
\end{code}

To obtain a datatype from a description, we can turn it into a container and
use the Petersson-Synek tree, or we can preserve the first orderness of first
order things and use the direct interpretation.

%format Data = "\D{Data}"
\begin{code}
data Data {l}{J : Set l}(F : J -> Desc J)(j : J) : Set l where
  <$_$> : <! F j !>D (Data F) -> Data F j
\end{code}

%format vnil0 = "\F{vnil}"
%format vcons0 =  "\F{vcons}"
For example, let us once again construct vectors.
\begin{code}
vnil0 : forall {X} -> Data (vecD' X) zero
vnil0 = <$ <> $>

vcons0 : forall {X n} -> X -> Data (vecD' X) n -> Data (vecD' X) (suc n)
vcons0 x xs = <$ x , xs $>
\end{code}


\begin{exe}[something like `levitation']
Construct a family of descriptions which describes a type like |Desc|.
As Agda is not natively cumulative, you will need to shunt types up
through the |Set l| hierarchy by hand, with this gadget:
%format Up = "\D{\Uparrow}"
%format up = "\C{\uparrow}"
%format down = "\F{\downarrow}"
\begin{code}
record Up {l}(X : Set l) : Set (lsuc l) where
  constructor up
  field
    down : X
open Up public
\end{code}
Now implement
%format DescD = "\F{DescD}"
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
%format desc = "\D{desc}"
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

%format Everywhere = "\F{Everywhere}"
%format Somewhere = "\F{Somewhere}"
%format EverywhereD = "\F{EverywhereD}"
%format SomewhereD = "\F{SomewhereD}"

A container stores a bunch of data. If we have a predicate |P| on
data, it might be useful to formulate the predicates on bunches of
data asserting that |P| holds \emph{everywhere} or \emph{somewhere}.
But an indexed container is a predicate transformer! We can thus
close indexed containers under the formation of `everywhere'.

\begin{code}
Everywhere : forall {I J}(C : I i> J)(X : I -> Set) -> Sg I X i> Sg J (<! C !>i X)
Everywhere (S <i P $ r) X
  =   (\ _ -> One)
  <i  (\ { (j , s , k) _ -> P j s })
  $   (\ { (j , s , k) _ p -> r j s p , k p })
\end{code}

The witnesses to the property of the elements of the original container
become the elements of the derived container.
The trivial predicate holds everywhere.

%format allTrivial = "\F{allTrivial}"
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
Somewhere (S <i P $ r) X
  =   ?
  <i  ?
  $   ?
\end{spec}
%if False
\begin{code}
Somewhere : forall {I J}(C : I i> J)(X : I -> Set) -> Sg I X i> Sg J (<! C !>i X)
Somewhere (S <i P $ r) X
  =   (\ { (j , s , k) -> P j s })
  <i  (\ { (j , s , k) _ -> One })
  $   (\ { (j , s , k) p _ -> r j s p , k p })
\end{code}
%endif
Check that the impossible predicate cannot hold somewhere.
%format noMagic = "\F{noMagic}"
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

%format lookup = "\F{lookup}"
\begin{exe}[|lookup|]
Implement generalized environment |lookup|.
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

%format treeInd = "\F{treeInd}"
\begin{code}
treeInd :  forall {I}(C : I i> I)(P : Sg I (ITree C) -> Set) ->
           (  <! Everywhere C (ITree C) !>i P -:>
              (vv \ i ts -> P (i , <$ ts $>)) ) ->
           (i : I)(t : ITree C i) -> P (i , t)
treeInd C P m i <$ s , k $> = m (i , s , k) (<> , \ p -> treeInd C P m _ (k p))
\end{code}

The step method of the above looks a bit like an algebra, modulo plumbing.

%format treeFold = "\F{treeFold}"
\begin{exe}[induction as a fold]
Petersson-Synek trees come with a `fold' operator, making |ITree C|
(weakly) initial for |<! C !>i|. We can compute any |P| from a |ITree C|,
given a |C|-algebra for |P|.
\begin{code}
treeFold :  forall {I}(C : I i> I)(P : I -> Set) ->
            (<! C !>i P -:> P) ->
            (ITree C -:> P)
treeFold C P m i <$ s , k $> = m i (s , \ p -> treeFold C P m _ (k p))
\end{code}
However, |treeFold| does not give us \emph{dependent} induction on |ITree C|.
If al you have is a hammer, everything looks like a nail. If we want to
compute why some |P : Sg I (ITree C) -> Set| always holds, we'll need an
indexed container storing |P|s in positions corresponding to the children
of a given tree. The |Everywhere C| construct does most of the work,
but you need a little adaptor to unwrap the |C| container inside the |ITree C|.
%format Children = "\F{Children}"
\begin{spec}
Children : forall {I}(C : I i> I) -> Sg I (ITree C) i> Sg I (ITree C)
Children C = CoIx ? (Everywhere C (ITree C))
\end{spec}
%if False
\begin{code}
Delta : forall {I J} -> (J -> I) -> I i> J
Delta f = descIxCon (var o f)

kids : forall {I}{C : I i> I} -> Sg I (ITree C) -> Sg I \ i -> <! C !>i (ITree C) i
kids (i , <$ ts $>) = i , ts

Children : forall {I}(C : I i> I) -> Sg I (ITree C) i> Sg I (ITree C)
Children C = CoIx (Delta kids) (Everywhere C (ITree C))
\end{code}
%endif
Now, you can extract a general induction principle for |ITree C| from
|treeFold (Children C)|, but you will need a little construction. Finish the
job.
%format treeFoldInd = "\F{treeFoldInd}"
\begin{spec}
treeFoldInd :  forall {I}(C : I i> I) P ->
               (<! Children C !>i P -:> P) ->
               forall it -> P it
treeFoldInd C P m (i , t) = treeFold (Children C) P m (i , t) ?
\end{spec}
%if False
\begin{code}
children : forall {I}(C : I i> I) i t -> ITree (Children C) (i , t)
children C i <$ s , k $> = <$ _ , (vv (\ _ p -> children C _ (k p))) $>

treeFoldInd :  forall {I}(C : I i> I) P ->
               (<! Children C !>i P -:> P) ->
               forall it -> P it
treeFoldInd C P m (i , t) = treeFold (Children C) P m (i , t) (children C i t)
\end{code}
%endif
Of course, you need to do what is effectively an inductive proof to fill in the
hole. Induction really does amount to more than weak initiality. But one last
induction will serve for all.
\end{exe}

What goes for containers goes for descriptions. We can biuld all the equipment of
this section for |Desc| and |Data|, too.

\begin{exe}[|Everywhere| and |Somewhere| for |Desc|]
Define suitable description transformers, capturing what it means for a predicate to hold in every or some element position within a given described structure.
\begin{spec}
EverywhereD SomewhereD :  {I : Set}(D : Desc I)(X : I -> Set) ->
                          <! D !>D X -> Desc (Sg I X)
EverywhereD  D X xs = ?
SomewhereD   D X xs = ?
\end{spec}
%if False
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
%endif
Now construct
%format dataInd = "\F{dataInd}"
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
%format vecNodeIx = "\F{vecNodeIx}"
\begin{code}
vecNodeIx : (One + Nat) i> Nat
vecNodeIx = descIxCon {J = Nat} \
  {  zero     -> kD One
  ;  (suc n)  -> var (tt , <>) *D var (ff , n)
  }
\end{code}

That is enough to see vector \emph{nodes} as containers of elements or
subnodes, but it still does not give \emph{vectors} as containers:
%format vecIx = "\F{vecIx}"
\begin{spec}
vecIx : One i> Nat
vecIx = ?
\end{spec}
We should be able to solve this goal by taking |vecNodeIx| and tying a
recursive knot at positions labelled |(ff , n)|, retaining positions
labelled |(tt , <>)|. Let us try the general case.
%format MuIx = "\F{\upmu{}Ix}"
\begin{code}
MuIx : forall {I J} -> (I + J) i> J -> I i> J
MuIx {I}{J} F = (ITree F' o _,_ ff) <i (P' o _,_ ff) $ (r' o _,_ ff) where
\end{code}
The shapes of the recursive structures are themselves trees, with unlabelled
leaves at |I|-indexed places and |F|-nodes in |J|-indexed places. We could try
to work in |J i> J|, cutting out the non-recursive positions. However, it is
easier to shift to |(I + J) i> (I + J)|, introducing `unlabelled leaf' as the
dull node structure whenever an |I| shape is requested. We may construct
%format F' = "\F{F'}"
\begin{code}
  F'  :   (I + J) i> (I + J)
  F'  =   (vv (\ i -> One)     <?> ShIx F)
      <i  (vv (\ _ _ -> Zero)  <?> PoIx F)
      $   (vv (\ t s ())       <?> riIx F)
\end{code}
and then choose to start with |(ff , j)| for the given top level |j| index.
A position is then a path to a leaf: either we are at a leaf already, or we
must descend further.
%format P' = "\F{P'}"
\begin{code}
  P' : (x : I + J) -> ITree F' x -> Set
  P' (tt , i)  _            = One
  P' (ff , j)  <$ s , k $>  = Sg (PoIx F j s) \ p -> P' (riIx F j s p) (k p)
\end{code}
Finally, we may follow each path to its indicated leaf and return the
index which sent us there.
%format r' = "\F{r'}"
\begin{code}
  r' : (x : I + J)(t : ITree F' x) -> P' x t -> I
  r' (tt , i)  _            _         = i
  r' (ff , j)  <$ s , k $>  (p , ps)  = r' _ (k p) ps
\end{code}
%format F' = "\V{F'}"
%format P' = "\V{P'}"
%format r' = "\V{r'}"

Let us check that this recipe cooks the vectors.

%format Vec' = "\F{Vec}"
%format vnil' = "\F{vnil}"
%format vcons' = "\F{vcons}"
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


\section{Adding fixpoints to |Desc|}

%format Desc' = Desc
%format mu = "\C{\upmu}"
%format !>' = !>D
%format <!_!>' = <! _ !>'
%format Data' = Data

We can extend descriptions to include a fixpoint operator:
\begin{code}
data Desc' (I : Set) : Set1 where
  var    : I -> Desc' I
  sg pi  : (A : Set)(D : A -> Desc' I) -> Desc' I
  _*D_   : Desc' I -> Desc' I -> Desc' I
  kD     : Set -> Desc' I
  mu     : (J : Set) -> (J -> Desc' (I + J)) -> J -> Desc' I
\end{code}

The interpretation must now be defined mutuallu with the universal
inductive type.
\begin{code}
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

Indeed, |Desc Zero| now does quite a good job of reflecting |Set|,
except that the domains of |sg| and |pi| are not concretely represented,
an issue we shall attend to in the next chapter.


\begin{exe}[induction]
State and prove the induction principle for |Desc'|. (This is not an
easy exercise.)
\end{exe}


\section{Jacobians}

I am always amused when computing people complain about being made to
learn mathematics choose calculus as their favourite example of
something that is of no use to them. I, for one, am profoundly
grateful to have learned vector calculus: it is exactly what you need
to develop notions of `context' for dependent datatypes.

An indexed container in |I i> J| explains |J| sorts of structure in
terms of |I| sorts of elements, and as such, we acquire a \emph{Jacobian
matrix} of partial derivatives, in |I i> (J * I)|. A |(j , i)| derivative
is a structure of index |j| with a hole of index |i|. Here's how we
build it.
%format Jac = "\F{\mathcal{J}}"
\begin{code}
Jac : forall {I J} -> I i> J -> I i> (J * I)
Jac (S <i P $ r)
  =   (\ { (j , i) -> Sg (S j) \ s -> r j s ^-1 i })
  <i  (\ { (j , .(r j s p)) (s , from p) -> P j s - p })
  $   (\ { (j , .(r j s p)) (s , from p) (p' , _) -> r j s p' })
\end{code}
The shape of an |(i , j)|-derivative must select a |j|-indexed shape
for the structure, together with a position (the hole) whose index is
|i|. As in the simple case, a position in the derivative is any position
other than the hole, and its index is calculated as before.

\begin{exe}[plugging]
Check\nudge{Einstein's summation convention might be useful to infer the choice
and placement of quantifiers.}
that a decidable equality for positions is enough to define the
`plugging in' function.
%format plugIx = "\F{plugIx}"
\begin{spec}
plugIx :  forall {I J}(C : I i> J) ->
        ((j : J)(s : ShIx C j)(p p' : PoIx C j s) -> Dec (p == p')) ->
        forall {i j X} -> <! Jac C !>i X (j , i) -> X i -> <! C !>i X j
plugIx C eq? jx x = ?
\end{spec}
%if False
\begin{code}
plugIx :  forall {I J}(C : I i> J) ->
        ((j : J)(s : ShIx C j)(p p' : PoIx C j s) -> Dec (p == p')) ->
        forall {i j X} -> <! Jac C !>i X (j , i) -> X i -> <! C !>i X j
plugIx C eq? {X = X} ((s , from p) , k) x = s , help where
  help : (p : PoIx C _ s) -> X (riIx C _ s p)
  help p' with eq? _ s p' p 
  help .p | tt , refl = x
  help p' | ff , np = k (p' , np)
\end{code}
%endif
\end{exe}

%format Zipper = "\F{Zipper}"
%format zipOut = "\F{zipOut}"
\begin{exe}[the Zipper]
For a given |C : I i> I|, construct the indexed container
|Zipper C : (I * I) i> (I * I)| such that |ITree (Zipper C) (ir , ih)|
represents a one |ih|-hole context in a |ITree C ir|, represented
as a sequence of hole-to-root layers.
\begin{spec}
Zipper : forall {I} -> I i> I -> (I * I) i> (I * I)
Zipper C = ?
\end{spec}
%if False
\begin{code}
Zipper : forall {I} -> I i> I -> (I * I) i> (I * I)
Zipper {I} C
  =   (\ { (ir , ih) ->
              (ir == ih) + Sg I \ ip -> <! Jac C !>i (ITree C) (ip , ih) } )
  <i  (\ { _ (tt , _) -> Zero ; _ (ff , _) -> One })
  $   (\ { _ (tt , _) () ; (ir , ih) (ff , (ip , _)) _ -> (ir , ip) })
\end{code}
%endif
Check that you can zipper all the way out to the root.
\begin{spec}
zipOut :  forall {I}(C : I i> I){ir ih} ->
          ((i : I)(s : ShIx C i)(p p' : PoIx C i s) -> Dec (p == p')) ->
          ITree (Zipper C) (ir , ih) -> ITree C ih -> ITree C ir
zipOut C eq? cz t = ?
\end{spec}
%if False
\begin{code}
zipOut :  forall {I}(C : I i> I){ir ih} ->
          ((i : I)(s : ShIx C i)(p p' : PoIx C i s) -> Dec (p == p')) ->
          ITree (Zipper C) (ir , ih) -> ITree C ih -> ITree C ir
zipOut C eq? <$ (tt , refl)     , _ $>   t  = t
zipOut C eq? <$ (ff , (_ , c))  , cz $>  t
  = zipOut C eq? (cz <>) <$ plugIx C eq? c t $>
\end{code}
%endif
\end{exe}

%format Grad = "\F{\nabla}"
\begin{exe}[differentiating |Desc|]
The notion corresponding to |Jac| for descriptions is |Grad|\nudge{"grad"},
computing a `vector' of partial derivatives. Define it
symbolically.\nudge{Symbolic differentiation is the first example
of a pattern matching program in my father's thesis (1970).}
\begin{spec}
Grad : {I : Set} -> Desc I -> I -> Desc I
Grad D h = ?
\end{spec}
%if False
\begin{code}
Grad : {I : Set} -> Desc I -> I -> Desc I
Grad (var i) h = kD (i == h)
Grad (sg A D) h = sg A \ a -> Grad (D a) h
Grad (pi A D) h = sg A \ a -> Grad (D a) h *D pi (A - a) \ { (a' , _) -> D a' }
Grad (D *D E) h = sg Two ((Grad D h *D E) <?> (D *D Grad E h))
Grad (kD A) h = kD Zero
\end{code}
%endif
Hence construct suitable zippering equipment for |Data|.
\end{exe}

It is amusing to note that the mathematical notion of \emph{divergence},
|Grad . D|, corresponds exactly to the choice of decompositions of a
|D|-structure into any element-in-context:
\[
  |sg I \ i -> Grad D i *D var i|
\]
I have not yet found a meaning for \emph{curl}, |Grad * D|, nor am I expecting
Maxwell's equations to pop up anytime soon. But I live in hope for light.


\section{Apocrypha}

\subsection{Roman Containers}

A Roman container is given as follows
%format Roman = "\D{Roman}"
%format Roman.S = "\F{Roman.S}"
%format Roman.P = "\F{Roman.P}"
%format Roman.q = "\F{Roman.q}"
%format Roman.r = "\F{Roman.r}"
%format Plain = "\F{Plain}"
%format SPqr = "\C{SPqr}"
%format !>R = !> "_{\!\F{R}}"
%format <!_!>R = <! _ !>R
%format Roman.Plain = Roman "\!" . "\!" Plain
%format Roman.<!_!>R = Roman "\!" . "\!" <!_!>R
%format S = "\F{S}"
%format P = "\F{P}"
%format q = "\F{q}"
%format r = "\F{r}"
\begin{code}
record Roman (I J : Set) : Set1 where
  constructor SPqr
  field
    S  : Set
    P  : S -> Set
    q  : S -> J
    r  : (s : S) -> P s -> I
  Plain : Con
  Plain = S <1 P
  <!_!>R : (I -> Set) -> (J -> Set)
  <!_!>R X j = Sg (Sg S \ s -> q s == j) (vv \ s _ -> (p : P s) -> X (r s p))
Plain   = Roman.Plain
<!_!>R  = Roman.<!_!>R
\end{code}
%format S = "\V{S}"
%format P = "\V{P}"
%format q = "\V{q}"
%format r = "\V{r}"
It's just a plain container, decorated by functions which attach input
indices to positions and an output index to the shape. We can turn |Roman|
containers into indexed containers whose meanings match on the nose.
%format FromRoman = "\F{FromRoman}"
%format onTheNose = "\F{onTheNose}"
\begin{code}
FromRoman : forall {I J} -> Roman I J -> I i> J
FromRoman (SPqr S P q r)
  =   (\ j -> Sg S \ s -> q s == j)
  <i  (\ j -> P o fst)
  $   (\ f -> r o fst)

onTheNose : forall {I J}(C : Roman I J) -> <! C !>R == <! FromRoman C !>i
onTheNose C = refl
\end{code}

Sadly, the other direction is a little more involved.
%format ToRoman = "\F{ToRoman}"
%format toRoman = "\F{toRoman}"
%format fromRoman = "\F{fromRoman}"
%format toAndFromRoman = "\F{toAndFromRoman}"
\begin{exe}[|ToRoman|]
Show how to construct the |Roman| container isomorphic to a given
indexed container and exhibit the isomorphism.
\begin{spec}
ToRoman : forall {I J} -> I i> J -> Roman I J
ToRoman {I}{J} (S <i P $ r) = ?

toRoman    :  forall {I J}(C : I i> J) ->
              forall {X j} -> <! C !>i X j -> <! ToRoman C !>R X j
toRoman C xs = ?

fromRoman  :  forall {I J}(C : I i> J) ->
              forall {X j} -> <! ToRoman C !>R X j -> <! C !>i X j
fromRoman C xs = ?

toAndFromRoman :
  forall {I J}(C : I i> J){X j}
  ->  (forall xs ->
         toRoman C {X}{j} (fromRoman C {X}{j} xs) == xs)
  *   (forall xs -> fromRoman C {X}{j} (toRoman C {X}{j} xs) == xs)
toAndFromRoman C = ?
\end{spec}
%if False
\begin{code}
ToRoman : forall {I J} -> I i> J -> Roman I J
ToRoman {I}{J} (S <i P $ r) = SPqr (Sg J S) (vv P) fst (vv r)

toRoman    :  forall {I J}(C : I i> J) ->
              forall {X j} -> <! C !>i X j -> <! ToRoman C !>R X j
toRoman C (s , k) = ((_ , s) , refl) , k

fromRoman  :  forall {I J}(C : I i> J) ->
              forall {X j} -> <! ToRoman C !>R X j -> <! C !>i X j
fromRoman C (((j , s) , refl) , k) = s , k

toAndFromRoman :
  forall {I J}(C : I i> J){X j}
  ->  (forall xs -> toRoman C {X}{j} (fromRoman C {X}{j} xs) == xs)
  *   (forall xs -> fromRoman C {X}{j} (toRoman C {X}{j} xs) == xs)
toAndFromRoman C = (\ { (((._ , _) , refl) , _) -> refl }) , \ _ -> refl
\end{code}
%endif
\end{exe}

The general purpose tree type for |Roman| containers looks a lot like
the inductive families you find in Agda or the GADTs of Haskell.
%format RomanData = "\D{RomanData}"
\begin{code}
data RomanData {I}(C : Roman I I) : I -> Set where
  _,_ :  (s : Roman.S C) ->
         ((p : Roman.P C s) -> RomanData C (Roman.r C s p)) ->
         RomanData C (Roman.q C s)
\end{code}
I could have just taken the fixpoint of the interpretation, but I
wanted to emphasize that the role of |Roman.q| is to specialize the
return type of the constructor, creating the constraint which shows
up as an explicit equation in the interpretation. The reason Roman
containers are so called is that they invoke equality and its
mysterious capacity for transubstantiation.

The |RomanData| type looks a lot like a |W|-type, albeit festooned with
equations. Let us show that it is exactly that.
\begin{exe}[|Roman| containers are |W|-types]
%format ideology = "\F{ideology}"
%format phenomenology = "\F{phenomenology}"
%format RomanW = "\F{RomanW}"
%format fromRomanW = "\F{fromRomanW}"
%format toRomanW = "\F{toRomanW}"
Construct a function which takes plain |W|-type data for a |Roman| container
and marks up each node with the index \emph{required} of it, using
|Roman.r|.
\begin{spec}
ideology :  forall {I}(C : Roman I I) ->
            I -> W (Plain C) -> W (Plain C *c Kc I)
ideology C i t = ?
\end{spec}
%if False
\begin{code}
ideology :  forall {I}(C : Roman I I) ->
            I -> W (Plain C) -> W (Plain C *c Kc I)
ideology C i <$ s , k $>
  = <$ (s , i) , (vv (\ p -> ideology C (Roman.r C s p) (k p)) <?> \ ()) $>
\end{code}
%endif
Construct a function which takes plain |W|-type data for a |Roman| container
and marks up each node with the index \emph{delivered} by it, using
|Roman.q|.
\begin{spec}
phenomenology :  forall {I}(C : Roman I I) ->
                 W (Plain C) -> W (Plain C *c Kc I)
phenomenology C t = ?
\end{spec}
%if False
\begin{code}
phenomenology :  forall {I}(C : Roman I I) ->
                 W (Plain C) -> W (Plain C *c Kc I)
phenomenology C <$ s , k $>
  = <$ (s , Roman.q C s) , (vv (\ p -> phenomenology C (k p)) <?> \ ()) $>
\end{code}
%endif
Take the |W|-type interpretation of a |Roman| container to be
the plain data for which the required indices are delivered.
\begin{code}
RomanW : forall {I} -> Roman I I -> I -> Set
RomanW C i = Sg (W (Plain C)) \ t -> phenomenology C t == ideology C i t
\end{code}
Now, check that you can extract |RomanData| from |RomanW|.
\begin{spec}
fromRomanW : forall {I}(C : Roman I I){i} -> RomanW C i -> RomanData C i
fromRomanW C (t , good) = ?
\end{spec}
%if False
\begin{code}
ik :  forall {I}(C : Roman I I){s i i' k k'} ->
      _==_ {X = W (Plain C *c Kc I)} <$ (s , i) , k $> <$ (s , i') , k' $> ->
      (i == i') * (k == k')
ik C refl = refl , refl

fromRWH : forall {I}(C : Roman I I){i}
  (t : W (Plain C)) -> phenomenology C t == ideology C i t -> RomanData C i
fromRWH C {i} <$ s , k $>  g
  rewrite (i << fst (ik C g) !!= Roman.q C s <QED>)
  = s , \ p -> fromRWH C (k p) (cong (\ f -> f (tt , p)) (snd (ik C g)))

fromRomanW : forall {I}(C : Roman I I){i} -> RomanW C i -> RomanData C i
fromRomanW C = vv fromRWH C
\end{code}
%endif

To go the other way, it is easy to construct the plain tree, but to prove
the constraint, you will need to establish equality of functions. Using
%format extensionality = "\F{\orange{extensionality}}"
\begin{code}
postulate
  extensionality :  forall {S : Set}{T : S -> Set}(f g : (s : S) -> T s) ->
                    ((s : S) -> f s == g s) -> f == g
\end{code}
construct
\begin{spec}
toRomanW : forall {I}(C : Roman I I){i} -> RomanData C i -> RomanW C i
toRomanW C t = ?
\end{spec}
\end{exe}


\subsection{Reflexive-Transitive closure}

This does not really belong here, but it is quite fun, and something to
do with indexed somethings. Consider the reflexive transitive closure
of a relation, also known as the `paths in a graph'.

%format ** = "\D{{}^{\ast\!\ast}}"
%format _** = _ **
\begin{code}
data _** {I : Set}(R : I * I -> Set) : I * I -> Set where
  <>   : {i : I}      -> (R **) (i , i)
  _,_  : {i j k : I}  -> R (i , j) -> (R **) (j , k) -> (R **) (i , k)
infix 1 _**
\end{code}

You can construct the natural numbers as an instance.
%format NAT = "\F{NAT}"
%format Loop = "\F{Loop}"
\begin{code}
NAT : Set
NAT = (Loop **) _ where Loop : One * One -> Set ; Loop _ = One
\end{code}

\begin{exe}[further constructions with |**|]
Using no recursive types other than |**|, construct the following
\begin{itemize}
 \item ordinary lists
 \item the $\ge$ relation
 \item lists of numbers in decreasing order
 \item vectors
 \item finite sets
 \item a set of size $n!$ for a given $n$
 \item `everywhere' and `somewhere' for edges in paths
\end{itemize}
\end{exe}

\begin{exe}[monadic operations]
Implement
%format one** = "\F{one}\!" **
%format join** = "\F{join}\!" **
\begin{spec}
one** : forall {I}{R : I * I -> Set} -> R -:> (R **)
one** r = ?

join** : forall {I}{R : I * I -> Set} -> ((R **) **) -:> (R **)
join** rss = ?
\end{spec}
such that the monad laws hold.
\end{exe}


%format Pow = "\F{Pow}"
%format Fam = "\F{Fam}"
\subsection{|Pow| and |Fam|}

We have two ways to formulate a notion of `subset' in type theory. We can
define a subset of |X| as a predicate in
\[
  |X -> Set|
\]
giving a proof-relevant notion of evidence that a given |X : X| belongs,
or we can pick out some elements of |X| as the image of a function
\[
  |Sg Set \ I -> I -> X|
\]
so we have a family of |X|s indexed by some set.

Are these notions the same? That turns out to be a subtle question.
A lot turns on the \emph{size} of |X|, so we had best be formal about
it. In general, |X| is \emph{large}.
\begin{code}
Pow : Set1 -> Set1
Pow X = X -> Set

Fam : Set1 -> Set1
Fam X = Sg Set \ I -> I -> X
\end{code}

\begin{exe}[small |Pow| and |Fam|]
Show that, given a suitable notion of propositional equality,
|Pow o Up| and |Fam o Up| capture essentially the same notion of subset.
%format p2f = "\F{p2f}"
%format f2p = "\F{f2p}"
\begin{spec}
p2f : (Pow o Up) -:> (Fam o Up)
p2f X P = ?

f2p : (Fam o Up) -:> (Pow o Up)
f2p X F = ?
\end{spec}
%if False
\begin{code}
p2f : (Pow o Up) -:> (Fam o Up)
p2f X P = Sg X (P o up) , (up o fst)

f2p : (Fam o Up) -:> (Pow o Up)
f2p X (I , f) (up x) = Sg I \ i -> down (f i) == x
\end{code}
%endif
\end{exe}

\begin{exe}[functoriality of |Pow| and |Fam|]
Equip |Pow| with a contravariant functorial action and |Fam| with a covariant
functorial action.
%format $P = "\F{\ensuremath{\scriptstyle{\$}_{P}}}"
%format $F = "\F{\ensuremath{\scriptstyle{\$}_{F}}}"
%format _$P_ = "\us{" $P "}"
%format _$F_ = "\us{" $F "}"
\begin{spec}
_$P_ : forall {I J} -> (J -> I) -> Pow I -> Pow J
f $P P = ?

_$F_ : forall {I J} -> (I -> J) -> Fam I -> Fam J
f $F F = ?
\end{spec}
%if False
\begin{code}
_$P_ : forall {I J} -> (J -> I) -> Pow I -> Pow J
f $P P = P o f

_$F_ : forall {I J} -> (I -> J) -> Fam I -> Fam J
f $F (X , i) = X , (f o i)
\end{code}
%endif
\end{exe}


|Fam Set| is Martin-L\"of's notion of a \emph{universe}, naming a bunch of sets
by the elements of some indexing set. Meanwhile, the `representation type'
method of describing types concretely in Haskell is just using |Pow Set| in
place of |Fam Set|. It is good to get used to recognizing when concepts are
related just by exchanging |Fam| and |Pow|.

%format ROMAN = "\F{ROMAN}"
%format HANCOCK = "\F{HANCOCK}"
%format NOTTINGHAM = "\F{NOTTINGHAM}"
%format HANCOCK' = "\F{HANCOCK}"
%format NOTTINGHAM' = "\F{NOTTINGHAM}"
Modulo currying and $\lambda$-lifting of parameters, the distinction between
|Roman I J| and our Hancock-style |I i> J|
is just that the former represents indexed shapes by a |Fam| (so |Roman.q|
reads off the shape) whilst the latter uses a |Pow| (so the shapes pertain
to a given index). Both use |Fam|s for positions.
\begin{code}
ROMAN : Set -> Set -> Set1
ROMAN I J = Sg (Fam (Up J)) \ { (S , q) -> S -> Fam (Up I) }

HANCOCK : Set -> Set -> Set1
HANCOCK I J = Sg (Pow (Up J)) \ S -> Sg J (S o up) -> Fam (Up I)
\end{code}
A `Nottingham' indexed container switches the positions to a |Pow|
(see Altenkirch and Morris).
\begin{code}
NOTTINGHAM : Set -> Set -> Set1
NOTTINGHAM I J = Sg (Pow (Up J)) \ S -> Sg J (S o up) -> Pow (Up I)
\end{code}
which amounts to a presentation of shapes and positions as predicates:
%format NSh = "\F{NSh}"
%format NPo = "\F{NPo}"
\begin{spec}
  NSh  : J -> Set
  NPo  : (j : J) -> NSh j -> I -> Set
\end{spec}

For |HANCOCK| and |NOTTINGHAM|, we can abstract the whole construction over |J|,
obtaining:
\begin{code}
HANCOCK' : Set -> Set -> Set1
HANCOCK'     I J = J -> Fam (Fam (Up I))

NOTTINGHAM' : Set -> Set -> Set1
NOTTINGHAM'  I J = J -> Fam (Pow (Up I))
\end{code}

\begin{exe}[|HANCOCK'| to |ROMAN|]
We have, modulo plumbing,
\begin{spec}
  HANCOCK  I J = J -> Fam (Fam (Up I))
  ROMAN    I J = Fam (Up J * Fam (Up I))
\end{spec}
Using |Fam|-|Pow| flips and currying, find a path from one to the other.
However, see below\ldots
\end{exe}

But just when we're getting casual about |Fam|-|Pow| flipping, think about what
happens when the argument is a \emph{large}.

\begin{exe}[fool's errand]
Construct the large version of the |Fam|-|Pow| exchange
\begin{spec}
p2f : Pow -:> Fam
p2f X P = ?

f2p : Fam -:> Pow
f2p X F = ?
\end{spec}
\end{exe}

In our study of datatypes so far, we have been constructing
inductively defined inhabitants of |Pow (Up I)|. Let us now perform our
own flip and consider inductive definition in |Fam I|. What should we
expect? Nothing much different for small |I|, of course. But for a large |I|,
all Heaven breaks loose.