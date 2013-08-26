module Exe4 where

open import Vec public
open import Normal public
open import STLC public
open import Containers public


record _i>_ (I J : Set) : Set1 where
  constructor _<i_$_
  field
    ShIx : J        -> Set
    PoIx : (j : J)  -> ShIx j -> Set
    riIx : (j : J)(s : ShIx j)(p : PoIx j s) -> I
  <!_!>i : (I -> Set) -> (J -> Set)
  <!_!>i X j = Sg (ShIx j) \ s -> (p : PoIx j s) -> X (riIx j s p)
open _i>_ public

{- {exe}[functoriality]
We have given the interpretation of indexed containers as operations on
indexed families of sets. Equip them with their functorial action for
the following notion of morphism -}

_-:>_ : forall {k l}{I : Set k} -> (I -> Set l) -> (I -> Set l) -> Set (lmax l k)
X -:> Y = forall i -> X i -> Y i

ixMap : forall {I J}{C : I i> J}{X Y} -> (X -:> Y) -> <! C !>i X -:> <! C !>i Y
ixMap f j xs = {!!}

------------------------------------------------------------------------
data ITree {J : Set}(C : J i> J)(j : J) : Set where
  <$_$> : <! C !>i (ITree C) j -> ITree C j

{- {exe}[simply typed $\lambda$-calculus]
Define the simply typed $\lambda$-terms as Petersson-Synek trees. -}

STLC : (Cx Ty * Ty) i> (Cx Ty * Ty)
STLC = {!!}

{- Implement the constructors. -}

---------------------------------------------------------------

{- {exe}[identity and composition]
Construct -}

IdIx : forall {I} -> I i> I
IdIx = {!!}

{- such that
\[ |<! IdIx !>i X i| \cong |X i|
\]
Similarly, construct the composition -}

CoIx : forall {I J K} -> J i> K -> I i> J -> I i> K
CoIx C C' = {!!}

{- such that
\[ |<! CoIx C C' !>i X k| \cong |<! C !>i (<! C' !>i X) k|
\]
-}

data Desc {l}(I : Set l) : Set (lsuc l) where
  var    : I -> Desc I
  sg pi  : (A : Set l)(D : A -> Desc I) -> Desc I
  _*D_   : Desc I -> Desc I -> Desc I
  kD     : Set l -> Desc I
infixr 4 _*D_

<!_!>D : forall {l}{I : Set l} -> Desc I -> (I -> Set l) -> Set l
<! var i !>D    X  = X i
<! sg A D !>D   X  = Sg A \ a -> <! D a !>D X
<! pi A D !>D   X  = (a : A) -> <! D a !>D X
<! D *D E !>D   X  = <! D !>D X * <! E !>D X
<! kD A !>D     X  = A

ixConDesc : forall {I J} -> I i> J -> J -> Desc I
ixConDesc (S <i P $ r) j = sg (S j) \ s -> pi (P j s) \ p -> var (r j s p)

{- {exe}[from |J -> Desc I| to |I i> J|]
Construct functions -}

DSh : {I : Set} -> Desc I -> Set
DSh D = {!!}
DPo : forall {I}(D : Desc I) -> DSh D -> Set
DPo D s = {!!}
Dri : forall {I}(D : Desc I)(s : DSh D) -> DPo D s -> I
Dri D s p = {!!}

{- in order to compute the indexed container form of a family of descriptions.
-}

descIxCon : forall {I J} -> (J -> Desc I) -> I i> J
descIxCon F = (DSh o F) <i (DPo o F) $ (Dri o F)

{-Exhibit the isomorphism
\[
  |<! descIxCon F !>i X j| \cong |<! F j !>D X|
\]
-}


---------------------------------------------------------------

vecD : Set -> Nat -> Desc Nat
vecD X n =
  sg Two    (     kD (n == zero)
            <?>   sg Nat \ k -> kD X *D var k *D kD (n == suc k)
            )

vecD' : Set -> Nat -> Desc Nat
vecD' X zero     = kD One
vecD' X (suc n)  = kD X *D var n

data Data {l}{J : Set l}(F : J -> Desc J)(j : J) : Set l where
  <$_$> : <! F j !>D (Data F) -> Data F j

vnil0 : forall {X} -> Data (vecD' X) zero
vnil0 = <$ <> $>

vcons0 : forall {X n} -> X -> Data (vecD' X) n -> Data (vecD' X) (suc n)
vcons0 x xs = <$ x , xs $>

{- {exe}[something like `levitation']
Construct a family of descriptions which describes a type like |Desc|.
As Agda is not natively cumulative, you will need to shunt types up
through the |Set l| hierarchy by hand, with this gadget: -}

record Up {l}(X : Set l) : Set (lsuc l) where
  constructor up
  field
    down : X
open Up public

{- Now implement -}

DescD : forall {l}(I : Set l) -> One{lsuc l} -> Desc (One{lsuc l})
DescD {l} I _ = {!!}

{- Check that you can map your described descriptions back to descriptions. -}

desc : forall {l}{I : Set l} -> Data (DescD I) <> -> Desc I
desc D = {!!}


---------------------------------------------------------------
Everywhere : forall {I J}(C : I i> J)(X : I -> Set) -> Sg I X i> Sg J (<! C !>i X)
Everywhere (S <i P $ r) X
  =   (\ _ -> One)
  <i  (\ { (j , s , k) _ -> P j s })
  $   (\ { (j , s , k) _ p -> r j s p , k p })

allTrivial : forall {I J}(C : I i> J)(X : I -> Set) jc ->
             <! Everywhere C X !>i (\ _ -> One) jc
allTrivial C X _ = <> , \ p -> <>

{- {exe}[Somewhere]
Construct the transformer which takes |C| to the container for witnesses
that a property holds for some element of a |C|-structure -}

Somewhere : forall {I J}(C : I i> J)(X : I -> Set) -> Sg I X i> Sg J (<! C !>i X)
Somewhere (S <i P $ r) X
  =   {!!}
  <i  {!!}
  $   {!!}

{-Check that the impossible predicate cannot hold somewhere. -}

noMagic : forall {I J}(C : I i> J)(X : I -> Set) jc ->
             <! Somewhere C X !>i (\ _ -> Zero) jc -> Zero
noMagic C X _ (p , m) = {!!}

{- {exe}[|lookup|]
Implement generalized environment |lookup|. -}

lookup :  forall {I J}(C : I i> J)(X : I -> Set) jc {Q R} ->
          <! Everywhere C X !>i Q jc -> <! Somewhere C X !>i R jc ->
          <! Somewhere C X !>i (\ ix -> Q ix * R ix) jc
lookup C X jc qs r = {!!}


{- {exe}[induction as a fold]
Petersson-Synek trees come with a `fold' operator, making |ITree C|
(weakly) initial for |<! C !>i|. We can compute any |P| from a |ITree C|,
given a |C|-algebra for |P|. -}

treeFold :  forall {I}(C : I i> I)(P : I -> Set) ->
            (<! C !>i P -:> P) ->
            (ITree C -:> P)
treeFold C P m i <$ s , k $> = m i (s , \ p -> treeFold C P m _ (k p))

{-However, |treeFold| does not give us \emph{dependent} induction on |ITree C|.
If al you have is a hammer, everything looks like a nail. If we want to
compute why some |P : Sg I (ITree C) -> Set| always holds, we'll need an
indexed container storing |P|s in positions corresponding to the children
of a given tree. The |Everywhere C| construct does most of the work,
but you need a little adaptor to unwrap the |C| container inside the |ITree C|. -}

Children : forall {I}(C : I i> I) -> Sg I (ITree C) i> Sg I (ITree C)
Children C = CoIx {!!} (Everywhere C (ITree C))

{- Now, you can extract a general induction principle for |ITree C| from
|treeFold (Children C)|, but you will need a little construction. Finish the
job. -}

treeFoldInd :  forall {I}(C : I i> I) P ->
               (<! Children C !>i P -:> P) ->
               forall it -> P it
treeFoldInd C P m (i , t) = treeFold (Children C) P m (i , t) {!!}

{- Of course, you need to do what is effectively an inductive proof to
fill in the hole. Induction really does amount to more than weak
initiality. But one last induction will serve for all.  -}


{- {exe}[|Everywhere| and |Somewhere| for |Desc|] Define suitable
description transformers, capturing what it means for a predicate to
hold in every or some element position within a given described
structure. -}

EverywhereD SomewhereD :  {I : Set}(D : Desc I)(X : I -> Set) ->
                          <! D !>D X -> Desc (Sg I X)
EverywhereD  D X xs = {!!}
SomewhereD   D X xs = {!!}

{- Now construct -}

dataInd : forall {I : Set}(F : I -> Desc I)(P : Sg I (Data F) -> Set) ->
          (  (i : I)(ds : <! F i !>D (Data F)) ->
             <! EverywhereD (F i) (Data F) ds !>D P -> P (i , <$ ds $>)) ->
          forall i d -> P (i , d)
dataInd F P m i d = {!!}

---------------------------------------------------------------
data Desc' (I : Set) : Set1 where
  var    : I -> Desc' I
  sg pi  : (A : Set)(D : A -> Desc' I) -> Desc' I
  _*D_   : Desc' I -> Desc' I -> Desc' I
  kD     : Set -> Desc' I
  mu     : (J : Set) -> (J -> Desc' (I + J)) -> J -> Desc' I

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

{- {exe}[induction]
State and prove the induction principle for |Desc'|. (This is not an
easy exercise.)
-}


---------------------------------------------------------------

Jac : forall {I J} -> I i> J -> I i> (J * I)
Jac (S <i P $ r)
  =   (\ { (j , i) -> Sg (S j) \ s -> r j s ^-1 i })
  <i  (\ { (j , .(r j s p)) (s , from p) -> P j s - p })
  $   (\ { (j , .(r j s p)) (s , from p) (p' , _) -> r j s p' })

{- {exe}[plugging]
Check that a decidable equality for positions is enough to define the
`plugging in' function. -}

plugIx :  forall {I J}(C : I i> J) ->
        ((j : J)(s : ShIx C j)(p p' : PoIx C j s) -> Dec (p == p')) ->
        forall {i j X} -> <! Jac C !>i X (j , i) -> X i -> <! C !>i X j
plugIx C eq? jx x = {!!}

{- {exe}[the Zipper]
For a given |C : I i> I|, construct the indexed container
|Zipper C : (I * I) i> (I * I)| such that |ITree (Zipper C) (ir , ih)|
represents a one |ih|-hole context in a |ITree C ir|, represented
as a sequence of hole-to-root layers. -}

Zipper : forall {I} -> I i> I -> (I * I) i> (I * I)
Zipper C = {!!}

{- Check that you can zipper all the way out to the root. -}

zipOut :  forall {I}(C : I i> I){ir ih} ->
          ((i : I)(s : ShIx C i)(p p' : PoIx C i s) -> Dec (p == p')) ->
          ITree (Zipper C) (ir , ih) -> ITree C ih -> ITree C ir
zipOut C eq? cz t = {!!}

{- {exe}[differentiating |Desc|]
The notion corresponding to |Jac| for descriptions is |Grad|\nudge{"grad"},
computing a `vector' of partial derivatives. Define it
symbolically.\nudge{Symbolic differentiation is the first example
of a pattern matching program in my father's thesis (1970).} -}

Grad : {I : Set} -> Desc I -> I -> Desc I
Grad D h = {!!}

{- Hence construct suitable zippering equipment for |Data|.
-}



---------------------------------------------------------------

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

FromRoman : forall {I J} -> Roman I J -> I i> J
FromRoman (SPqr S P q r)
  =   (\ j -> Sg S \ s -> q s == j)
  <i  (\ j -> P o fst)
  $   (\ f -> r o fst)

onTheNose : forall {I J}(C : Roman I J) -> <! C !>R == <! FromRoman C !>i
onTheNose C = refl

{- {exe}[|ToRoman|]
Show how to construct the |Roman| container isomorphic to a given
indexed container and exhibit the isomorphism. -}

ToRoman : forall {I J} -> I i> J -> Roman I J
ToRoman {I}{J} (S <i P $ r) = {!!}

toRoman    :  forall {I J}(C : I i> J) ->
              forall {X j} -> <! C !>i X j -> <! ToRoman C !>R X j
toRoman C xs = {!!}

fromRoman  :  forall {I J}(C : I i> J) ->
              forall {X j} -> <! ToRoman C !>R X j -> <! C !>i X j
fromRoman C xs = {!!}

toAndFromRoman :
  forall {I J}(C : I i> J){X j}
  ->  (forall xs ->
         toRoman C {X}{j} (fromRoman C {X}{j} xs) == xs)
  *   (forall xs -> fromRoman C {X}{j} (toRoman C {X}{j} xs) == xs)
toAndFromRoman C = {!!}

data RomanData {I}(C : Roman I I) : I -> Set where
  _,_ :  (s : Roman.S C) ->
         ((p : Roman.P C s) -> RomanData C (Roman.r C s p)) ->
         RomanData C (Roman.q C s)

{- {exe}[|Roman| containers are |W|-types]
Construct a function which takes plain |W|-type data for a |Roman| container
and marks up each node with the index \emph{required} of it, using
|Roman.r|. -}

ideology :  forall {I}(C : Roman I I) ->
            I -> W (Plain C) -> W (Plain C *c Kc I)
ideology C i t = {!!}

{-Construct a function which takes plain |W|-type data for a |Roman| container
and marks up each node with the index \emph{delivered} by it, using
|Roman.q|. -}

phenomenology :  forall {I}(C : Roman I I) ->
                 W (Plain C) -> W (Plain C *c Kc I)
phenomenology C t = {!!}

{- Take the |W|-type interpretation of a |Roman| container to be
the plain data for which the required indices are delivered. -}

RomanW : forall {I} -> Roman I I -> I -> Set
RomanW C i = Sg (W (Plain C)) \ t -> phenomenology C t == ideology C i t

{- Now, check that you can extract |RomanData| from |RomanW|. -}

fromRomanW : forall {I}(C : Roman I I){i} -> RomanW C i -> RomanData C i
fromRomanW C (t , good) = {!!}

{- To go the other way, it is easy to construct the plain tree, but to prove
the constraint, you will need to establish equality of functions. Using -}

postulate
  extensionality :  forall {S : Set}{T : S -> Set}(f g : (s : S) -> T s) ->
                    ((s : S) -> f s == g s) -> f == g

{- construct -}

toRomanW : forall {I}(C : Roman I I){i} -> RomanData C i -> RomanW C i
toRomanW C t = {!!}


--------------------------------------------------------------------
data _** {I : Set}(R : I * I -> Set) : I * I -> Set where
  <>   : {i : I}      -> (R **) (i , i)
  _,_  : {i j k : I}  -> R (i , j) -> (R **) (j , k) -> (R **) (i , k)
infix 1 _**

NAT : Set
NAT = (Loop **) _ where Loop : One * One -> Set ; Loop _ = One

{- {exe}[further constructions with |**|]
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
-}

{- {exe}[monadic operations]
Implement -}

one** : forall {I}{R : I * I -> Set} -> R -:> (R **)
one** r = {!!}

join** : forall {I}{R : I * I -> Set} -> ((R **) **) -:> (R **)
join** rss = {!!}

{- such that the monad laws hold.
-}


------------------------------------------------------------------------
Pow : Set1 -> Set1
Pow X = X -> Set

Fam : Set1 -> Set1
Fam X = Sg Set \ I -> I -> X

{- {exe}[small |Pow| and |Fam|]
Show that, given a suitable notion of propositional equality,
|Pow o Up| and |Fam o Up| capture essentially the same notion of subset. -}

p2f : (Pow o Up) -:> (Fam o Up)
p2f X P = {!!}

f2p : (Fam o Up) -:> (Pow o Up)
f2p X F = {!!}

{- {exe}[functoriality of |Pow| and |Fam|]
Equip |Pow| with a contravariant functorial action and |Fam| with a covariant
functorial action. -}

_$P_ : forall {I J} -> (J -> I) -> Pow I -> Pow J
f $P P = {!!}

_$F_ : forall {I J} -> (I -> J) -> Fam I -> Fam J
f $F F = {!!}

{- {exe}[fool's errand]
Construct the large version of the |Fam|-|Pow| exchange -}

P2F : Pow -:> Fam
P2F X P = {!!}

F2P : Fam -:> Pow
F2P X F = {!!}
