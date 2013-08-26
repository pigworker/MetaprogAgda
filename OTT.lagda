%if False
\begin{code}
module OTT where

open import IR public

\end{code}
%endif

We cannot have an equality which is both extensional and decidable.
We choose to keep \emph{judgmental} equality decidable, hence it is
inevitably disappointing, but we introduce a \emph{propositional} equality,
allowing us to give evidence for equations on open terms which the computer
is too stupid to see. Correspondingly, we need a |subst|itution mechanism
to transport values from |P s| to |P t| whenever |s == t|. The way |subst|
has worked thus far is to wait at least until |s jeq t| holds judgmentally,
so that |p : P s| implies |p : P t|, allowing |p| to be transmitted as it
stands. (Waiting for the proof of |s == t| to become |refl| means waiting
at least until |s jeq t|.)

The trouble with this way to compute |subst| is that we have no way to
explain its computation if there are provably equal closed terms which
are not judgmentally equal. We can add axioms for extensionality and
retain consistency, even extracting working programs which compile
|subst| to |id| and never compute under a binder. However, such axioms
impede open computation. If we want a propositional equality to make
up for our disappointment with judgmental equality, and a |subst|
which works, we must figure out how to transport values between
provably but not judgmentally equal types.

The situation is particularly galling when you think how a type like
|P f| could possibly depend on a function |f|. If all |P| ever does with
|f| is to \emph{apply} it, then of course |P| respects extensional
equality. If types can only depend on values by observing them, then
there should be a systematic way to show that transportability between
types respects equality-up-to-observation.

But does the hypothesis of the previous sentence hold? Consider

%format Favourite = "\D{Favourite}"
%format favourite = "\C{favourite}"
\begin{code}
data Favourite : (Nat -> Nat) -> Set where
  favourite : Favourite (\ x -> zero +Nat x)
\end{code}

We may certainly prove that |\ x -> zero +Nat x| and |\ x -> x +Nat
zero| agree on all inputs. But is there a canonical inhabitant of
|Favourite (\ x -> x +Nat zero)|? If so, it can only be |favourite|,
for that is the only constructor, but |favourite| does not have that
type because the two functions are not judgmentally equal. The trouble
is that by using the power to `focus' a constructor's return type on
specific indices, |Favourite| is an \emph{intensional} predicate,
holding only for a specific implementation of a particular
function. We cannot expect a type theory with intensional predicates
to admit a sensible notion of extensional equality. Let us do away
with them! If, instead, we reformulate |Favourite| in the Henry Ford
tradition,
%format Favourite' = "\D{Favourite}"
%format favourite' = "\C{favourite}"
\begin{code}
data Favourite' (f : Nat -> Nat) : Set where
  favourite' : (\ x -> zero +Nat x) == f -> Favourite' f
\end{code}
then our definition of |Favourite'| becomes just as intensional as
our equality. If, somehow, |==| were to admit extensionality, we could
certainly show that |Favourite'| respects |==|.
If |q' : f == g|, then we can transport
|favourite' q| from |Favourite' f | to |Favourite' g|,
returning, not the original data but
\[
  |favourite' ((\ x -> zero +Nat x) =!! q >> f =!! q' >> g <QED>)|
\]
with a modified proof.


\section{Observational Equality for Types and Values in |TU|}

We have got as far as figuring out that a propositional equality which is
more generous than the judgmental equality will require a computation
mechanism which might modify the data it transports between provably
equal types, but should not change the results of observing the data.
To say what that mechanism is, we shall need to inspect the types involved,
so let us work with the types of the |TU| universe and develop what
equality means for its types and values by metaprogramming.

%format <-> = "\F{\leftrightarrow}"
%format _<->_ = "\us{" <-> "}"
%format Eq = "\F{Eq}"
%format EQ = "\F{EQ}"

We shall need to consider when types are equal: I write |X <-> Y| to
indicate that |X| and |Y| are types whose data are interchangeable.
I propose the bold choice to consider only those kinds of interchangeability
which can be implemented by the identity function at closed-run time.
Enthusiasts for Voevodsky's univalence axiom are entitled to be disappointed
by this choice, but perhaps a simple computational interpretation will prove
modest consolation.

Inasmuch as types depend on values, we shall also need to say when
values are equal. There is no reason to presume that we shall be
interested only to consider the equality of values in types which are
judgmentally equal, for we know that judgmental equality is too weak
to recognize the sameness of some types whose values are
interchangeable. Correspondingly, let us weaken our requirement for
the formation of value equalities and have a \emph{heterogeneous}
equality, |Eq X x Y y|. We have some options for how to do that:
\begin{itemize}
\item We could make add the requirement |X <-> Y| to the \emph{formation}
  rule for |Eq|.
\item We could allow the formation of any |Eq X x Y y|, but ensure that it
  holds only if |X <-> Y|.
\item We could allow the formation of any |Eq X x Y y|, but ensure that
  proofs of such equations are useless information unless |X <-> Y|.
\end{itemize}
All three are sustainable, but I find the third is the least bureaucratic.
The proposition |Eq X x Y y| means `if |X| is |Y|, then |x| is |y|' and
should thus be considered `true but dull' if |X| is clearly not |Y|.

We need to define them by recursion on types. It's convenient to build them
together, then project out the type and value components. Note that we work
internally to the universe: we already have the types we need to descrbe the
evidence for equality of types and values in this sense.
\begin{code}
mutual

  EQ : (X Y : TU) -> TU * (<! X !>TU -> <! Y !>TU -> TU)

  _<->_ : TU -> TU -> TU
  X <-> Y = fst (EQ X Y)

  Eq : (X : TU)(x : <! X !>TU) -> (Y : TU)(y : <! Y !>TU) -> TU
  Eq X x Y y = snd (EQ X Y) x y
\end{code}

We should expect, ultimately, to construct a coercion mechanism
which realises equality as transportation.
%format coe = "\F{coe}"
%format coh = "\F{coh}"
\begin{spec}
coe : (X Y : TU) -> <! X <-> Y !>TU -> <! X !>TU -> <! Y !>TU
\end{spec}
Moreover, we should ensure that coercion does not change the observable
properties of values and is thus \emph{coherent} in the sense that
\begin{spec}
coh : (X Y : TU)(Q : <! X <-> Y !>TU)(x : <! X !>TU) -> <! Eq X x Y (coe X Y Q x) !>TU
\end{spec}

Given what we want to use equality \emph{for}, we should be able to figure
out what it needs to \emph{be}, on  a case-by-case basis.

Base types equal only themselves, and we need no help to transport a
value from a type to itself. For |Zero'| and |One'|, all values are
equal as there is at most one value anyway. For |Two'|, we must
actually test the values.
\begin{code}
  EQ  Zero'  Zero'  = One' , \ _ _ -> One'
  EQ  One'   One'   = One' , \ _ _ -> One'
  EQ  Two'   Two'   = One' , \
    {  tt  tt  -> One'
    ;  ff  ff  -> One'
    ;  _   _   -> Zero'
    }
\end{code}

|Sg'|-types are interchangable if their components are, but how are we
to express the interchangeability of the dependent second components?
It is enough to consider the types of the second components only when
the values of the first components agree, a situation we can consider
hypothetically by abstracting not over one value, which would need to
have both first component types, but rather over a pair of equal values
drawn from each.
\begin{code}
  EQ (Sg' S T) (Sg' S' T')
    =  (  Sg' (S <-> S') \ _ ->
          Pi' S \ s -> Pi' S' \ s' -> Pi' (Eq S s S' s') \ _ ->
          T s <-> T' s'  )
    ,  \ {  (s , t) (s' , t') ->
            Sg' (Eq S s S' s') \ _ -> Eq (T s) t (T' s') t' }
\end{code}
Equality of pair values is straightforwardly structural. Notice that
if the |Sg'|-types are equal then their first component types are equal,
so it is useful to know that the first component values are equal, which
in turn lets us deduce equality of the second component types.

Equality of functions types is similar, save for the contravariant twist
I have put in the domain type equation. To coerce a function from left to
right, we shall need to coerce its input from right to left.
\begin{code}
  EQ (Pi' S T) (Pi' S' T')
    =  (  Sg' (S' <-> S) \ _ ->
          Pi' S' \ s' -> Pi' S \ s -> Pi' (Eq S' s' S s) \ _ ->
          T s <-> T' s'  )
    ,  \ {  f f' ->
            Pi' S \ s -> Pi' S' \ s' -> Pi' (Eq S s S' s') \ _ ->
            Eq (T s) (f s) (T' s') (f' s') }
\end{code}
Function values are considered equal if they take equal inputs to equal
outputs.

|Tree'| types are, again, compared structurally, with pointwise equality
expressed by abstraction over pairs of equal values.
%format teq = "\F{teq}"
\begin{code}
  EQ (Tree' I F i) (Tree' I' F' i')
    =  (  Sg' (I <-> I') \ _ -> Sg' (Eq I i I' i') \ _ ->
          Pi' I \ i -> Pi' I' \ i' -> Pi' (Eq I i I' i') \ _ ->
          let  (S , K) = F i ; S' , K' = F' i'
          in   Sg' (S <-> S') \ _ ->
               Pi' S \ s -> Pi' S' \ s' -> Pi' (Eq S s S' s') \ _ ->
               let (P , r) = K s ; (P' , r') = K' s' 
               in  Sg' (P' <-> P) \ _ ->
                   Pi' P' \ p' -> Pi' P  \ p -> Pi' (Eq P' p' P p) \ _ ->
                   Eq I (r p) I' (r' p') )
    ,  teq i i' where
       teq : (i : <! I !>TU) -> (i' : <! I' !>TU) ->
             <! Tree' I F i !>TU -> <! Tree' I' F' i' !>TU -> TU
       teq i i' <$ s , k $> <$ s' , k' $>
         =  let  (S , K) = F i  ; (S' , K') = F' i'
                 (P , r) = K s  ; (P' , r') = K' s'
            in   Sg' (Eq S s S' s') \ _ ->
                 Pi' P \ p -> Pi' P' \ p' -> Pi' (Eq P p P' p') \ _ ->
                 teq (r p) (r' p') (k p) (k' p')
\end{code}
|Tree'| value equality is defined by structural recursion. At each node,
we demand equal shapes, then at equal positions, equal subtrees.

Finally, types whose head constructors disagree are considered unequal,
hence their values are vacuously equal.
\begin{code}
  EQ _ _ = Zero' , \ _ _ -> One'
\end{code}

\begin{exe}[define |coe|, postulate |coh|]
Implement |coe|rcion, assuming |coh|erence.
\begin{spec}
coe : (X Y : TU) -> <! X <-> Y !>TU -> <! X !>TU -> <! Y !>TU

postulate
  coh : (X Y : TU)(Q : <! X <-> Y !>TU)(x : <! X !>TU) -> <! Eq X x Y (coe X Y Q x) !>TU

coe X Y Q x = ?
\end{spec}
%if False
\begin{code}
coe : (X Y : TU) -> <! X <-> Y !>TU -> <! X !>TU -> <! Y !>TU

postulate
  coh : (X Y : TU)(Q : <! X <-> Y !>TU)(x : <! X !>TU) -> <! Eq X x Y (coe X Y Q x) !>TU

coe Zero' Zero' <> x = x
coe Zero' One' () x
coe Zero' Two' () x
coe Zero' (Sg' Y T) () x
coe Zero' (Pi' Y T) () x
coe Zero' (Tree' Y F i) () x
coe One' Zero' () x
coe One' One' <> x = x
coe One' Two' () x
coe One' (Sg' Y T) () x
coe One' (Pi' Y T) () x
coe One' (Tree' Y F i) () x
coe Two' Zero' () x
coe Two' One' () x
coe Two' Two' <> x = x
coe Two' (Sg' Y T) () x
coe Two' (Pi' Y T) () x
coe Two' (Tree' Y F i) () x
coe (Sg' X T) Zero' () x
coe (Sg' X T) One' () x
coe (Sg' X T) Two' () x
coe (Sg' S T) (Sg' S' T') (SQ , TQ) (s , t) =
  let  s' = coe S S' SQ s  ; sq = coh S S' SQ s
  in   s' , coe (T s) (T' s') (TQ s s' sq) t
coe (Sg' X T) (Pi' Y T₁) () x
coe (Sg' X T) (Tree' Y F i) () x
coe (Pi' X T) Zero' () x
coe (Pi' X T) One' () x
coe (Pi' X T) Two' () x
coe (Pi' X T) (Sg' Y T₁) () x
coe (Pi' S T) (Pi' S' T') (SQ , TQ) f = \ s' ->
  let  s = coe S' S SQ s' ; sq = coh S' S SQ s'
  in   coe (T s) (T' s') (TQ s' s sq) (f s)
coe (Pi' X T) (Tree' Y F i) () x
coe (Tree' X F i) Zero' () x
coe (Tree' X F i) One' () x
coe (Tree' X F i) Two' () x
coe (Tree' X F i) (Sg' Y T) () x
coe (Tree' X F i) (Pi' Y T) () x
coe (Tree' I F i) (Tree' I' F' i') (IQ , iq , FQ) x = tcoe i i' iq x where
  tcoe : (i : <! I !>TU)(i' : <! I' !>TU)(iq : <! Eq I i I' i' !>TU) ->
         <! Tree' I F i !>TU -> <! Tree' I' F' i' !>TU
  tcoe i i' iq <$ s , k $> = <$ (
    let  (S , K) = F i ; (S' , K') = F' i'
         (SQ , KQ) = FQ i i' iq
         s' = coe S S' SQ s ; sq = coh S S' SQ s
         (P , r) = K s ; (P' , r') = K' s'
         (PQ , rq) = KQ s s' sq
    in   s' , \ p' ->
         let  p = coe P' P PQ p' ; pq = coh P' P PQ p'
         in   tcoe (r p) (r' p') (rq p' p pq) (k p) ) $>
\end{code}
%endif
\end{exe}

If you look at the definition of |EQ| quite carefully, you will notice
that we did not use all of the types in |TU| to express
equations. There is never any choice about how to be equal, so we need
never use |Two'|; meanwhile, we can avoid expressing tree equality as
itself a tree just by using structural recursion. As a result, the
only constructor pattern matching |coe| need ever perform on
\emph{proofs} is on pairs, which is just sugar for the lazy use of
projections. Correspondingly, the only way coercion of canonical
values between canonical types can get stuck is if those types are
conspicuously different. Although we postulated |coh|erence, no
computation which relies on it is strict in equality proofs, so it is
no source of blockage.

The only way a closed |coercion| can get stuck is if we can prove a
false equation. The machinery works provided the theory is consistent,
but we can prove no equations which do not also hold in extensional
type theories which are known to be consistent. In general, we are free
to assert consistent equations. Let us have
%format reflTU = "\F{\orange{refl}_{\F{TU}}}"
\begin{code}
postulate
  reflTU : (X : TU)(x : <! X !>TU) -> <! Eq X x X x !>TU
\end{code}

\begin{exe}[explore failing to prove |reflTU|]
Try proving
\begin{spec}
reflTU : (X : TU)(x : <! X !>TU) -> <! Eq X x X x !>TU
reflTU X x = ?
\end{spec}
Where do you get stuck?
\end{exe}

Homogeneous equations between values are made useful just by asserting
that predicates respect them. We recover the Leibniz property.
%format RespTU = "\F{\orange{Resp}_{\F{TU}}}"
%format substTU = "\F{subst}_{\F{TU}}"
\begin{code}
postulate
  RespTU :  (X : TU)(P : <! X !>TU -> TU)
            (x x' : <! X !>TU) -> <! Eq X x X x' !>TU -> <! P x <-> P x' !>TU

substTU : (X : TU)(P : <! X !>TU -> TU)
          (x x' : <! X !>TU) -> <! Eq X x X x' !>TU -> <! P x !>TU -> <! P x' !>TU
substTU X P x x' q = coe (P x) (P x') (RespTU X P x x' q)
\end{code}

It is clearly desirable to construct a model in which these postulated
constructs are given computational force, not least because such a model
would yield a more direct proof of consistency. However, we have done
enough to gain a propositional equality which is extensional for functions,
equipped with a mechanism for obtaining canonical forms in `data' computation.



\section{A Universe with Propositions}

%format Sort = "\D{Sort}"
%format PU = "\D{Set}"
%format set = "\C{set}"
%format prop = "\C{prop}"
%format IsSet = "\F{IsSet}"
%format !>PU = !> "_{\F{PU}}"
%format <!_!>PU = <! _ !>PU
%format Prf' = "\C{Prf}" redp

We can express the observation that all of our proofs belong to lazy
types by splitting our universe into two |Sort|s, corresponding to
|set|s and |prop|ositions, embedding the latter explicitly into the former
with a new set-former, |Prf'|.
\begin{code}
data Sort : Set where set prop : Sort

IsSet : Sort -> Set
IsSet set   = One
IsSet prop  = Zero

mutual
  data PU (u : Sort) : Set where
    Zero' One' : PU u
    Two'   :  {_ : IsSet u} -> PU u
    Sg'    :  (S : PU u)(T : <! S !>PU -> PU u) -> PU u
    Pi'    :  (S : PU set)(T : <! S !>PU -> PU u) -> PU u
    Tree'  :  {_ : IsSet u}
              (I : PU set)
              (F :  <! I  !>PU  -> Sg (PU set) \ S ->
                    <! S  !>PU  -> Sg (PU set) \ P ->
                    <! P  !>PU  -> <! I !>PU  )
              (i : <! I !>PU) -> PU u
    Prf'   :  {_ : IsSet u} -> PU prop -> PU u

  <!_!>PU : forall {u} -> PU u -> Set
  <! Zero'        !>PU  = Zero
  <! One'         !>PU  = One
  <! Two'         !>PU  = Two
  <! Sg' S T      !>PU  = Sg <! S !>PU \ s -> <! T s !>PU
  <! Pi' S T      !>PU  = (s : <! S !>PU) -> <! T s !>PU
  <! Tree' I F i  !>PU  = ITree
    (   (\ i -> <! fst (F i) !>PU)
    <i  (\ i s -> <! fst (snd (F i) s) !>PU)
    $   (\ i s p -> snd (snd (F i) s) p)
    )   i
  <! Prf' P       !>PU  = <! P !>PU
\end{code}
Note that |Two'| and |Tree'| are excluded from |PU prop| and that sort is always
\emph{preserved} in covariant positions and |set| in contravariant
positions. The interpretation of types is just as before. One could
allow the formation of \emph{inductive predicates}, being |Tree'| structures
with propositional node shapes, but we should then be careful not to
pattern match on proofs when working with data in |set|s. I have chosen to avoid
the risk, allowing only propositions whose eliminators are in any case lazy.

%format /\ = "\F{\wedge}"
%format _/\_ = "\us{" /\ "}"
%format => = "\F{\Rightarrow}"
%format _=>_ = "\us{" => "}"
%format <=> = "\F{\Leftrightarrow}"
%format _<=>_ = "\us{" <=> "}"
%format PEQ = "\F{PEQ}"
%format PEq = "\F{PEq}"

\begin{exe}[observational propositional equality]
Reconstruct the definition of observational equality in this more refined
setting. Take equality of propositions to be mutual implication and
equality of proofs to be trivial: after all, equality for proofs of the
atomic |Zero'| and |One'| propositions are trivial.

\begin{spec}
_/\_ : PU prop -> PU prop -> PU prop
P /\ Q = Sg' P \ _ -> Q

_=>_ : PU prop -> PU prop -> PU prop
P => Q = Pi' (Prf' P) \ _ -> Q

mutual

  PEQ : (X Y : PU set) -> PU prop * (<! X !>PU -> <! Y !>PU -> PU prop)

  _<=>_ : PU set -> PU set -> PU prop
  X <=> Y = fst (PEQ X Y)

  PEq : (X : PU set)(x : <! X !>PU) -> (Y : PU set)(y : <! Y !>PU) -> PU prop
  PEq X x Y y = snd (PEQ X Y) x y

  PEQ  (Prf' P) (Prf' Q) = ((P => Q) /\ (Q => P)) , \ _ _ -> One'
  -- \orange{more code goes here}
  PEQ  _ _ = Zero' , \ _ _ -> One'
\end{spec}
\end{exe}


