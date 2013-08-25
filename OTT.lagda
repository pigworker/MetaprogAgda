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
\end{exe}

